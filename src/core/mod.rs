mod argparse;
mod parse;

use std::{
    fs::{self, DirEntry, ReadDir},
    io::{self, Read},
    path::Path,
};

use crate::{
    error::{QueriesError, SqlgenError},
    lang::Codegen,
};

pub use parse::NamedQuery;
pub use parse::SqlType;

use self::parse::Sqlparser;

#[derive(Clone, Copy, Debug)]
pub enum SqlDialect {
    Sqlite,
}

pub type QueriesResult<R> = Result<QueriesEntry<R>, QueriesError>;

#[derive(Debug)]
pub struct Sqlgen<R, Q, C>
where
    R: Read,
    Q: Iterator<Item = QueriesResult<R>>,
    C: Codegen,
{
    pub schema_file: R,
    pub queries: Q,
    pub dialect: SqlDialect,
    pub code_generator: C,
}

impl<R, Q, C> Sqlgen<R, Q, C>
where
    R: Read,
    Q: Iterator<Item = QueriesResult<R>>,
    C: Codegen,
{
    pub fn run(&mut self) -> Result<String, SqlgenError> {
        let parser = Sqlparser::with_dialect(self.dialect);

        let mut schema_sql = String::new();
        self.schema_file.read_to_string(&mut schema_sql)?;
        let schema = parser.parse_schema(schema_sql)?;

        let mut queries: Vec<NamedQuery> = vec![];

        for entry_result in self.queries.by_ref() {
            let mut entry = entry_result?;
            let mut query_sql = String::new();
            entry.source.read_to_string(&mut query_sql)?;

            let query = parser.parse_query(&query_sql, &schema)?;

            let args = argparse::args(&query_sql);

            let raw_query = replace(&query_sql, self.dialect, &args);

            queries.push(query.into_named(entry.name(), &raw_query, args));
        }

        queries.sort_unstable_by(|a,b| a.partial_cmp(b).unwrap());

        self.code_generator
            .codegen(&queries)
            .map_err(|err| err.into())
    }
}

fn replace<S: AsRef<str>>(sql: S, dialect: SqlDialect, args: &[argparse::Arg]) -> String {
    let s = sql.as_ref();

    let mut pos = 0;
    
    let mut out = args.iter().fold(String::new(), |acc, x| {
        let binding = match dialect {
            SqlDialect::Sqlite => "?"
        };

        let next = acc + &s[pos..x.pos()] + binding;

        pos = x.pos() + x.len();

        next
    });

    out.push_str(&s[pos..]);

    out
}

pub struct QueriesEntry<R: Read> {
    name: String,
    source: R,
}

impl<R: Read> QueriesEntry<R> {
    pub fn name(&self) -> &str {
        self.name.as_ref()
    }

    pub fn source(&self) -> &R {
        &self.source
    }
}

#[derive(Debug)]
pub struct Queries {
    read_dir: ReadDir,
}

impl Iterator for Queries {
    type Item = Result<QueriesEntry<fs::File>, QueriesError>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(entry) = self.read_dir.next() {
            if let Some(result) = self.filter_entry(entry).transpose() {
                return Some(result);
            }
        }
        None
    }
}

impl Queries {
    pub fn new<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        fs::read_dir(path).map(|read_dir| Queries { read_dir })
    }

    /// Result contains `Some` if entry is a sql file, otherwise `None`.
    fn filter_entry(
        &self,
        entry_result: io::Result<DirEntry>,
    ) -> Result<Option<QueriesEntry<fs::File>>, QueriesError> {
        let entry = entry_result?;
        let file_type = entry.file_type()?;
        if !file_type.is_file() {
            return Ok(None);
        }

        let path = entry.path();
        let extension = path.extension().and_then(|s| s.to_str());
        if !matches!(extension, Some("sql")) {
            return Ok(None);
        }

        let name = path
            .file_stem()
            .ok_or_else(|| QueriesError::PathError("cannot get filename from path".to_string()))?
            .to_string_lossy()
            .to_string();
        let source = fs::File::open(path)?;

        Ok(Some(QueriesEntry { name, source }))
    }
}
