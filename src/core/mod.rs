mod argparse;
mod parse;

use std::{
    collections::HashMap,
    ffi::OsStr,
    fs::{self, DirEntry, ReadDir},
    io::{self, Read},
    path::Path,
};

use crate::{
    error::{FilesError, SqlgenError},
    lang::Codegen,
};

pub use argparse::ArgType;
pub use parse::NamedQuery;
pub use parse::SqlType;

use self::parse::Sqlparser;

#[derive(Clone, Copy, Debug)]
pub enum SqlDialect {
    Sqlite,
}

pub type QueriesResult<R> = Result<FilesEntry<R>, FilesError>;

#[derive(Debug)]
pub struct Sqlgen<R, Q, C>
where
    R: Read,
    Q: Iterator<Item = QueriesResult<R>>,
    C: Codegen,
{
    pub schema: String,
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

        let schema = parser.parse_schema(&self.schema)?;

        let mut queries: Vec<NamedQuery> = vec![];

        for entry_result in self.queries.by_ref() {
            let mut entry = entry_result?;
            dbg!(&entry.name);
            let mut query_sql = String::new();
            entry.source.read_to_string(&mut query_sql)?;

            let args = argparse::args(&query_sql);

            let typed_args = args
                .iter()
                .filter_map(|a| a.arg_type().map(|t| (a.ident().to_string(), t)))
                .collect::<HashMap<_, _>>();

            for arg in &args {
                if arg.arg_type().is_none() && !typed_args.contains_key(arg.ident()) {
                    return Err(SqlgenError::UntypedArg(arg.ident().to_string()));
                }
                if arg
                    .arg_type()
                    .is_some_and(|t| typed_args.get(arg.ident()) != Some(&t))
                {
                    return Err(SqlgenError::ConflictingArgType(arg.ident().to_string()));
                }
            }

            let raw_query = replace(&query_sql, self.dialect, &args);

            let query = parser.parse_query(&raw_query, &schema)?;

            queries.push(query.into_named(entry.name(), &raw_query, args));
        }

        queries.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());

        self.code_generator
            .codegen(&queries)
            .map_err(|err| err.into())
    }
}

fn replace<S: AsRef<str>>(sql: S, dialect: SqlDialect, args: &[argparse::Arg]) -> String {
    let s = sql.as_ref();

    let mut pos = 0;

    dbg!(args);

    let mut out = args.iter().fold(String::new(), |acc, x| {
        let binding = match dialect {
            SqlDialect::Sqlite => "?",
        };

        let next = acc + &s[pos..x.pos()] + binding;

        pos = x.pos() + x.len();

        next
    });

    out.push_str(&s[pos..]);

    out
}

pub struct FilesEntry<R: Read> {
    name: Box<str>,
    source: R,
}

impl<R: Read> FilesEntry<R> {
    pub fn name(&self) -> &str {
        self.name.as_ref()
    }

    pub fn source(&self) -> &R {
        &self.source
    }
}

impl TryFrom<Box<Path>> for FilesEntry<fs::File> {
    type Error = FilesError;
    fn try_from(path: Box<Path>) -> Result<Self, Self::Error> {
        let name = path
            .file_stem()
            .and_then(OsStr::to_str)
            .ok_or(FilesError::PathError(
                "cannot get filename from path".to_string(),
            ))?;
        let source = fs::File::open(&path)?;

        Ok(Self {
            name: name.into(),
            source,
        })
    }
}

pub trait FileFilter {
    fn filter(&self, entry: &DirEntry) -> io::Result<Option<Box<Path>>>;
}

pub struct SqlFileFilter {}
impl FileFilter for SqlFileFilter {
    fn filter(&self, entry: &DirEntry) -> io::Result<Option<Box<Path>>> {
        let file_type = entry.file_type()?;
        if !file_type.is_file() {
            return Ok(None);
        }

        let path = entry.path();

        Ok(path.as_path().to_str().and_then(|s| {
            if s.ends_with(".sql") {
                Some(path.as_path().into())
            } else {
                None
            }
        }))
    }
}

pub struct SqlUpFileFilter {}
impl FileFilter for SqlUpFileFilter {
    fn filter(&self, entry: &DirEntry) -> io::Result<Option<Box<Path>>> {
        let file_type = entry.file_type()?;
        if !file_type.is_file() {
            return Ok(None);
        }

        let path = entry.path();

        Ok(path.as_path().to_str().and_then(|s| {
            if s.ends_with(".up.sql") {
                Some(path.as_path().into())
            } else {
                None
            }
        }))
    }
}

#[derive(Debug)]
pub struct Files<F: FileFilter> {
    read_dir: ReadDir,
    file_filter: F,
}

impl<F: FileFilter> Iterator for Files<F> {
    type Item = Result<FilesEntry<fs::File>, FilesError>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(entry) = self.read_dir.next() {
            match entry.and_then(|e| self.file_filter.filter(&e)) {
                Ok(Some(path)) => return Some(path.try_into()),
                Ok(None) => continue,
                Err(err) => return Some(Err(err.into())),
            };
        }
        None
    }
}

impl<F: FileFilter> Files<F> {
    pub fn new<P: AsRef<Path>>(path: P, file_filter: F) -> io::Result<Self> {
        fs::read_dir(path).map(|read_dir| Files {
            read_dir,
            file_filter,
        })
    }

    pub fn try_into_string(self) -> Result<String, FilesError> {
        let mut strings = Vec::<String>::new();

        for file in self {
            let mut s = String::new();
            let file = file?;
            s.push_str("-- ");
            s.push_str(file.name());
            s.push('\n');
            file.source().read_to_string(&mut s)?;

            strings.push(s);
        }

        strings.sort_unstable();

        Ok(strings.join("\n"))
    }
}
