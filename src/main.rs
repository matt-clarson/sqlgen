use std::{
    fs,
    io::{self, Write},
    path::PathBuf,
};

use clap::{Parser, Subcommand, ValueEnum};
use sqlgen::{
    core::{Files, SqlDialect, SqlFileFilter, SqlUpFileFilter},
    lang::{golang::GoCodegen, typescript::TSCodegen},
    Sqlgen,
};

/// Language to target for generation
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum LangTarget {
    Typescript,
    Golang,
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Copy, Clone, clap::ValueEnum)]
enum Dialect {
    Sqlite,
    Postgres,
}

impl From<Dialect> for SqlDialect {
    fn from(value: Dialect) -> Self {
        match value {
            Dialect::Sqlite => SqlDialect::Sqlite,
            Dialect::Postgres => SqlDialect::Postgres,
        }
    }
}

#[derive(Subcommand)]
enum Command {
    /// Generate go code for the given schema and queries.
    Golang {
        /// The SQL dialect to use - affects how arguments bindings are rendered and what
        /// types/functions are available.
        #[arg(short, long)]
        dialect: Dialect,

        /// The sql schema file to use. Either this option OR --migration_dir must be provided.
        #[arg(short, long, value_name = "FILE")]
        schema: Option<PathBuf>,

        /// The migrations dir to use, will sort files named <file>.up.sql in ascending order, and
        /// use them to determine the database schema to use. Either this option OR --schema must
        /// be provided.
        #[arg(short, long, value_name = "DIR")]
        migration_dir: Option<PathBuf>,

        /// A directory containing sql queries.
        #[arg(short, long, value_name = "DIR")]
        queries_dir: PathBuf,

        /// File to output to - if not provided sqlgen will write output to stdout.
        ///
        /// Uses this file to determine the generated package name - if the path is a single file,
        /// uses the filename, otherwise uses the first parent directory name.
        ///
        /// If this arg is not provided, 'queries' will be used as the default package name.
        ///
        /// --outfile mypackage.go --> package would be 'mypackage'
        ///
        /// --outfile something/file.go --> package would be 'something'  
        #[arg(short, long, value_name = "FILE")]
        outfile: Option<PathBuf>,
    },
    /// Generate typescript code for the given schema and queries.
    Typescript {
        /// The SQL dialect to use - affects how arguments bindings are rendered and what
        /// types/functions are available.
        #[arg(short, long)]
        dialect: Dialect,

        /// The sql schema file to use. Either this option OR --migration_dir must be provided.
        #[arg(short, long, value_name = "FILE")]
        schema: Option<PathBuf>,

        /// The migrations dir to use, will sort files named <file>.up.sql in ascending order, and
        /// use them to determine the database schema to use. Either this option OR --schema must
        /// be provided.
        #[arg(short, long, value_name = "DIR")]
        migration_dir: Option<PathBuf>,

        /// A directory containing sql queries.
        #[arg(short, long, value_name = "DIR")]
        queries_dir: PathBuf,

        /// File to output to - if not provided sqlgen will write output to stdout.
        #[arg(short, long, value_name = "FILE")]
        outfile: Option<PathBuf>,
    },
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Command::Golang {
            dialect,
            schema,
            migration_dir,
            queries_dir,
            outfile,
        } => {
            let schema = load_schema(schema, migration_dir)?;
            let queries = Files::new(queries_dir, SqlFileFilter {})?;

            let mut out: Box<dyn io::Write> = match &outfile {
                Some(path) => {
                    if let Some(parent_dir) = path.parent() {
                        fs::create_dir_all(parent_dir)?;
                    }
                    Box::new(fs::File::create(path)?)
                }
                None => Box::new(io::stdout()),
            };
            let code_generator = match outfile {
                Some(path) => GoCodegen::from(path.as_path()),
                None => GoCodegen::default(),
            };
            let mut sqlgen = Sqlgen {
                schema,
                queries,
                code_generator,
                dialect: dialect.into(),
            };
            match sqlgen.run() {
                Ok(s) => out.write_all(s.as_bytes()),
                Err(err) => {
                    let message = format!("Error: {err}");
                    io::stderr().write_all(message.as_bytes())
                }
            }
        }
        Command::Typescript {
            dialect,
            schema,
            migration_dir,
            queries_dir,
            outfile,
            ..
        } => {
            let schema = load_schema(schema, migration_dir)?;
            let queries = Files::new(queries_dir, SqlFileFilter {})?;

            let mut out: Box<dyn io::Write> = match outfile {
                Some(path) => {
                    if let Some(parent_dir) = path.parent() {
                        fs::create_dir_all(parent_dir)?;
                    }
                    Box::new(fs::File::create(path)?)
                }
                None => Box::new(io::stdout()),
            };
            let mut sqlgen = Sqlgen {
                schema,
                queries,
                code_generator: TSCodegen {},
                dialect: dialect.into(),
            };
            match sqlgen.run() {
                Ok(s) => out.write_all(s.as_bytes()),
                Err(err) => {
                    let message = format!("Error: {err}");
                    io::stderr().write_all(message.as_bytes())
                }
            }
        }
    }
}

fn load_schema(schema_file: Option<PathBuf>, migration_dir: Option<PathBuf>) -> io::Result<String> {
    if let Some(path) = schema_file {
        return fs::read_to_string(path);
    }

    if let Some(path) = migration_dir {
        let files = Files::new(path, SqlUpFileFilter {})?;
        files.try_into_string().map_err(|e| e.into())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "one of --schema or --migration-dir is required",
        ))
    }
}
