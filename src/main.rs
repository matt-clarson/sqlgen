use std::{
    fs,
    io::{self, Write},
    path::PathBuf,
};

use clap::{Parser, Subcommand, ValueEnum};
use sqlgen::{
    core::{Queries, SqlDialect},
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

#[derive(Subcommand)]
enum Command {
    /// Generate go code for the given schema and queries.
    Golang {
        /// The sql schema file to use.
        #[arg(short, long, value_name = "FILE")]
        schema: PathBuf,

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
        /// The sql schema file to use.
        #[arg(short, long, value_name = "FILE")]
        schema: PathBuf,

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
            schema,
            queries_dir,
            outfile,
        } => {
            let schema_file = fs::File::open(schema)?;
            let queries = Queries::new(queries_dir)?;
            let dialect = SqlDialect::Sqlite;

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
                schema_file,
                queries,
                code_generator,
                dialect,
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
            schema,
            queries_dir,
            outfile,
        } => {
            let schema_file = fs::File::open(schema)?;
            let queries = Queries::new(queries_dir)?;
            let dialect = SqlDialect::Sqlite;

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
                schema_file,
                queries,
                code_generator: TSCodegen {},
                dialect,
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
