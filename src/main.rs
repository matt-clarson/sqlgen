use std::{
    fs,
    io::{self, Write},
    path::PathBuf,
};

use clap::{Parser, ValueEnum};
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
    /// The sql schema file to use.
    #[arg(short, long, value_name = "FILE")]
    schema: PathBuf,

    /// A directory containing sql queries.
    #[arg(short, long, value_name = "DIR")]
    queries_dir: PathBuf,

    /// File to output to - if not provided sqlgen will write output to stdout.
    #[arg(short, long, value_name = "FILE")]
    outfile: Option<PathBuf>,

    #[arg(short, long)]
    target: LangTarget,
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    let schema_file = fs::File::open(cli.schema)?;
    let queries = Queries::new(cli.queries_dir)?;
    let dialect = SqlDialect::Sqlite;

    let mut out: Box<dyn io::Write> = match cli.outfile {
        Some(path) => Box::new(fs::File::create(path)?),
        None => Box::new(io::stdout()),
    };

    let result = match cli.target {
        LangTarget::Typescript => {
            let mut sqlgen = Sqlgen {
                schema_file,
                queries,
                code_generator: TSCodegen {},
                dialect,
            };
            sqlgen.run()
        }
        LangTarget::Golang => {
            let mut sqlgen = Sqlgen {
                schema_file,
                queries,
                code_generator: GoCodegen {},
                dialect,
            };
            sqlgen.run()
        }
    };

    match result {
        Ok(s) => out.write_all(s.as_bytes()),
        Err(err) => {
            let message = format!("Error: {err}");
            io::stderr().write_all(message.as_bytes())
        }
    }
}
