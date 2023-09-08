use std::{
    fs,
    io::{self, Write},
    path::PathBuf,
};

use clap::Parser;
use sqlgen::{
    core::{Queries, SqlDialect},
    lang::typescript::TSCodegen,
    Sqlgen,
};

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
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    let mut sqlgen = Sqlgen {
        schema_file: fs::File::open(cli.schema)?,
        queries: Queries::new(cli.queries_dir)?,
        code_generator: TSCodegen {},
        dialect: SqlDialect::Sqlite,
    };

    let mut out: Box<dyn io::Write> = match cli.outfile {
        Some(path) => Box::new(fs::File::create(path)?),
        None => Box::new(io::stdout()),
    };

    match sqlgen.run() {
        Ok(s) => out.write_all(s.as_bytes()),
        Err(err) => {
            let message = format!("Error: {err}");
            io::stderr().write_all(message.as_bytes())
        }
    }
}
