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

    /// A directory contain sql queries
    #[arg(short, long, value_name = "DIR")]
    queries_dir: PathBuf,
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    let mut sqlgen = Sqlgen {
        schema_file: fs::File::open(cli.schema)?,
        queries: Queries::new(cli.queries_dir)?,
        code_generator: TSCodegen {},
        dialect: SqlDialect::Sqlite,
    };

    match sqlgen.run() {
        Ok(s) => io::stdout().write_all(s.as_bytes()),
        Err(err) => {
            let message = format!("Error: {err}");
            io::stderr().write_all(message.as_bytes())
        }
    }
}
