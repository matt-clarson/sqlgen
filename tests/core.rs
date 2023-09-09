use std::{fs, io};

use pretty_assertions::assert_eq;
use sqlgen::{
    core::{Queries, SqlDialect},
    Sqlgen,
};

#[test]
fn typescript_sqlite_simple() -> io::Result<()> {
    let schemafile = "examples/sqlite/simple/schema.sql";
    let queriesdir = "examples/sqlite/simple/queries";
    let outputfile = "examples/sqlite/simple/typescript/queries.ts";

    let expected = fs::read_to_string(outputfile).unwrap();

    let mut sqlgen = Sqlgen {
        schema_file: fs::File::open(schemafile)?,
        queries: Queries::new(queriesdir)?,
        code_generator: sqlgen::lang::typescript::TSCodegen {},
        dialect: SqlDialect::Sqlite,
    };

    let actual = sqlgen.run().unwrap();

    assert_eq!(actual, expected);

    Ok(())
}

#[test]
fn golang_sqlite_simple() -> io::Result<()> {
    let schemafile = "examples/sqlite/simple/schema.sql";
    let queriesdir = "examples/sqlite/simple/queries";
    let outputfile = "examples/sqlite/simple/golang/queries.go";

    let expected = fs::read_to_string(outputfile).unwrap();

    let mut sqlgen = Sqlgen {
        schema_file: fs::File::open(schemafile)?,
        queries: Queries::new(queriesdir)?,
        code_generator: sqlgen::lang::golang::GoCodegen {},
        dialect: SqlDialect::Sqlite,
    };

    let actual = sqlgen.run().unwrap();

    assert_eq!(actual, expected);

    Ok(())
}
