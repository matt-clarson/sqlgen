use std::{fs, io};

use pretty_assertions::assert_eq;
use sqlgen::{
    core::{Files, SqlDialect, SqlFileFilter, SqlUpFileFilter},
    Sqlgen,
};

#[test]
fn typescript_sqlite_simple() -> io::Result<()> {
    let schemafile = "examples/sqlite/simple/schema.sql";
    let queriesdir = "examples/sqlite/simple/queries";
    let outputfile = "examples/sqlite/simple/typescript/queries.ts";

    let expected = fs::read_to_string(outputfile).unwrap();

    let mut sqlgen = Sqlgen {
        schema: fs::read_to_string(schemafile)?,
        queries: Files::new(queriesdir, SqlFileFilter {})?,
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
        schema: fs::read_to_string(schemafile)?,
        queries: Files::new(queriesdir, SqlFileFilter {})?,
        code_generator: sqlgen::lang::golang::GoCodegen::default(),
        dialect: SqlDialect::Sqlite,
    };

    let actual = sqlgen.run().unwrap();

    assert_eq!(actual, expected);

    Ok(())
}

#[test]
fn typescript_sqlite_migration() -> io::Result<()> {
    let migration_dir = "examples/sqlite/migration/migrations";
    let queriesdir = "examples/sqlite/migration/queries";
    let outputfile = "examples/sqlite/migration/typescript/queries.ts";

    let expected = fs::read_to_string(outputfile).unwrap();

    let mut sqlgen = Sqlgen {
        schema: Files::new(migration_dir, SqlUpFileFilter {})?.try_into_string()?,
        queries: Files::new(queriesdir, SqlFileFilter {})?,
        code_generator: sqlgen::lang::typescript::TSCodegen {},
        dialect: SqlDialect::Sqlite,
    };

    let actual = sqlgen.run().unwrap();

    assert_eq!(actual, expected);

    Ok(())
}

#[test]
fn golang_sqlite_migration() -> io::Result<()> {
    let migration_dir = "examples/sqlite/migration/migrations";
    let queriesdir = "examples/sqlite/migration/queries";
    let outputfile = "examples/sqlite/migration/golang/queries.go";

    let expected = fs::read_to_string(outputfile).unwrap();

    let mut sqlgen = Sqlgen {
        schema: Files::new(migration_dir, SqlUpFileFilter {})?.try_into_string()?,
        queries: Files::new(queriesdir, SqlFileFilter {})?,
        code_generator: sqlgen::lang::golang::GoCodegen::default(),
        dialect: SqlDialect::Sqlite,
    };

    let actual = sqlgen.run().unwrap();

    assert_eq!(actual, expected);

    Ok(())
}

#[test]
fn typescript_sqlite_aggregation() -> io::Result<()> {
    let schemafile = "examples/sqlite/aggregation/schema.sql";
    let queriesdir = "examples/sqlite/aggregation/queries";
    let outputfile = "examples/sqlite/aggregation/typescript/queries.ts";

    let expected = fs::read_to_string(outputfile).unwrap();

    let mut sqlgen = Sqlgen {
        schema: fs::read_to_string(schemafile)?,
        queries: Files::new(queriesdir, SqlFileFilter {})?,
        code_generator: sqlgen::lang::typescript::TSCodegen {},
        dialect: SqlDialect::Sqlite,
    };

    let actual = sqlgen.run().unwrap();

    assert_eq!(actual, expected);

    Ok(())
}

#[test]
fn golang_sqlite_aggregation() -> io::Result<()> {
    let schemafile = "examples/sqlite/aggregation/schema.sql";
    let queriesdir = "examples/sqlite/aggregation/queries";
    let outputfile = "examples/sqlite/aggregation/golang/queries.go";

    let expected = fs::read_to_string(outputfile).unwrap();

    let mut sqlgen = Sqlgen {
        schema: fs::read_to_string(schemafile)?,
        queries: Files::new(queriesdir, SqlFileFilter {})?,
        code_generator: sqlgen::lang::golang::GoCodegen::default(),
        dialect: SqlDialect::Sqlite,
    };

    let actual = sqlgen.run().unwrap();

    assert_eq!(actual, expected);

    Ok(())
}

