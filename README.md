# Sqlgen

A CLI tool for generating typed code for SQL queries.

![CI](https://github.com/matt-clarson/sqlgen/actions/workflows/ci.yml/badge.svg)

## Get Started

Define a database schema using SQL, put it in a file called `schema.sql`:

```sql
CREATE TABLE users (
    id INT PRIMARY KEY,
    email TEXT NOT NULL,
    nickname TEXT
);
```

Then, define some queries, using SQL again, in a single directory `queries/`:

`queries/get-all-user-nicknames.sql`

```sql
SELECT id, nickname FROM users;
```

`queries/find-user-by-email.sql`

```sql
SELECT * FROM users
WHERE email = $email::text;
```

Finally, run `sqlgen` to produce typed code:

```sh
sqlgen typescript -s ./schema.sql -q ./queries/ > my-queries.ts
# or use the -o flag for an output file
sqlgen typescript -s ./schema.sql -q ./queries. -o my-queries.ts
```

To see all the CLI options, run:

```sh
sqlgen --help
```

## Install

### Pre-built binaries

Pre-built binaries are available from GitHub -> https://github.com/matt-clarson/sqlgen/releases.

### Build from source

This requires an up-to-date, stable Rust installation:

```sh
# clone the repo
git clone https://github.com/matt-clarson/sqlgen.git --depth=1

# use cargo to build and install the sqlgen executable
cargo install --path ./sqlgen/

# verify the installation
sqlgen --version
```

Note `sqlgen` will only be in your path if Cargo is configured to install to a directory in your path. The default install directory is `~/.cargo/bin`.

## Examples

Check out [the examples](./examples/) in this repository to see what code is generated for schemas and queries.

## Features

### Calculating output types

Output types will be calculated based on the provided SQL schema. For example with a table schema like this:

```sql
CREATE TABLE my_table (
    col_a INT PRIMARY KEY,
    col_b TEXT
```

If we run `sqlgen` on this query:

```sql
SELECT * FROM my_table;
```

The output type (in TypeScript) will be:

```typescript
{
    // INT gets converted to the TypeScript number
    colA: number;
    // TEXT gets converted to the TypeSCript string
    // also, col_b is nullable, which is reflected in the output type
    colB: string | null;
}
```

### Relational queries

`sqlgen` understands the complete schema, and can handle queries referencing multiple tables:

If we extend our schema to include another table:

```sql
CREATE TABLE another_table (
    id INT PRIMARY KEY,
    name TEXT NOT NULL,
    ref INT,
    FOREIGN KEY (ref) REFERENCES my_table(col_a)
);
```

And then add a query over both tables:

```sql
SELECT id, name, col_b
FROM another_table
    JOIN my_table ON id=col_a;
```

The output type will be:

```typescript
{
    id: number;
    name: string;
    // The definition of col_b is brought in from the `my_table` definition
    colB: string | null;
}
```

### Arguments

`sqlgen` also supports queries with dynamic arguments, using a small extension to the SQL spec.

Specifically, an argument is defined as follows:

```ebnf
arg = "$" ident "::" [ "?" ] type
ident = alpha { alphanum }
alphanum = alpha | "0" | "1" | "2" | "3" | "4" | "5" | "8" | "9";
type = "tinyint" | "smallint" | "int" | "bigint"
     | "float" | "double" | "bool" | "text" | "blob";
alpha = "A" | "B" | "C" | "D" | "E" | "F" | "G"
      | "H" | "I" | "J" | "K" | "L" | "M" | "N"
      | "O" | "P" | "Q" | "R" | "S" | "T" | "U"
      | "V" | "W" | "X" | "Y" | "Z" | "a" | "b"
      | "c" | "d" | "e" | "f" | "g" | "h" | "i"
      | "j" | "k" | "l" | "m" | "n" | "o" | "p"
      | "q" | "r" | "s" | "t" | "u" | "v" | "w"
      | "x" | "y" | "z" | "_" ;
```

Given the SQL schemas we've already defined above, we could have the following query:

```sql
SELECT * FROM my_table
    JOIN another_table ON col_a=id
WHERE name = $someName::text AND
      col_a > $val::int;
```

This would produce an _argument_ type in the generated code, that looks like this:

```typescript
{
    someName: string;
    val: number;
}
```

And the generated code would replace the argument syntax with proper injection bindings - for Sqlite that would look like this:

```sql
SELECT * FROM my_table
    JOIN another_table ON col_a=id
WHERE name = ? AND
      col_a > ?;
```

You can include a `?` character to denote an optional argument - these will be converted into a null-like value for the target language:

```sql
$myarg::?int
```

becomes:

```typescript
// in typescript
let myarg: number | null;
```

```golang
// in go
var myarg sql.NullInt32
```

### Languages

#### Typescript

`sqlgen typescript` will generate typescript code. It accepts the following arguments:

| Name                   | Required | Description                                                                                                                                                                                          |
| ---------------------- | -------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `-s` `--schema`        | No       | The sql schema file to use. One of `--schema` or `--migration-dir` must be provided.                                                                                                                 |
| `-m` `--migration-dir` | No       | A directory of migration files to use. Only files ending in `.up.sql` will be used, and files will be read in ascending alphanumeric order. One of `--schema` or `--migration-dir` must be provided. |
| `-q` `--queries-dir`   | Yes      | A directory containing sql queries.                                                                                                                                                                  |
| `-o` `--outfile`       | No       | File to output to - if not provided sqlgen will write output to stdout.                                                                                                                              |

To use the generated code, a `Dispatcher` implementation should be created. You can see the definition fof this interface in the `examples/` directory.

#### Golang

`sqlgen golang` will generate go code. It accepts the following arguments:

| Name                   | Required | Description                                                                                                                                                                                                                                                                                                        |
| ---------------------- | -------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `-s` `--schema`        | No       | The sql schema file to use. One of `--schema` or `--migration-dir` must be provided.                                                                                                                                                                                                                               |
| `-m` `--migration-dir` | No       | A directory of migration files to use. Only files ending in `.up.sql` will be used, and files will be read in ascending alphanumeric order. One of `--schema` or `--migration-dir` must be provided.                                                                                                               |
| `-q` `--queries-dir`   | Yes      | A directory containing sql queries.                                                                                                                                                                                                                                                                                |
| `-o` `--outfile`       | No       | File to output to - if not provided sqlgen will write output to stdout. Uses this file to determine the generated package name - if the path is a single file, uses the filename, otherwise uses the first parent directory name. If this arg is not provided, 'queries' will be used as the default package name. |

You can use `sqlgen` as a `go generate` directive - the example below assumes we have followed the get started example at the top of this file:

```go
package main

import (
    "context"
    "database/sql"
    "fmt"
    "log"

    // generated with the directive below
    "mypkg/queries"
)

//go:generate sqlgen golang -s sql/schema.sql -q sql/queries/ -o queries/queries.go

func main() {
    var db *sql.DB = CreateDBSomehow()

    rows, err := queries.GetAllUserNicknames(db, context.Background())
    if err != nil {
        log.Fatal(err)
    }

    for _, row := range rows {
        fmt.Println("id: %d; nickname %s", row.Id, row.Nickname)
    }
}
```

### SQL

#### SQL Dialects

The following dialects are supported by `sqlgen` - any dialects not listed are not currently planned to have support:

| Dialect  | Supported |
| -------- | --------- |
| Sqlite   | ✅        |
| MySQL    | ❌        |
| Postgres | ❌        |

#### Spec

The following SQL is currently understood by the `sqlgen` parser - support for other parts of the SQL spec will be added over time.:

| Type                                                    | Supported |
| ------------------------------------------------------- | --------- |
| SELECT statements                                       | ✅        |
| Aliases (fields and tables)                             | ✅        |
| JOINs                                                   | ✅        |
| CTEs                                                    | ❌        |
| Subqueries                                              | ❌        |
| Aggregate Functions (`count()`, `avg()`, etc.)          | ❌        |
| Scalar Functions (`coalesce()`, `substr()`, etc.)       | ❌        |
| Casting (`CAST('1' AS INT)`, or `'1'::int` in Postgres) | ❌        |
| INSERT statemements (incl. `RETURNING`)                 | ✅        |
| UPDATE statemements (incl. `RETURNING`)                 | ✅        |
| DELETE statemements (incl. `RETURNING`)                 | ✅        |

## Development

Tests can be run with Cargo:

```sh
cargo test
```

Releases are manual for now. To create a new release, use cargo-release, and cross

Install them like so:

```sh
cargo install cross cargo-release
```

Then run the following scripts:

```sh
# increment the package version - for now only alpha is used as this project is in a pre-release state - eventually any semver increment can be used: major, minor, patch, etc.
cargo release version alpha --execute

# commit the version bump
cargo release commit --execute

# tag the latest commit with the new version
cargo release tag --execute

# use a custom build script to cross-compile for a defined set of target architectures
./build-releases.sh
```

The output of the `build-releases.sh` script should be published using GitHub Releases
