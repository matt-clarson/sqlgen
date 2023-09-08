# Sqlgen

A CLI tool for generating typed code for SQL queries.

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
sqlgen -s ./schema.sql -q ./queries/ > my-queries.ts
# or use the -o flag for an output file
sqlgen -s ./schema.sql -q ./queries. -o my-queries.ts
```

## Install

For now, the only way to install `sqlgen` is to build it from source. This requires an up-to-date, stable Rust installation:

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
arg = "$" ident "::" type
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

### Languages

Currently, `sqlgen` only outputs TypeScript.

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
| Aliases (fields and tables) | ✅ |
| JOINs                                                   | ✅        |
| CTEs                                                    | ❌        |
| Subqueries                                              | ❌        |
| Aggregate Functions (`count()`, `avg()`, etc.)          | ❌        |
| Scalar Functions (`coalesce()`, `substr()`, etc.)       | ❌        |
| Casting (`CAST('1' AS INT)`, or `'1'::int` in Postgres) | ❌        |
| INSERT statemements (incl. `RETURNING`)                 | ✅        |
| UPDATE statemements (incl. `RETURNING`)                 | ✅        |
| DELETE statemements (incl. `RETURNING`)                 | ✅        |
