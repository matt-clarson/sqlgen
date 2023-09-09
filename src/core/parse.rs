use std::{borrow::Borrow, collections::HashMap, fmt::Display, hash::Hash};

use sqlparser::{
    ast::{self, Expr, ObjectName, SelectItem, SetExpr, Statement, TableFactor},
    dialect,
    parser::Parser,
};

use crate::error::SqlgenError;

use super::argparse;

impl From<&super::SqlDialect> for Parser<'_> {
    fn from(dialect: &super::SqlDialect) -> Self {
        match dialect {
            super::SqlDialect::Sqlite => Parser::new(&dialect::SQLiteDialect {}),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct NamedQuery {
    name: String,
    query: Query,
    raw: String,
    args: Vec<argparse::Arg>,
}

impl NamedQuery {
    pub fn name(&self) -> &str {
        self.name.as_ref()
    }

    pub fn query(&self) -> &Query {
        &self.query
    }

    pub fn raw(&self) -> &str {
        self.raw.trim()
    }

    pub fn args(&self) -> &[argparse::Arg] {
        self.args.as_ref()
    }
}

impl PartialOrd for NamedQuery {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.name.partial_cmp(&other.name)
    }
}

#[derive(Debug, PartialEq)]
pub struct Schema {
    tables: Vec<Table>,
}

impl Schema {
    pub fn get_table<S: AsRef<str>>(&self, name: S) -> Option<&Table> {
        self.tables
            .iter()
            .find(|&table| table.name.as_str() == name.as_ref())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Table {
    name: String,
    fields: OrderedHashMap<String, FieldDef>,
}

impl PartialOrd for Table {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.name.partial_cmp(&other.name)
    }
}

impl Table {
    pub fn new(name: String) -> Self {
        Self {
            name,
            fields: OrderedHashMap::new(),
        }
    }

    pub fn insert_field(&mut self, name: String, field_def: FieldDef) {
        self.fields.insert(name, field_def);
    }

    pub fn get_sorted_fields(&self) -> Vec<&FieldDef> {
        self.fields.values().collect()
    }

    pub fn find_field<S: AsRef<str>>(&self, name: S) -> Option<&FieldDef> {
        self.fields.get(name.as_ref())
    }
}

#[derive(Debug, PartialEq)]
pub struct Query {
    projection: Vec<FieldDef>,
}

impl Query {
    pub fn into_named<S: Into<String>>(
        self,
        name: S,
        raw: S,
        args: Vec<argparse::Arg>,
    ) -> NamedQuery {
        NamedQuery {
            name: name.into(),
            query: self,
            raw: raw.into(),
            args,
        }
    }

    pub fn projection(&self) -> &Vec<FieldDef> {
        &self.projection
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldDef {
    name: String,
    sqltype: SqlType,
    nullable: bool,
}

impl PartialOrd for FieldDef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.name.partial_cmp(&other.name)
    }
}

impl FieldDef {
    pub fn clone_with_alias<S: std::fmt::Display>(&self, alias: S) -> Self {
        Self {
            name: alias.to_string(),
            sqltype: self.sqltype,
            nullable: self.nullable,
        }
    }

    pub fn name(&self) -> &str {
        self.name.as_ref()
    }

    pub fn sqltype(&self) -> SqlType {
        self.sqltype
    }

    pub fn nullable(&self) -> bool {
        self.nullable
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SqlType {
    Bool,
    Float32,
    Float64,
    Int8,
    Int16,
    Int32,
    Int64,
    Text,
    Binary,
}

#[derive(Debug)]
pub struct Sqlparser {
    dialect: super::SqlDialect,
}

impl Sqlparser {
    pub fn with_dialect(dialect: super::SqlDialect) -> Self {
        Self { dialect }
    }

    pub fn parse_schema<S: AsRef<str>>(&self, sql: S) -> Result<Schema, SqlgenError> {
        let statements = self.parse_to_statements(sql)?;

        let mut schema = Schema { tables: vec![] };

        for stmt in statements {
            if let Some(table) = self.statement_to_table(&stmt).unwrap() {
                schema.tables.push(table);
            }
        }

        Ok(schema)
    }

    pub fn parse_query<S: AsRef<str>>(
        &self,
        sql: S,
        schema: &Schema,
    ) -> Result<Query, SqlgenError> {
        let statements = self.parse_to_statements(sql)?;
        let stmt = statements.first().ok_or(SqlgenError::EmptyQuery)?;

        let mut out_query = Query { projection: vec![] };

        match stmt {
            Statement::Insert {
                returning: None, ..
            } => Ok(out_query),
            Statement::Insert {
                table_name,
                returning: Some(projection),
                ..
            } => {
                let mut query_tables = QueryTables::new(schema);
                query_tables.try_insert_table(table_name)?;
                for select_item in projection {
                    for field in query_tables.get_fields_for_select_item(select_item)? {
                        out_query.projection.push(field)
                    }
                }
                Ok(out_query)
            }
            Statement::Update {
                returning: None, ..
            } => Ok(out_query),
            Statement::Update {
                table,
                returning: Some(projection),
                ..
            } => {
                let mut query_tables = QueryTables::new(schema);
                for join in &table.joins {
                    query_tables.try_insert_table_factor(&join.relation)?;
                }
                query_tables.try_insert_table_factor(&table.relation)?;

                for select_item in projection {
                    for field in query_tables.get_fields_for_select_item(select_item)? {
                        out_query.projection.push(field)
                    }
                }
                Ok(out_query)
            }
            Statement::Delete {
                returning: None, ..
            } => Ok(out_query),
            Statement::Delete {
                from,
                returning: Some(projection),
                ..
            } => {
                let mut query_tables = QueryTables::new(schema);
                for table_with_joins in from {
                    for join in &table_with_joins.joins {
                        query_tables.try_insert_table_factor(&join.relation)?;
                    }
                    query_tables.try_insert_table_factor(&table_with_joins.relation)?;
                }

                for select_item in projection {
                    for field in query_tables.get_fields_for_select_item(select_item)? {
                        out_query.projection.push(field)
                    }
                }

                Ok(out_query)
            }
            Statement::Query(query) => {
                if query.with.is_some() {
                    return Err(SqlgenError::Unsupported(
                        "CTEs are not supported".to_string(),
                    ));
                }
                return match query.body.as_ref() {
                    SetExpr::Select(select) => {
                        let mut query_tables = QueryTables::new(schema);
                        for table_with_joins in &select.from {
                            for join in &table_with_joins.joins {
                                query_tables.try_insert_table_factor(&join.relation)?;
                            }
                            query_tables.try_insert_table_factor(&table_with_joins.relation)?;
                        }

                        for select_item in &select.projection {
                            for field in query_tables.get_fields_for_select_item(select_item)? {
                                out_query.projection.push(field);
                            }
                        }

                        return Ok(out_query);
                    }
                    _ => Err(SqlgenError::Unsupported(
                        "only SELECT, UPDATE, INSERT, and DELETE statements are supported in queries".to_string(),
                    )),
                };
            }
            _ => Err(SqlgenError::Unsupported(
                "only SELECT, UPDATE, INSERT, and DELETE  statements are supported in queries"
                    .to_string(),
            )),
        }
    }

    fn parse_to_statements<S: AsRef<str>>(
        &self,
        sql: S,
    ) -> Result<Vec<sqlparser::ast::Statement>, Box<dyn std::error::Error>> {
        let parser: Parser<'_> = self.dialect.borrow().into();
        parser
            .try_with_sql(sql.as_ref())
            .and_then(|mut p| p.parse_statements())
            .map_err(|e| e.into())
    }

    fn statement_to_table(
        &self,
        stmt: &Statement,
    ) -> Result<Option<Table>, crate::error::SqlgenError> {
        match stmt {
            sqlparser::ast::Statement::CreateTable { name, columns, .. } => {
                let table_name = name.0.last().unwrap().to_string();
                let mut table = Table::new(table_name);
                for coldef in columns {
                    let field_name = coldef.name.to_string();
                    let sqltype = match &coldef.data_type {
                        ast::DataType::Bool | ast::DataType::Boolean => SqlType::Bool,
                        ast::DataType::TinyInt(_) => SqlType::Int8,
                        ast::DataType::SmallInt(_) | ast::DataType::Int2(_) => SqlType::Int16,
                        ast::DataType::Int4(_)
                        | ast::DataType::Integer(_)
                        | ast::DataType::MediumInt(_)
                        | ast::DataType::Int(_) => SqlType::Int32,
                        ast::DataType::BigInt(_) | ast::DataType::Int8(_) => SqlType::Int64,
                        ast::DataType::Text => SqlType::Text,
                        ast::DataType::Real | ast::DataType::Float4 => SqlType::Float32,
                        ast::DataType::Float(_)
                        | ast::DataType::Float8
                        | ast::DataType::Double
                        | ast::DataType::DoublePrecision => SqlType::Float64,
                        ast::DataType::Blob(_) => SqlType::Binary,
                        data_type => {
                            return Err(SqlgenError::Unsupported(format!(
                                "data type {data_type} is not supported"
                            )))
                        }
                    };
                    let not_null = coldef.options.iter().any(|opt| {
                        matches!(
                            opt.option,
                            ast::ColumnOption::NotNull
                                | ast::ColumnOption::Unique { is_primary: true }
                        )
                    });
                    let field = FieldDef {
                        name: field_name.clone(),
                        sqltype,
                        nullable: !not_null,
                    };
                    table.insert_field(field_name, field);
                }
                Ok(Some(table))
            }
            _ => Ok(None),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct OrderedHashMap<K: Clone + Eq + PartialEq + Hash, V> {
    hash_map: HashMap<K, V>,
    ordered_keys: Vec<K>,
}

impl<K: Clone + Eq + PartialEq + Hash, V> OrderedHashMap<K, V> {
    pub fn new() -> Self {
        Self {
            hash_map: HashMap::new(),
            ordered_keys: Vec::new(),
        }
    }

    pub fn insert(&mut self, k: K, v: V) {
        self.hash_map.insert(k.clone(), v);
        self.ordered_keys.push(k);
    }

    pub fn get<Q>(&self, k: &Q) -> Option<&V>
        where
            Q: ?Sized,
            K: Borrow<Q>,
            Q: Eq + Hash
    {
        self.hash_map.get(k)
    }

    pub fn values<'a>(&'a self) -> Box<dyn Iterator<Item = &V> + 'a> {
        let iter = self
            .ordered_keys
            .iter()
            .map(|k| unsafe { self.hash_map.get(k).unwrap_unchecked() });
        Box::new(iter)
    }
}

impl <K: Clone + Eq + PartialEq + Hash, V, const N: usize> From<[(K, V); N]> for OrderedHashMap<K, V> {
    fn from(pairs: [(K, V); N]) -> Self {
        let mut hash_map = Self::new();
        for (k, v) in pairs {
            hash_map.insert(k, v);
        }
        hash_map
    }
}

struct QueryTables<'a> {
    schema: &'a Schema,
    tables: OrderedHashMap<String, Table>,
}

impl<'a> QueryTables<'a> {
    fn new(schema: &'a Schema) -> Self {
        Self {
            schema,
            tables: OrderedHashMap::new(),
        }
    }

    fn insert<S: Into<String>>(&mut self, name: S, table: Table) {
        self.tables.insert(name.into(), table);
    }

    fn find_table<S: AsRef<str>>(&self, table_name: S) -> Option<&Table> {
        self.tables.get(table_name.as_ref())
    }

    fn all_table_fields(&self) -> Vec<&FieldDef> {
        self.tables
            .values()
            .flat_map(|t| t.get_sorted_fields())
            .collect()
    }

    fn find_qualified_field<S: Display>(&self, name_parts: &[S]) -> Option<&FieldDef> {
        let table_name = name_parts.first().unwrap().to_string();
        let field_name = name_parts.last().unwrap().to_string();

        self.tables
            .get(&table_name)
            .and_then(|table| table.find_field(&field_name))
    }

    fn find_field<S: AsRef<str>>(&self, field_name: S) -> Option<&FieldDef> {
        for table in self.tables.values() {
            if let Some(field) = table.find_field(field_name.as_ref()) {
                return Some(field);
            }
        }
        None
    }

    fn try_insert_table_factor(&mut self, table_factor: &TableFactor) -> Result<(), SqlgenError> {
        match table_factor {
            sqlparser::ast::TableFactor::Table { name, alias, .. } => {
                let table_name = alias
                    .as_ref()
                    .map(|a| a.name.to_string())
                    .unwrap_or_else(|| name.0.last().unwrap().to_string());
                if let Some(table) = self.schema.get_table(&name.to_string()) {
                    self.insert(table_name, table.clone());
                    Ok(())
                } else {
                    Err(SqlgenError::EntityNotFound(format!(
                        "table {name} does not exist in known schema"
                    )))
                }
            }
            _ => Err(SqlgenError::Unsupported(
                "only named table expressions are supported in FROM clauses".to_string(),
            )),
        }
    }

    fn try_insert_table(&mut self, name: &ObjectName) -> Result<(), SqlgenError> {
        let table_name = name.0.last().unwrap().to_string();
        if let Some(table) = self.schema.get_table(&name.to_string()) {
            self.insert(table_name, table.clone());
            Ok(())
        } else {
            Err(SqlgenError::EntityNotFound(format!(
                "table {name} does not exist in known schema"
            )))
        }
    }

    fn get_fields_for_select_item<'b>(
        &'b self,
        select_item: &SelectItem,
    ) -> Result<Box<dyn Iterator<Item = FieldDef> + 'b>, SqlgenError> {
        match select_item {
            SelectItem::Wildcard(_) => {
                let iter = self.all_table_fields().into_iter().cloned();
                Ok(Box::new(iter))
            }
            SelectItem::QualifiedWildcard(table_name, _) => {
                let name = table_name.to_string();
                if let Some(table) = self.find_table(&name) {
                    let iter = table.get_sorted_fields().into_iter().cloned();
                    Ok(Box::new(iter))
                } else {
                    Err(SqlgenError::EntityNotFound(name))
                }
            }
            SelectItem::UnnamedExpr(Expr::Identifier(ident)) => {
                if let Some(field) = self.find_field(&ident.value) {
                    Ok(Box::new(Singleton::from(field.clone())))
                } else {
                    Err(SqlgenError::EntityNotFound(ident.to_string()))
                }
            }
            SelectItem::UnnamedExpr(Expr::CompoundIdentifier(idents)) => {
                if let Some(field) = self.find_qualified_field(idents) {
                    Ok(Box::new(Singleton::from(field.clone())))
                } else {
                    Err(SqlgenError::EntityNotFound(compound_name(idents)))
                }
            }
            SelectItem::ExprWithAlias {
                expr: Expr::Identifier(ident),
                alias,
            } => {
                if let Some(field) = self.find_field(&ident.value) {
                    Ok(Box::new(Singleton::from(field.clone_with_alias(alias))))
                } else {
                    Err(SqlgenError::EntityNotFound(ident.to_string()))
                }
            }
            SelectItem::ExprWithAlias {
                expr: Expr::CompoundIdentifier(idents),
                alias,
            } => {
                if let Some(field) = self.find_qualified_field(idents) {
                    Ok(Box::new(Singleton::from(field.clone_with_alias(alias))))
                } else {
                    Err(SqlgenError::EntityNotFound(compound_name(idents)))
                }
            }
            c => Err(SqlgenError::Unsupported(format!(
                "got unsupported select projection: {c:?}",
            ))),
        }
    }
}

/// A singleton iterator - yields the contained value exactly once.
struct Singleton<T> {
    value: Option<T>,
}
impl<T> From<T> for Singleton<T> {
    fn from(value: T) -> Self {
        Self { value: Some(value) }
    }
}
impl<T> Iterator for Singleton<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        Option::take(&mut self.value)
    }
}

fn compound_name<S: Display>(name: &[S]) -> String {
    name.iter()
        .fold(String::new(), |acc, n| acc + &n.to_string() + ".")
}

#[cfg(test)]
mod test {
    use super::super::SqlDialect;
    use super::*;

    #[test]
    fn parse_empty_table() {
        let expected = Schema {
            tables: vec![Table {
                name: "empty".to_string(),
                fields: OrderedHashMap::new(),
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let actual = parser.parse_schema("CREATE TABLE empty();").unwrap();

        assert_eq!(expected, actual);
    }

    macro_rules! table_with_typed_column_test {
        ($test_fn:ident, $str_type:expr, $sql_type:expr) => {
            #[test]
            fn $test_fn() {
                let expected = Schema {
                    tables: vec![Table {
                        name: "t1".to_string(),
                        fields: OrderedHashMap::from([(
                            "col".to_string(),
                            FieldDef {
                                name: "col".to_string(),
                                sqltype: $sql_type,
                                nullable: true,
                            },
                        )]),
                    }],
                };

                let parser = Sqlparser {
                    dialect: SqlDialect::Sqlite,
                };

                let actual = parser
                    .parse_schema(format!("CREATE TABLE t1(col {});", $str_type))
                    .unwrap();

                assert_eq!(expected, actual);
            }
        };
    }

    table_with_typed_column_test!(parse_table_with_bool_column, "BOOL", SqlType::Bool);
    table_with_typed_column_test!(parse_table_with_boolean_column, "BOOLEAN", SqlType::Bool);
    table_with_typed_column_test!(parse_table_with_tinyint_column, "TINYINT", SqlType::Int8);
    table_with_typed_column_test!(parse_table_with_smallint_column, "SMALLINT", SqlType::Int16);
    table_with_typed_column_test!(parse_table_with_int2_column, "INT2", SqlType::Int16);
    table_with_typed_column_test!(parse_table_with_int_column, "INT", SqlType::Int32);
    table_with_typed_column_test!(parse_table_with_integer_column, "INTEGER", SqlType::Int32);
    table_with_typed_column_test!(
        parse_table_with_mediumint_column,
        "MEDIUMINT",
        SqlType::Int32
    );
    table_with_typed_column_test!(parse_table_with_int4_column, "INT4", SqlType::Int32);
    table_with_typed_column_test!(parse_table_with_bigint_column, "BIGINT", SqlType::Int64);
    table_with_typed_column_test!(parse_table_with_int8_column, "INT8", SqlType::Int64);
    table_with_typed_column_test!(parse_table_with_text_column, "TEXT", SqlType::Text);
    table_with_typed_column_test!(parse_table_with_real_column, "REAL", SqlType::Float32);
    table_with_typed_column_test!(parse_table_with_float4_column, "FLOAT4", SqlType::Float32);
    table_with_typed_column_test!(parse_table_with_float_column, "FLOAT", SqlType::Float64);
    table_with_typed_column_test!(parse_table_with_float8_column, "FLOAT8", SqlType::Float64);
    table_with_typed_column_test!(parse_table_with_double_column, "DOUBLE", SqlType::Float64);
    table_with_typed_column_test!(
        parse_table_with_double_precision_column,
        "DOUBLE PRECISION",
        SqlType::Float64
    );
    table_with_typed_column_test!(parse_table_with_blob_column, "BLOB", SqlType::Binary);

    #[test]
    fn parse_table_primary_key() {
        let expected = Schema {
            tables: vec![Table {
                name: "t1".to_string(),
                fields: OrderedHashMap::from([(
                    "col".to_string(),
                    FieldDef {
                        name: "col".to_string(),
                        sqltype: SqlType::Int32,
                        nullable: false,
                    },
                )]),
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let actual = parser
            .parse_schema("CREATE TABLE t1(col INT PRIMARY KEY);")
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_wildcard_query() {
        let expected = Query {
            projection: vec![
                FieldDef {
                    name: "id".to_string(),
                    sqltype: SqlType::Int32,
                    nullable: false,
                },
                FieldDef {
                    name: "col_a".to_string(),
                    sqltype: SqlType::Text,
                    nullable: true,
                },
            ],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(id INT NOT NULL, col_a TEXT);")
            .unwrap();
        let actual = parser.parse_query("SELECT * FROM t1;", &schema).unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_named_fields_query() {
        let expected = Query {
            projection: vec![
                FieldDef {
                    name: "id".to_string(),
                    sqltype: SqlType::Int32,
                    nullable: false,
                },
                FieldDef {
                    name: "col_a".to_string(),
                    sqltype: SqlType::Text,
                    nullable: true,
                },
            ],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(id INT NOT NULL, col_a TEXT, col_b INT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT id, col_a FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_aliased_fields_query() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "aliased".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(id INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT id aliased FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_as_aliased_fields_query() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "aliased".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(id INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT id AS aliased FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_multiple_table_query() {
        let expected = Query {
            projection: vec![
                FieldDef {
                    name: "col_a".to_string(),
                    sqltype: SqlType::Int32,
                    nullable: false,
                },
                FieldDef {
                    name: "col_b".to_string(),
                    sqltype: SqlType::Text,
                    nullable: true,
                },
            ],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL); CREATE TABLE t2(col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT col_a, col_b FROM t1, t2;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_multiple_table_wildcard_query() {
        let expected = Query {
            projection: vec![
                FieldDef {
                    name: "col_a".to_string(),
                    sqltype: SqlType::Int32,
                    nullable: false,
                },
                FieldDef {
                    name: "col_b".to_string(),
                    sqltype: SqlType::Text,
                    nullable: true,
                },
            ],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL); CREATE TABLE t2(col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT * FROM t1, t2;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_multiple_table_multiple_wildcards_query() {
        let expected = Query {
            projection: vec![
                FieldDef {
                    name: "col_b".to_string(),
                    sqltype: SqlType::Text,
                    nullable: true,
                },
                FieldDef {
                    name: "col_a".to_string(),
                    sqltype: SqlType::Int32,
                    nullable: false,
                },
            ],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL); CREATE TABLE t2(col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT t2.*, t1.* FROM t1, t2;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_joined_query() {
        let expected = Query {
            projection: vec![
                FieldDef {
                    name: "col_a".to_string(),
                    sqltype: SqlType::Int32,
                    nullable: false,
                },
                FieldDef {
                    name: "col_b".to_string(),
                    sqltype: SqlType::Text,
                    nullable: true,
                },
            ],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL); CREATE TABLE t2(id INT NOT NULL, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query(
                "SELECT col_a, col_b FROM t1 JOIN t2 ON t1.col_a=t2.id;",
                &schema,
            )
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_compound_field_query() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "col_a".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT t1.col_a FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_compound_field_aliased_query() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "x".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT t1.col_a AS x FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_insert_statement_no_return() {
        let expected = Query { projection: vec![] };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("INSERT INTO t1 VALUES (3);", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_insert_statement_returning() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "col_a".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("INSERT INTO t1 VALUES (3) RETURNING col_a;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_delete_statement_no_return() {
        let expected = Query { projection: vec![] };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("DELETE FROM t1 WHERE col_a < 3;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_delete_statement_returning() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "col_a".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("DELETE FROM t1 WHERE col_a < 3 RETURNING col_a;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_update_statement_no_return() {
        let expected = Query { projection: vec![] };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("UPDATE t1 SET col_a = 3;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_update_statement_returning() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "col_a".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("UPDATE t1 SET col_a = 3 RETURNING col_a;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }
}
