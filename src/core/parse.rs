use std::{borrow::Borrow, collections::HashMap, fmt::Display};

use indexmap::IndexMap;
use sqlparser::{
    ast::{
        self, AlterTableOperation, ColumnDef, DataType, Expr, Function, FunctionArg,
        FunctionArgExpr, ObjectName, SelectItem, SetExpr, Statement, TableFactor,
    },
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
    tables: HashMap<String, Table>,
}

impl Schema {
    pub fn get_table<S: AsRef<str>>(&self, name: S) -> Option<&Table> {
        self.tables
            .values()
            .find(|&table| table.name.as_str() == name.as_ref())
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Table {
    name: String,
    fields: IndexMap<String, FieldDef>,
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
            fields: IndexMap::new(),
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

    pub fn rename_field<S: AsRef<str>, D: Display>(
        &mut self,
        old_name: S,
        new_name: D,
    ) -> Option<FieldDef> {
        let field = self.fields.get(old_name.as_ref())?;
        let renamed = field.clone_with_alias(&new_name);
        self.fields.insert(new_name.to_string(), renamed);
        self.fields.swap_remove(old_name.as_ref())
    }

    pub fn delete_field<S: AsRef<str>>(&mut self, name: S) -> Option<FieldDef> {
        self.fields.shift_remove(name.as_ref())
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

        let mut schema = Schema {
            tables: HashMap::new(),
        };

        for stmt in statements {
            match stmt {
                Statement::CreateTable { name, columns, .. } => {
                    let table_name = name.0.last().unwrap().to_string();
                    let mut table = Table::new(table_name.clone());
                    for coldef in &columns {
                        let field: FieldDef = coldef.try_into()?;
                        table.insert_field(field.name.clone(), field);
                    }
                    schema.tables.insert(table_name, table);
                }
                Statement::AlterTable {
                    name,
                    operation: AlterTableOperation::AddColumn { column_def, .. },
                } => {
                    let table_name = name.0.last().unwrap().to_string();
                    if let Some(table) = schema.tables.get_mut(&table_name) {
                        let new_field = FieldDef::try_from(&column_def)?;
                        table.insert_field(new_field.name().to_string(), new_field)
                    } else {
                        return Err(SqlgenError::EntityNotFound(format!(
                            "can't find definition for table {table_name}"
                        )));
                    }
                }
                Statement::AlterTable {
                    name,
                    operation:
                        AlterTableOperation::RenameColumn {
                            old_column_name,
                            new_column_name,
                        },
                } => {
                    let table_name = name.0.last().unwrap().to_string();
                    if let Some(table) = schema.tables.get_mut(&table_name) {
                        if table
                            .rename_field(old_column_name.to_string(), new_column_name)
                            .is_none()
                        {
                            return Err(SqlgenError::EntityNotFound(format!(
                                "can't find column to rename {old_column_name}"
                            )));
                        }
                    } else {
                        return Err(SqlgenError::EntityNotFound(format!(
                            "can't find definition for table {table_name}"
                        )));
                    }
                }
                Statement::AlterTable {
                    name,
                    operation: AlterTableOperation::DropColumn { column_name, .. },
                } => {
                    let table_name = name.0.last().unwrap().to_string();
                    if let Some(table) = schema.tables.get_mut(&table_name) {
                        if table.delete_field(column_name.to_string()).is_none() {
                            return Err(SqlgenError::EntityNotFound(format!(
                                "can't find column to remove {column_name}"
                            )));
                        }
                    } else {
                        return Err(SqlgenError::EntityNotFound(format!(
                            "can't find definition for table {table_name}"
                        )));
                    }
                }
                _ => {}
            };
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
}

impl TryFrom<&ColumnDef> for FieldDef {
    type Error = SqlgenError;

    fn try_from(coldef: &ColumnDef) -> Result<Self, Self::Error> {
        let field_name = coldef.name.to_string();
        let sqltype = SqlType::try_from(&coldef.data_type)?;
        let not_null = coldef.options.iter().any(|opt| {
            matches!(
                opt.option,
                ast::ColumnOption::NotNull | ast::ColumnOption::Unique { is_primary: true }
            )
        });
        Ok(FieldDef {
            name: field_name.clone(),
            sqltype,
            nullable: !not_null,
        })
    }
}

impl TryFrom<&DataType> for SqlType {
    type Error = SqlgenError;

    fn try_from(value: &DataType) -> Result<Self, Self::Error> {
        match value {
            ast::DataType::Bool | ast::DataType::Boolean => Ok(SqlType::Bool),
            ast::DataType::TinyInt(_) => Ok(SqlType::Int8),
            ast::DataType::SmallInt(_) | ast::DataType::Int2(_) => Ok(SqlType::Int16),
            ast::DataType::Int4(_)
            | ast::DataType::Integer(_)
            | ast::DataType::MediumInt(_)
            | ast::DataType::Int(_) => Ok(SqlType::Int32),
            ast::DataType::BigInt(_) | ast::DataType::Int8(_) => Ok(SqlType::Int64),
            ast::DataType::Text => Ok(SqlType::Text),
            ast::DataType::Real | ast::DataType::Float4 => Ok(SqlType::Float32),
            ast::DataType::Float(_)
            | ast::DataType::Float8
            | ast::DataType::Double
            | ast::DataType::DoublePrecision => Ok(SqlType::Float64),
            ast::DataType::Blob(_) => Ok(SqlType::Binary),
            data_type => Err(SqlgenError::Unsupported(format!(
                "data type {data_type} is not supported"
            ))),
        }
    }
}

struct QueryTables<'a> {
    schema: &'a Schema,
    tables: IndexMap<String, Table>,
}

impl<'a> QueryTables<'a> {
    fn new(schema: &'a Schema) -> Self {
        Self {
            schema,
            tables: IndexMap::new(),
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
            SelectItem::UnnamedExpr(Expr::Function(func)) => {
                if let Some(field) = self.builtin_func_to_field(func) {
                    Ok(Box::new(Singleton::from(field?)))
                } else {
                    Err(SqlgenError::Unsupported(format!(
                        "function {} is not supported",
                        func.name
                    )))
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
            SelectItem::ExprWithAlias {
                expr: Expr::Function(func),
                alias,
            } => {
                if let Some(field) = self.builtin_func_to_field(func) {
                    Ok(Box::new(Singleton::from(field?.clone_with_alias(alias))))
                } else {
                    Err(SqlgenError::Unsupported(format!(
                        "function {} is not supported",
                        func.name
                    )))
                }
            }
            c => Err(SqlgenError::Unsupported(format!(
                "got unsupported select projection: {c:?}",
            ))),
        }
    }

    fn builtin_func_to_field(&self, func: &Function) -> Option<Result<FieldDef, SqlgenError>> {
        let name = func.name.to_string();
        match name.to_lowercase().as_str() {
            "avg" => Some(Ok(FieldDef {
                name,
                sqltype: SqlType::Float64,
                nullable: true,
            })),
            "count" => Some(Ok(FieldDef {
                name,
                sqltype: SqlType::Int32,
                nullable: false,
            })),
            "group_concat" => Some(Ok(FieldDef {
                name,
                sqltype: SqlType::Text,
                nullable: false,
            })),
            "total" => Some(Ok(FieldDef {
                name,
                sqltype: SqlType::Float64,
                nullable: false,
            })),
            "max" | "min" => match func.args.first() {
                Some(FunctionArg::Unnamed(FunctionArgExpr::Expr(Expr::Identifier(ident)))) => {
                    if let Some(field) = self.find_field(&ident.value) {
                        Some(Ok(FieldDef {
                            name,
                            sqltype: field.sqltype(),
                            nullable: false,
                        }))
                    } else {
                        Some(Err(SqlgenError::EntityNotFound(ident.to_string())))
                    }
                }
                Some(FunctionArg::Unnamed(FunctionArgExpr::Expr(Expr::CompoundIdentifier(
                    idents,
                )))) => {
                    if let Some(field) = self.find_qualified_field(idents) {
                        Some(Ok(FieldDef {
                            name,
                            sqltype: field.sqltype(),
                            nullable: false,
                        }))
                    } else {
                        Some(Err(SqlgenError::EntityNotFound(compound_name(idents))))
                    }
                }
                _ => Some(Err(SqlgenError::Unknown(
                    format!("{name} function called with invalid args - expected a single column identifier"),
                ))),
            },
            "sum" => match func.args.first() {
                Some(FunctionArg::Unnamed(FunctionArgExpr::Expr(Expr::Identifier(ident)))) => {
                    if let Some(field) = self.find_field(&ident.value) {
                        Some(Ok(FieldDef {
                            name,
                            sqltype: match field.sqltype() {
                                SqlType::Int8 | SqlType::Int16 | SqlType::Int32 | SqlType::Int64 => field.sqltype(),
                                _ => SqlType::Float64
                            },
                            nullable: true,
                        }))
                    } else {
                        Some(Err(SqlgenError::EntityNotFound(ident.to_string())))
                    }
                }
                Some(FunctionArg::Unnamed(FunctionArgExpr::Expr(Expr::CompoundIdentifier(
                    idents,
                )))) => {
                    if let Some(field) = self.find_qualified_field(idents) {
                        Some(Ok(FieldDef {
                            name,
                            sqltype: match field.sqltype() {
                                SqlType::Int8 | SqlType::Int16 | SqlType::Int32 | SqlType::Int64 => field.sqltype(),
                                _ => SqlType::Float64
                            },
                            nullable: true,
                        }))
                    } else {
                        Some(Err(SqlgenError::EntityNotFound(compound_name(idents))))
                    }
                }
                _ => Some(Err(SqlgenError::Unknown(
                    format!("{name} function called with invalid args - expected a single column identifier"),
                ))),
            },
            _ => None,
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
            tables: HashMap::from([(
                "empty".to_string(),
                Table {
                    name: "empty".to_string(),
                    fields: IndexMap::new(),
                },
            )]),
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
                    tables: HashMap::from([(
                        "t1".to_string(),
                        Table {
                            name: "t1".to_string(),
                            fields: IndexMap::from([(
                                "col".to_string(),
                                FieldDef {
                                    name: "col".to_string(),
                                    sqltype: $sql_type,
                                    nullable: true,
                                },
                            )]),
                        },
                    )]),
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
            tables: HashMap::from([(
                "t1".to_string(),
                Table {
                    name: "t1".to_string(),
                    fields: IndexMap::from([(
                        "col".to_string(),
                        FieldDef {
                            name: "col".to_string(),
                            sqltype: SqlType::Int32,
                            nullable: false,
                        },
                    )]),
                },
            )]),
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
    fn parse_alter_table_add_column() {
        let expected = Schema {
            tables: HashMap::from([(
                "t1".to_string(),
                Table {
                    name: "t1".to_string(),
                    fields: IndexMap::from([
                        (
                            "col".to_string(),
                            FieldDef {
                                name: "col".to_string(),
                                sqltype: SqlType::Int32,
                                nullable: false,
                            },
                        ),
                        (
                            "new_col".to_string(),
                            FieldDef {
                                name: "new_col".to_string(),
                                sqltype: SqlType::Float64,
                                nullable: true,
                            },
                        ),
                    ]),
                },
            )]),
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let actual = parser
            .parse_schema(
                r#"
                CREATE TABLE t1(col INT PRIMARY KEY);
                ALTER TABLE t1
                ADD COLUMN new_col DOUBLE;
            "#,
            )
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_alter_table_rename_column() {
        let expected = Schema {
            tables: HashMap::from([(
                "t1".to_string(),
                Table {
                    name: "t1".to_string(),
                    fields: IndexMap::from([
                        (
                            "renamed".to_string(),
                            FieldDef {
                                name: "renamed".to_string(),
                                sqltype: SqlType::Int32,
                                nullable: false,
                            },
                        ),
                        (
                            "other".to_string(),
                            FieldDef {
                                name: "other".to_string(),
                                sqltype: SqlType::Text,
                                nullable: true,
                            },
                        ),
                    ]),
                },
            )]),
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let actual = parser
            .parse_schema(
                r#"
                CREATE TABLE t1(col INT PRIMARY KEY, other TEXT);
                ALTER TABLE t1
                RENAME COLUMN col TO renamed;
            "#,
            )
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_alter_table_drop_column() {
        let expected = Schema {
            tables: HashMap::from([(
                "t1".to_string(),
                Table {
                    name: "t1".to_string(),
                    fields: IndexMap::from([(
                        "col".to_string(),
                        FieldDef {
                            name: "col".to_string(),
                            sqltype: SqlType::Int32,
                            nullable: false,
                        },
                    )]),
                },
            )]),
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let actual = parser
            .parse_schema(
                r#"
                CREATE TABLE t1(col INT PRIMARY KEY, other TEXT);
                ALTER TABLE t1
                DROP COLUMN other;
            "#,
            )
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

    #[test]
    fn parse_sqlite_agg_func_avg() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "avg".to_string(),
                sqltype: SqlType::Float64,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT avg(a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_avg_aliased() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "some_name".to_string(),
                sqltype: SqlType::Float64,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT avg(a) AS some_name FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_count() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "count".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT count(a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_group_concat() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "group_concat".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT group_concat(a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_max_int() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "max".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT max(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_max_text() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "max".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT max(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_max_compound() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "max".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT max(t1.col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_min_int() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "min".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT min(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_min_text() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "min".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT min(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_min_compound() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "min".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT min(t1.col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_sum_int() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "sum".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT sum(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_sum_float() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "sum".to_string(),
                sqltype: SqlType::Float64,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a FLOAT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT sum(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_sum_text() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "sum".to_string(),
                sqltype: SqlType::Float64,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT sum(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_total_int() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "total".to_string(),
                sqltype: SqlType::Float64,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT total(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_total_float() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "total".to_string(),
                sqltype: SqlType::Float64,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a FLOAT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT total(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_total_text() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "total".to_string(),
                sqltype: SqlType::Float64,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT total(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }
}
