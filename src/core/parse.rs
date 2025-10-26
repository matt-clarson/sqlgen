use std::{borrow::Borrow, collections::HashMap, fmt::Display};

use indexmap::IndexMap;
use sqlparser::{ast, dialect, parser::Parser};
use uuid::Uuid;

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
                ast::Statement::CreateTable { name, columns, .. } => {
                    let table_name = name.0.last().unwrap().to_string();
                    let mut table = Table::new(table_name.clone());
                    for coldef in &columns {
                        let field: FieldDef = coldef.try_into()?;
                        table.insert_field(field.name.clone(), field);
                    }
                    schema.tables.insert(table_name, table);
                }
                ast::Statement::AlterTable {
                    name,
                    operation: ast::AlterTableOperation::AddColumn { column_def, .. },
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
                ast::Statement::AlterTable {
                    name,
                    operation:
                        ast::AlterTableOperation::RenameColumn {
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
                ast::Statement::AlterTable {
                    name,
                    operation: ast::AlterTableOperation::DropColumn { column_name, .. },
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
            ast::Statement::Insert {
                returning: None, ..
            } => Ok(out_query),
            ast::Statement::Insert {
                table_name,
                returning: Some(projection),
                ..
            } => {
                let mut query_tables = QueryTables::new(schema);
                self.try_store_named_query_table(&mut query_tables, table_name)?;
                for field in SqliteFieldIter::new(&query_tables, projection) {
                    out_query.projection.push(field?);
                }
                Ok(out_query)
            }
            ast::Statement::Update {
                returning: None, ..
            } => Ok(out_query),
            ast::Statement::Update {
                table,
                returning: Some(projection),
                ..
            } => {
                let mut query_tables = QueryTables::new(schema);
                for join in &table.joins {
                    self.try_store_query_table_factor(&mut query_tables, &join.relation)?;
                }
                self.try_store_query_table_factor(&mut query_tables, &table.relation)?;

                for field in SqliteFieldIter::new(&query_tables, projection) {
                    out_query.projection.push(field?);
                }
                Ok(out_query)
            }
            ast::Statement::Delete {
                returning: None, ..
            } => Ok(out_query),
            ast::Statement::Delete {
                from,
                returning: Some(projection),
                ..
            } => {
                let mut query_tables = QueryTables::new(schema);
                for table_with_joins in from {
                    for join in &table_with_joins.joins {
                        self.try_store_query_table_factor(&mut query_tables, &join.relation)?;
                    }
                    self.try_store_query_table_factor(
                        &mut query_tables,
                        &table_with_joins.relation,
                    )?;
                }

                for field in SqliteFieldIter::new(&query_tables, projection) {
                    out_query.projection.push(field?);
                }

                Ok(out_query)
            }
            ast::Statement::Query(query) => {
                let query_tables = QueryTables::new(schema);
                self.parse_select_query(query.as_ref(), &query_tables)
            }
            _ => Err(SqlgenError::Unsupported(
                "only SELECT, UPDATE, INSERT, and DELETE  statements are supported in queries"
                    .to_string(),
            )),
        }
    }

    fn try_store_named_query_table(
        &self,
        query_tables: &mut QueryTables,
        name: &ast::ObjectName,
    ) -> Result<(), SqlgenError> {
        let table_name = name.0.last().unwrap().to_string();
        if let Some(table) = query_tables.find_table_in_schema(name.to_string()) {
            query_tables.insert_table(table_name, table.clone());
            Ok(())
        } else {
            Err(SqlgenError::EntityNotFound(format!(
                "table {name} does not exist in known schema"
            )))
        }
    }

    fn try_store_query_table_factor(
        &self,
        query_tables: &mut QueryTables,
        table_factor: &ast::TableFactor,
    ) -> Result<(), SqlgenError> {
        match table_factor {
            ast::TableFactor::Table { name, alias, .. } => {
                let table_name = alias
                    .as_ref()
                    .map(|a| a.name.to_string())
                    .unwrap_or_else(|| name.0.last().unwrap().to_string());
                if let Some(table) = query_tables.find_table_in_schema(name.to_string()) {
                    query_tables.insert_table(table_name, table.clone());
                    Ok(())
                } else {
                    Err(SqlgenError::EntityNotFound(format!(
                        "table {name} does not exist in known schema"
                    )))
                }
            }
            ast::TableFactor::Derived {
                subquery, alias, ..
            } => {
                let table_name = alias
                    .as_ref()
                    .map(|a| a.name.to_string())
                    .unwrap_or_else(|| Uuid::new_v4().to_string());

                let subquery_out = self.parse_select_query(subquery, query_tables)?;
                query_tables.insert_table_from_query(&table_name, &subquery_out);
                Ok(())
            }
            _ => Err(SqlgenError::Unsupported(
                "only named table expressions and subqueries are supported in FROM clauses"
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

    fn parse_select_query(
        &self,
        query: &ast::Query,
        in_scope_tables: &QueryTables,
    ) -> Result<Query, SqlgenError> {
        let mut out_query = Query { projection: vec![] };
        let mut query_tables = in_scope_tables.clone();

        if let Some(with_clause) = &query.with {
            for cte in &with_clause.cte_tables {
                let cte_out = self.parse_select_query(&cte.query, &query_tables)?;
                query_tables.insert_temp_from_query(&cte.alias, &cte_out);
            }
        }

        match query.body.as_ref() {
            ast::SetExpr::Select(select) => {
                for table_with_joins in &select.from {
                    for join in &table_with_joins.joins {
                        self.try_store_query_table_factor(&mut query_tables, &join.relation)?;
                    }
                    self.try_store_query_table_factor(
                        &mut query_tables,
                        &table_with_joins.relation,
                    )?;
                }

                for field in SqliteFieldIter::new(&query_tables, &select.projection) {
                    out_query.projection.push(field?);
                }

                Ok(out_query)
            }
            _ => Err(SqlgenError::Unsupported(
                "only SELECT, UPDATE, INSERT, and DELETE statements are supported in queries"
                    .to_string(),
            )),
        }
    }
}

struct SqliteFieldIter<'a> {
    query_tables: &'a QueryTables<'a>,
    select_items: Box<dyn Iterator<Item = &'a ast::SelectItem> + 'a>,
    current: Option<Box<dyn Iterator<Item = FieldDef> + 'a>>,
}

impl<'a> Iterator for SqliteFieldIter<'a> {
    type Item = Result<FieldDef, SqlgenError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.current
            .as_mut()
            .and_then(|iter| Ok(iter.next()).transpose())
            .or_else(|| {
                self.select_items.next().and_then(|item| {
                    self.get_fields_for_select_item(item)
                        .map(|mut next_iter| {
                            let next = next_iter.next();
                            self.current = Some(next_iter);
                            next
                        })
                        .transpose()
                })
            })
    }
}

impl<'a> SqliteFieldIter<'a> {
    fn new(query_tables: &'a QueryTables, select_items: &'a [ast::SelectItem]) -> Self {
        Self {
            current: None,
            query_tables,
            select_items: Box::new(select_items.iter()),
        }
    }

    fn get_fields_for_select_item(
        &self,
        select_item: &ast::SelectItem,
    ) -> Result<Box<dyn Iterator<Item = FieldDef> + 'a>, SqlgenError> {
        match select_item {
            ast::SelectItem::Wildcard(_) => {
                let iter = self.query_tables.all_table_fields().into_iter().cloned();
                Ok(Box::new(iter))
            }
            ast::SelectItem::QualifiedWildcard(table_name, _) => {
                let name = table_name.to_string();
                if let Some(table) = self.query_tables.find_table(&name) {
                    let iter = table.get_sorted_fields().into_iter().cloned();
                    Ok(Box::new(iter))
                } else {
                    Err(SqlgenError::EntityNotFound(name))
                }
            }
            ast::SelectItem::UnnamedExpr(expr) => self.expr_to_field_def(expr).map(|field| {
                let iter: Box<dyn Iterator<Item = FieldDef> + 'a> =
                    Box::new(Singleton::from(field));
                iter
            }),
            ast::SelectItem::ExprWithAlias { expr, alias } => {
                self.expr_to_field_def(expr).map(|field| {
                    let iter: Box<dyn Iterator<Item = FieldDef> + 'a> =
                        Box::new(Singleton::from(field.clone_with_alias(alias)));
                    iter
                })
            }
        }
    }

    fn expr_to_field_def(&self, expr: &ast::Expr) -> Result<FieldDef, SqlgenError> {
        match expr {
            ast::Expr::Identifier(ident) => self
                .query_tables
                .find_field(&ident.value).cloned()
                .ok_or_else(|| SqlgenError::EntityNotFound(ident.to_string())),
            ast::Expr::CompoundIdentifier(idents) => self
                .query_tables
                .find_qualified_field(idents).cloned()
                .ok_or_else(|| SqlgenError::EntityNotFound(compound_name(idents))),
            ast::Expr::Function(func) => self.builtin_func_to_field(func),
            _ => Err(SqlgenError::Unsupported(format!(
                "expression unsupported {}",
                expr
            ))),
        }
    }

    fn builtin_func_to_field(&self, func: &ast::Function) -> Result<FieldDef, SqlgenError> {
        let name = func.name.to_string();
        match name.to_lowercase().as_str() {
            "avg" | "round" => self.infer_null_func_eager(name, func, SqlType::Float64),
            "lower" | "ltrim" | "replace" | "rtrim" | "upper" => {
                self.infer_null_func_unary(name, func, SqlType::Text)
            }
            "changes" | "count" | "last_insert_rowid" | "random" | "total_changes" => {
                Ok(FieldDef {
                    name,
                    sqltype: SqlType::Int32,
                    nullable: false,
                })
            }
            "char" | "concat" | "concat_ws" | "format" | "group_concat" | "hex" | "printf"
            | "quote" | "typeof" => Ok(FieldDef {
                name,
                sqltype: SqlType::Text,
                nullable: false,
            }),
            "glob" => self.infer_null_func_greedy(name, func, SqlType::Bool),
            "instr" => self.infer_null_func_greedy(name, func, SqlType::Int32),
            "length" | "octet_length" => self.infer_null_func_unary(name, func, SqlType::Int32),
            "sign" => self.infer_sqlite_sign_func(name, func),
            "unicode" => Ok(FieldDef {
                name,
                sqltype: SqlType::Int32,
                nullable: true,
            }),
            "randomblob" | "zeroblob" => Ok(FieldDef {
                name,
                sqltype: SqlType::Binary,
                nullable: false,
            }),
            "total" => Ok(FieldDef {
                name,
                sqltype: SqlType::Float64,
                nullable: false,
            }),
            "unhex" => Ok(FieldDef {
                name,
                sqltype: SqlType::Binary,
                nullable: true,
            }),
            "coalesce" | "ifnull" | "max" | "min" | "nullif" => {
                self.no_map_func_eager(name, func, 0)
            }
            "iif" => self.no_map_func_eager(name, func, 1),
            "abs" | "sum" => self.infer_sqlite_numeric_func(name, func),
            "substr" => self.nullable_text_binary_func(name, func),
            "date" | "time" | "datetime" => {
                self.infer_sqlite_date_func(name, func, SqlType::Text, 0)
            }
            "julianday" => self.infer_sqlite_date_func(name, func, SqlType::Float64, 0),
            "unixepoch" => self.infer_sqlite_date_func(name, func, SqlType::Int32, 0),
            "strftime" => self.infer_sqlite_date_func(name, func, SqlType::Text, 1),
            "timediff" => self.infer_null_func_greedy(name, func, SqlType::Text),
            _ => Err(SqlgenError::Unsupported(format!(
                "function {} is not supported",
                func.name
            ))),
        }
    }

    fn infer_sqlite_date_func(
        &self,
        name: String,
        func: &ast::Function,
        sqltype: SqlType,
        first_arg_pos: usize,
    ) -> Result<FieldDef, SqlgenError> {
        match func.args.get(first_arg_pos) {
            Some(arg) => self.function_arg_to_field_def(arg).map(|field| FieldDef {
                name,
                sqltype,
                nullable: field.nullable,
            }),
            None => Ok(FieldDef {
                name,
                sqltype,
                nullable: false,
            }),
        }
    }

    fn infer_null_func_unary(
        &self,
        name: String,
        func: &ast::Function,
        sqltype: SqlType,
    ) -> Result<FieldDef, SqlgenError> {
        match func.args.first() {
            Some(arg) => self.function_arg_to_field_def(arg).map(|field| FieldDef {
                name,
                sqltype,
                nullable: field.nullable,
            }),
            None => Err(SqlgenError::Unknown(format!(
                "{name} function called with invalid args - expected a single column identifier"
            ))),
        }
    }

    fn infer_null_func_eager(
        &self,
        name: String,
        func: &ast::Function,
        sqltype: SqlType,
    ) -> Result<FieldDef, SqlgenError> {
        self.no_map_func_eager(name, func, 0).map(|field| FieldDef {
            name: field.name,
            sqltype,
            nullable: field.nullable,
        })
    }

    fn infer_null_func_greedy(
        &self,
        name: String,
        func: &ast::Function,
        sqltype: SqlType,
    ) -> Result<FieldDef, SqlgenError> {
        self.no_map_func_greedy(name, func, 0)
            .map(|field| FieldDef {
                name: field.name,
                sqltype,
                nullable: field.nullable,
            })
    }

    fn infer_sqlite_sign_func(
        &self,
        name: String,
        func: &ast::Function,
    ) -> Result<FieldDef, SqlgenError> {
        self.no_map_func_eager(name, func, 0)
            .map(|field| match field.sqltype {
                SqlType::Int8
                | SqlType::Int16
                | SqlType::Int32
                | SqlType::Int64
                | SqlType::Float32
                | SqlType::Float64
                | SqlType::Bool => FieldDef {
                    name: field.name,
                    sqltype: SqlType::Int32,
                    nullable: field.nullable,
                },
                _ => FieldDef {
                    name: field.name,
                    sqltype: SqlType::Int32,
                    nullable: true,
                },
            })
    }

    fn no_map_func_eager(
        &self,
        name: String,
        func: &ast::Function,
        num_to_skip: usize,
    ) -> Result<FieldDef, SqlgenError> {
        let folded = func
            .args
            .iter()
            .skip(num_to_skip)
            .fold(None, |acc, arg| match acc {
                Some(Ok(
                    prev_field @ FieldDef {
                        nullable: false, ..
                    },
                )) => Some(Ok(prev_field)),
                Some(Ok(_)) | None => Some(self.function_arg_to_field_def(arg)),
                Some(err) => Some(err),
            });

        match folded {
            Some(result) => result.map(|field| field.clone_with_alias(name)),
            None => Err(SqlgenError::Unknown(format!(
                "{name} function called with invalid args - expected a single column identifier"
            ))),
        }
    }

    fn no_map_func_greedy(
        &self,
        name: String,
        func: &ast::Function,
        num_to_skip: usize,
    ) -> Result<FieldDef, SqlgenError> {
        let folded = func
            .args
            .iter()
            .skip(num_to_skip)
            .fold(None, |acc, arg| match acc {
                Some(Ok(prev_field @ FieldDef { nullable: true, .. })) => Some(Ok(prev_field)),
                Some(Ok(_)) | None => Some(self.function_arg_to_field_def(arg)),
                Some(err) => Some(err),
            });

        match folded {
            Some(result) => result.map(|field| field.clone_with_alias(name)),
            None => Err(SqlgenError::Unknown(format!(
                "{name} function called with invalid args - expected a single column identifier"
            ))),
        }
    }

    fn infer_sqlite_numeric_func(
        &self,
        name: String,
        func: &ast::Function,
    ) -> Result<FieldDef, SqlgenError> {
        self.no_map_func_eager(name, func, 0)
            .map(|field| match field.sqltype {
                SqlType::Int8
                | SqlType::Int16
                | SqlType::Int32
                | SqlType::Int64
                | SqlType::Bool => FieldDef {
                    name: field.name,
                    sqltype: SqlType::Int32,
                    nullable: field.nullable,
                },
                _ => FieldDef {
                    name: field.name,
                    sqltype: SqlType::Float64,
                    nullable: field.nullable,
                },
            })
    }

    fn nullable_text_binary_func(
        &self,
        name: String,
        func: &ast::Function,
    ) -> Result<FieldDef, SqlgenError> {
        match func.args.first() {
            Some(arg) => match self.function_arg_to_field_def(arg) {
                Ok(
                    field @ FieldDef {
                        sqltype: SqlType::Binary,
                        ..
                    },
                ) => Ok(FieldDef {
                    name,
                    sqltype: field.sqltype,
                    nullable: field.nullable,
                }),
                Ok(field) => Ok(FieldDef {
                    name,
                    sqltype: SqlType::Text,
                    nullable: field.nullable,
                }),
                Err(err) => Err(err),
            },
            None => Err(SqlgenError::Unknown(format!(
                "{name} function called with invalid args - expected a single column identifier"
            ))),
        }
    }

    fn function_arg_to_field_def(&self, arg: &ast::FunctionArg) -> Result<FieldDef, SqlgenError> {
        match arg {
            ast::FunctionArg::Named {
                arg: ast::FunctionArgExpr::Expr(expr),
                ..
            } => self.expr_to_field_def(expr),
            ast::FunctionArg::Unnamed(ast::FunctionArgExpr::Expr(expr)) => {
                self.expr_to_field_def(expr)
            }
            _ => Err(SqlgenError::Unsupported(
                "wildcard expressions as function args aren't supported".to_string(),
            )),
        }
    }
}

impl TryFrom<&ast::ColumnDef> for FieldDef {
    type Error = SqlgenError;

    fn try_from(coldef: &ast::ColumnDef) -> Result<Self, Self::Error> {
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

impl TryFrom<&ast::DataType> for SqlType {
    type Error = SqlgenError;

    fn try_from(value: &ast::DataType) -> Result<Self, Self::Error> {
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

#[derive(Clone, Debug)]
struct QueryTables<'a> {
    schema: &'a Schema,
    temp_schema: IndexMap<String, Table>,
    tables: IndexMap<String, Table>,
}

impl<'a> QueryTables<'a> {
    fn new(schema: &'a Schema) -> Self {
        Self {
            schema,
            temp_schema: IndexMap::new(),
            tables: IndexMap::new(),
        }
    }

    fn insert_temp_from_query<S: Display>(&mut self, name: S, out_query: &Query) {
        let mut table = Table {
            name: name.to_string(),
            fields: IndexMap::with_capacity(out_query.projection().len()),
        };
        for field in out_query.projection() {
            table.insert_field(field.name.clone(), field.clone());
        }
        self.temp_schema.insert(name.to_string(), table);
    }

    fn insert_table<S: Into<String>>(&mut self, name: S, table: Table) {
        self.tables.insert(name.into(), table);
    }

    fn insert_table_from_query<S: Display>(&mut self, name: S, query: &Query) {
        let mut table = Table {
            name: name.to_string(),
            fields: IndexMap::with_capacity(query.projection().len()),
        };
        for field in query.projection() {
            table.insert_field(field.name.clone(), field.clone());
        }
        self.tables.insert(name.to_string(), table);
    }

    fn find_table_in_schema<S: AsRef<str>>(&self, table_name: S) -> Option<&Table> {
        self.schema
            .get_table(table_name.as_ref())
            .or_else(|| self.temp_schema.get(table_name.as_ref()))
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
            .parse_query("SELECT avg(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_agg_func_avg_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "avg".to_string(),
                sqltype: SqlType::Float64,
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
            .parse_query("SELECT avg(col_a) FROM t1;", &schema)
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
            .parse_query("SELECT avg(col_a) AS some_name FROM t1;", &schema)
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
                nullable: true,
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
    fn parse_sqlite_agg_func_max_int_not_null() {
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

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL);")
            .unwrap();
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
                nullable: true,
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
                nullable: true,
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
    fn parse_sqlite_agg_func_min_int_not_null() {
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

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL);")
            .unwrap();
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
                nullable: true,
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
                nullable: true,
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
    fn parse_sqlite_agg_func_sum_int_nullable() {
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
    fn parse_sqlite_agg_func_sum_int_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "sum".to_string(),
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
    fn parse_sqlite_agg_func_sum_text_nullable() {
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
    fn parse_sqlite_agg_func_sum_text_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "sum".to_string(),
                sqltype: SqlType::Float64,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL);")
            .unwrap();
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

    #[test]
    fn parse_sqlite_scalar_func_abs_int_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "abs".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT abs(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_abs_int_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "abs".to_string(),
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
            .parse_query("SELECT abs(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_abs_float() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "abs".to_string(),
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
            .parse_query("SELECT abs(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_abs_text_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "abs".to_string(),
                sqltype: SqlType::Float64,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT abs(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_abs_text_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "abs".to_string(),
                sqltype: SqlType::Float64,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT abs(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_changes() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "changes".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser.parse_query("SELECT changes();", &schema).unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_char() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "char".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT, col_b INT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT char(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_coalesce_int() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "coalesce".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT, col_b INT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT coalesce(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_coalesce_int_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "coalesce".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL, col_b INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT coalesce(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_coalesce_int_mixed_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "coalesce".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT, col_b INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT coalesce(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_coalesce_float() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "coalesce".to_string(),
                sqltype: SqlType::Float64,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a FLOAT, col_b FLOAT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT coalesce(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_coalesce_text() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "coalesce".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT coalesce(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_concat() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "concat".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT concat(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_concat_ws() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "concat_ws".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT concat_ws(', ', col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_format() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "format".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT format('%d) %s', col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_glob() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "glob".to_string(),
                sqltype: SqlType::Bool,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT glob(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_glob_left_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "glob".to_string(),
                sqltype: SqlType::Bool,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT glob(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_glob_right_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "glob".to_string(),
                sqltype: SqlType::Bool,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT glob(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_glob_both_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "glob".to_string(),
                sqltype: SqlType::Bool,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL, col_b TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT glob(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_hex() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "hex".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a BLOB);").unwrap();
        let actual = parser
            .parse_query("SELECT hex(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_ifnull_int() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "ifnull".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT, col_b INT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT ifnull(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_ifnull_int_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "ifnull".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL, col_b INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT ifnull(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_ifnull_float() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "ifnull".to_string(),
                sqltype: SqlType::Float64,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a FLOAT, col_b FLOAT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT ifnull(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_ifnull_text() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "ifnull".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT ifnull(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_iif_int() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "iif".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT, col_b INT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT iif(true, col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_iif_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "iif".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL, col_b INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT iif(true, col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_iif_float() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "iif".to_string(),
                sqltype: SqlType::Float64,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a FLOAT, col_b FLOAT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT iif(false, col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_iif_text() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "iif".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT iif(1 > 2, col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_instr() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "instr".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT instr(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_instr_left_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "instr".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT instr(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_instr_right_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "instr".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT instr(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_instr_both_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "instr".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL, col_b TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT instr(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_last_insert_rowid() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "last_insert_rowid".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT last_insert_rowid();", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_length() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "length".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT length(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_lower() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "lower".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT lower(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_lower_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "lower".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT lower(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_ltrim() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "ltrim".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT ltrim(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_nullif_int() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "nullif".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT, col_b INT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT nullif(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_nullif_int_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "nullif".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT NOT NULL, col_b INT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT nullif(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_nullif_float() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "nullif".to_string(),
                sqltype: SqlType::Float64,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a FLOAT, col_b FLOAT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT nullif( col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_nullif_text() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "nullif".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT nullif(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_octet_length() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "octet_length".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT octet_length(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_printf() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "printf".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT printf('%d) %s', col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_quote() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "quote".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a INT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT quote('%d) %s', col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_random() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "random".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser.parse_query("SELECT random();", &schema).unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_randomblob() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "randomblob".to_string(),
                sqltype: SqlType::Binary,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT randomblob(64);", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_replace() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "replace".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT replace(col_a, 'a', 'b') FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_round() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "round".to_string(),
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
            .parse_query("SELECT round(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_rtrim() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "rtrim".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT rtrim(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_sign_int() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "sign".to_string(),
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
            .parse_query("SELECT sign(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_sign_int_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "sign".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT sign(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_sign_text() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "sign".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT sign(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_substr_text_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "substr".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT substr(col_a, 10) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_substr_text_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "substr".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT substr(col_a, 10) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_substr_binary() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "substr".to_string(),
                sqltype: SqlType::Binary,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a BLOB);").unwrap();
        let actual = parser
            .parse_query("SELECT substr(col_a, 10) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_substr_int() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "substr".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT substr(col_a, 10) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_total_changes() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "total_changes".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT total_changes();", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_typeof() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "typeof".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT typeof(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_unhex() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "unhex".to_string(),
                sqltype: SqlType::Binary,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT unhex(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_unicode() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "unicode".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT unicode(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_upper() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "upper".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a TEXT);").unwrap();
        let actual = parser
            .parse_query("SELECT upper(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_scalar_func_zeroblob() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "zeroblob".to_string(),
                sqltype: SqlType::Binary,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser.parse_query("SELECT zeroblob(64);", &schema).unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_date_func_no_args() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "date".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser.parse_query("SELECT date();", &schema).unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_date_func_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "date".to_string(),
                sqltype: SqlType::Text,
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
            .parse_query("SELECT date(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_date_func_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "date".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT date(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_time_func_no_args() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "time".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser.parse_query("SELECT time();", &schema).unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_time_func_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "time".to_string(),
                sqltype: SqlType::Text,
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
            .parse_query("SELECT time(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_time_func_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "time".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT time(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_datetime_func_no_args() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "datetime".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser.parse_query("SELECT datetime();", &schema).unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_datetime_func_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "datetime".to_string(),
                sqltype: SqlType::Text,
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
            .parse_query("SELECT datetime(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_datetime_func_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "datetime".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT datetime(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_julianday_func_no_args() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "julianday".to_string(),
                sqltype: SqlType::Float64,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser.parse_query("SELECT julianday();", &schema).unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_julianday_func_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "julianday".to_string(),
                sqltype: SqlType::Float64,
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
            .parse_query("SELECT julianday(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_julianday_func_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "julianday".to_string(),
                sqltype: SqlType::Float64,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT julianday(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_unixepoch_func_no_args() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "unixepoch".to_string(),
                sqltype: SqlType::Int32,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser.parse_query("SELECT unixepoch();", &schema).unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_unixepoch_func_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "unixepoch".to_string(),
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
            .parse_query("SELECT unixepoch(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_unixepoch_func_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "unixepoch".to_string(),
                sqltype: SqlType::Int32,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT unixepoch(col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_strftime_func_no_args() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "strftime".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT strftime('%Y-%m-%d');", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_strftime_func_not_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "strftime".to_string(),
                sqltype: SqlType::Text,
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
            .parse_query("SELECT strftime('%Y-%m-%d', col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_strftime_func_nullable() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "strftime".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser.parse_schema("CREATE TABLE t1(col_a INT);").unwrap();
        let actual = parser
            .parse_query("SELECT strftime('%Y-%m-%d', col_a) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_func_timediff() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "timediff".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT timediff(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_func_timediff_left_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "timediff".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL, col_b TEXT);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT timediff(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_func_timediff_right_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "timediff".to_string(),
                sqltype: SqlType::Text,
                nullable: true,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT, col_b TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT timediff(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_sqlite_func_timediff_both_not_null() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "timediff".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL, col_b TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT timediff(col_a, col_b) FROM t1;", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_select_with_cte() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "field".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query(
                "WITH cte AS (SELECT col_a field FROM t1) SELECT * FROM cte;",
                &schema,
            )
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_select_with_subquery() {
        let expected = Query {
            projection: vec![FieldDef {
                name: "field".to_string(),
                sqltype: SqlType::Text,
                nullable: false,
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query("SELECT * FROM (SELECT col_a field FROM t1);", &schema)
            .unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_select_with_subquery_prevent_invalid_scope_access() {
        let expected =
            SqlgenError::EntityNotFound("table sq does not exist in known schema".to_string());

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let schema = parser
            .parse_schema("CREATE TABLE t1(col_a TEXT NOT NULL);")
            .unwrap();
        let actual = parser
            .parse_query(
                "SELECT * FROM (SELECT col_a field FROM t1) as sq, (SELECT * FROM sq);",
                &schema,
            )
            .unwrap_err();

        assert_eq!(expected, actual);
    }
}
