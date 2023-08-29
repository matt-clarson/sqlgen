use std::{borrow::Borrow, collections::HashMap};

use sqlparser::{
    ast::{self, SelectItem, SetExpr, Statement},
    dialect,
    parser::Parser,
};

use crate::error::SqlgenError;

impl From<&super::SqlDialect> for Parser<'_> {
    fn from(dialect: &super::SqlDialect) -> Self {
        match dialect {
            super::SqlDialect::Sqlite => Parser::new(&dialect::SQLiteDialect {}),
        }
    }
}

pub struct NamedQuery {
    name: String,
    query: Query,
    raw: String,
}

impl NamedQuery {
    pub fn name(&self) -> &str {
        self.name.as_ref()
    }

    pub fn query(&self) -> &Query {
        &self.query
    }

    pub fn raw(&self) -> &str {
        self.raw.as_ref()
    }
}

#[derive(Debug, PartialEq)]
pub struct Schema {
    tables: Vec<Table>,
}

impl Schema {
    pub fn get_table<S: AsRef<str>>(&self, name: S) -> Option<&Table> {
        self.tables.iter().find(|&table| table.name.as_str() == name.as_ref())
    }
}

#[derive(Debug, PartialEq)]
pub struct Table {
    name: String,
    fields: HashMap<String, FieldDef>,
}

impl Table {
    pub fn get_sorted_fields(&self) -> Vec<&FieldDef> {
        let mut fields: Vec<&FieldDef> = self.fields.values().collect();
        fields.sort_unstable_by(|a, b| a.partial_cmp(b).unwrap());
        fields
    }
}

#[derive(Debug, PartialEq)]
pub struct Query {
    projection: Vec<FieldDef>,
}

impl Query {
    pub fn into_named<S: Into<String>>(self, name: S, raw: S) -> NamedQuery {
        NamedQuery {
            name: name.into(),
            query: self,
            raw: raw.into(),
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
    pub fn clone_with_alias<S: Into<String>>(&self, alias: S) -> Self {
        Self {
            name: alias.into(),
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

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum SqlType {
    Int32,
    Text,
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
            sqlparser::ast::Statement::Query(query) => {
                if query.with.is_some() {
                    return Err(SqlgenError::Unsupported("CTEs are not supported".to_string()));
                }
                return match query.body.as_ref() {
                    SetExpr::Select(select) => {
                        let mut query_tables = HashMap::new();
                        for table_with_joins in &select.from {
                            if !table_with_joins.joins.is_empty() {
                                return Err(SqlgenError::Unsupported("queries with joins are not supported".to_string()));
                            }
                            match &table_with_joins.relation {
                                sqlparser::ast::TableFactor::Table { name, alias, .. } => {
                                    let table_name = alias
                                        .as_ref()
                                        .map(|a| a.name.to_string())
                                        .unwrap_or_else(|| name.0.last().unwrap().to_string());
                                    if let Some(table) = schema.get_table(&table_name) {
                                        query_tables.insert(table_name, table);
                                        Ok(())
                                    } else {
                                        return Err(SqlgenError::EntityNotFound(format!(
                                            "table {name} does not exist in known schema"
                                        )));
                                    }
                                }
                                _ => Err(SqlgenError::Unsupported("only named table expressions are supported in FROM clauses".to_string())),
                            }?;
                        }

                        for select_item in &select.projection {
                            match select_item {
                                SelectItem::Wildcard(_) => {
                                    for table in query_tables.values() {
                                        for field in table.get_sorted_fields() {
                                            out_query.projection.push(field.clone())
                                        }
                                    }
                                    Ok(())
                                }
                                _ => Err(SqlgenError::Unsupported("only wildcard projections are supported".to_string())),
                            }?;
                        }

                        return Ok(out_query);
                    }
                    _ => Err(SqlgenError::Unsupported("only SELECT statements are supported in queries".to_string())),
                };
            }
            _ => Err(SqlgenError::Unsupported("only SELECT statements are supported in queries".to_string())),
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
                let mut fields = HashMap::new();
                for coldef in columns {
                    let field_name = coldef.name.to_string();
                    let sqltype = match &coldef.data_type {
                        ast::DataType::Int(_) => SqlType::Int32,
                        ast::DataType::Text => SqlType::Text,
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
                    fields.insert(field_name, field);
                }
                let table = Table {
                    name: table_name,
                    fields,
                };
                Ok(Some(table))
            }
            _ => Ok(None),
        }
    }
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
                fields: HashMap::new(),
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let actual = parser.parse_schema("CREATE TABLE empty();").unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_table_with_int_column() {
        let expected = Schema {
            tables: vec![Table {
                name: "t1".to_string(),
                fields: HashMap::from([(
                    "col".to_string(),
                    FieldDef {
                        name: "col".to_string(),
                        sqltype: SqlType::Int32,
                        nullable: true,
                    },
                )]),
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let actual = parser.parse_schema("CREATE TABLE t1(col INT);").unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_table_with_text_column() {
        let expected = Schema {
            tables: vec![Table {
                name: "t1".to_string(),
                fields: HashMap::from([(
                    "col".to_string(),
                    FieldDef {
                        name: "col".to_string(),
                        sqltype: SqlType::Text,
                        nullable: true,
                    },
                )]),
            }],
        };

        let parser = Sqlparser {
            dialect: SqlDialect::Sqlite,
        };

        let actual = parser.parse_schema("CREATE TABLE t1(col TEXT);").unwrap();

        assert_eq!(expected, actual);
    }

    #[test]
    fn parse_table_primary_key() {
        let expected = Schema {
            tables: vec![Table {
                name: "t1".to_string(),
                fields: HashMap::from([(
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
                    name: "col_a".to_string(),
                    sqltype: SqlType::Text,
                    nullable: true,
                },
                FieldDef {
                    name: "id".to_string(),
                    sqltype: SqlType::Int32,
                    nullable: false,
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
}
