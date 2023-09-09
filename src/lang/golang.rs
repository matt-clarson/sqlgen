use std::cmp::max;

use crate::core::{NamedQuery, SqlType};

use super::{indent_lines, pascal_case, Codegen};

pub struct GoCodegen {}

impl Codegen for GoCodegen {
    fn codegen(
        &self,
        named_queries: &[crate::core::NamedQuery],
    ) -> Result<String, crate::error::CodegenError> {
        let mut out = String::new();

        self.header_comment(&mut out);
        self.base_types(&mut out);

        for named_query in named_queries {
            if !named_query.args().is_empty() {
                self.arg_type(&mut out, named_query);
            }
            if !named_query.query().projection().is_empty() {
                self.result_type(&mut out, named_query);
            }
            self.function(&mut out, named_query);
        }

        Ok(out)
    }
}

impl GoCodegen {
    fn header_comment(&self, s: &mut String) {
        s.push_str("// ");
        s.push_str(self.header());
        s.push_str("\n\n");
    }

    fn base_types(&self, s: &mut String) {
        s.push_str("package queries\n\n");
        s.push_str("import (\n");
        s.push_str("\t\"context\"\n");
        s.push_str("\t\"database/sql\"\n");
        s.push_str(")\n\n");

        s.push_str("type scannableRow interface {\n");
        s.push_str("\tscanRow(*sql.Rows) error\n");
        s.push_str("}\n\n");

        s.push_str("type resultSet[TResult scannableRow] struct {\n");
        s.push_str("\trows   *sql.Rows\n");
        s.push_str("\tcreate func() TResult\n");
        s.push_str("}\n\n");

        s.push_str("func (r *resultSet[TResult]) toSlice() ([]TResult, error) {\n");
        s.push_str("\tvar results []TResult\n");
        s.push_str("\tfor r.rows.Next() {\n");
        s.push_str("\t\tresult := r.create()\n");
        s.push_str("\t\tif err := result.scanRow(r.rows); err != nil {\n");
        s.push_str("\t\t\treturn nil, err\n");
        s.push_str("\t\t}\n");
        s.push_str("\t\tresults = append(results, result)\n");
        s.push_str("\t}\n\n");
        s.push_str("\tif err := r.rows.Err(); err != nil {\n");
        s.push_str("\t\treturn nil, err\n");
        s.push_str("\t}\n\n");
        s.push_str("\treturn results, nil\n");
        s.push_str("}\n\n");
    }

    fn arg_type(&self, s: &mut String, named_query: &NamedQuery) {
        let mut arg_name = pascal_case(named_query.name());
        arg_name.push_str("Arg");

        s.push_str("type ");
        s.push_str(arg_name.as_str());
        s.push_str(" struct {\n");

        let longest_arg_length = named_query
            .args()
            .iter()
            .fold(0usize, |acc, x| max(acc, pascal_case(x.ident()).len()));

        for arg in named_query.args() {
            s.push('\t');
            let name = pascal_case(arg.ident());
            s.push_str(name.as_str());
            let padding = longest_arg_length - name.len() + 1;
            for _ in 0..padding {
                s.push(' ');
            }
            s.push_str(arg.sql_type().into_strict_str());
            s.push('\n');
        }
        s.push_str("}\n\n");
    }

    fn result_type(&self, s: &mut String, named_query: &NamedQuery) {
        let mut result_name = pascal_case(named_query.name());
        result_name.push_str("Result");

        let longest_field_len = named_query
            .query()
            .projection()
            .iter()
            .fold(0usize, |acc, x| max(acc, pascal_case(x.name()).len()));

        s.push_str("type ");
        s.push_str(result_name.as_str());
        s.push_str(" struct {\n");

        for field in named_query.query().projection() {
            let name = pascal_case(field.name());
            s.push('\t');
            s.push_str(name.as_str());
            let padding = longest_field_len - name.len() + 1;
            for _ in 0..padding {
                s.push(' ');
            }
            if field.nullable() {
                s.push_str(field.sqltype().into_null_str());
            } else {
                s.push_str(field.sqltype().into_strict_str());
            }
            s.push('\n')
        }
        s.push_str("}\n\n");

        s.push_str("func create");
        s.push_str(result_name.as_str());
        s.push_str("() ");
        s.push_str(result_name.as_str());
        s.push_str(" {\n");
        s.push_str("\treturn ");
        s.push_str(result_name.as_str());
        s.push_str("{}\n");
        s.push_str("}\n\n");

        s.push_str("func (r ");
        s.push_str(result_name.as_str());
        s.push_str(") scanRow(rows *sql.Rows) error {\n");
        s.push_str("\treturn rows.Scan(\n");
        for field in named_query.query().projection() {
            s.push_str("\t\t&r.");
            s.push_str(pascal_case(field.name()).as_str());
            s.push_str(",\n");
        }
        s.push_str("\t)\n");
        s.push_str("}\n\n");
    }

    fn function(&self, s: &mut String, named_query: &NamedQuery) {
        let function_name = pascal_case(named_query.name());
        let mut result_name = pascal_case(named_query.name());
        result_name.push_str("Result");
        let mut arg_name = pascal_case(named_query.name());
        arg_name.push_str("Arg");

        s.push_str("func ");
        s.push_str(function_name.as_str());
        s.push_str("(db *sql.DB, ctx context.Context");
        if !named_query.args().is_empty() {
            s.push_str(", arg ");
            s.push_str(arg_name.as_str());
        }
        s.push_str(") ");
        if named_query.query().projection().is_empty() {
            s.push_str("error {\n");
        } else {
            s.push_str("([]");
            s.push_str(result_name.as_str());
            s.push_str(", error) {\n");
        }
        s.push_str("\tquery := `\n");
        s.push_str(indent_lines(named_query.raw(), "        ").as_str());
        s.push('\n');
        s.push_str("    `\n\n");

        if named_query.query().projection().is_empty() {
            if named_query.args().is_empty() {
                s.push_str("\t_, err := db.ExecContext(ctx, query)\n\n");
            } else {
                s.push_str("\t_, err := db.ExecContext(ctx, query,\n");
                for arg in named_query.args() {
                    s.push_str("\t\targ.");
                    s.push_str(pascal_case(arg.ident()).as_str());
                    s.push_str(",\n");
                }
                s.push_str("\t)\n\n");
            }
            s.push_str("\treturn err\n");
        } else {
            if named_query.args().is_empty() {
                s.push_str("\trows, err := db.QueryContext(ctx, query)\n");
            } else {
                s.push_str("\trows, err := db.QueryContext(ctx, query,\n");
                for arg in named_query.args() {
                    s.push_str("\t\targ.");
                    s.push_str(pascal_case(arg.ident()).as_str());
                    s.push_str(",\n")
                }
                s.push_str("\t)\n");
            }
            s.push_str("\tif err != nil {\n");
            s.push_str("\t\treturn nil, err\n");
            s.push_str("\t}\n\n");

            s.push_str("\tresults := resultSet[");
            s.push_str(result_name.as_str());
            s.push_str("]{rows, create");
            s.push_str(result_name.as_str());
            s.push_str("}\n\n");

            s.push_str("\treturn results.toSlice()\n");
        }

        s.push_str("}\n\n");
    }
}

trait StrictSqlTypeExt {
    fn into_strict_str(self) -> &'static str;
}
trait NullableSqlTypeExt {
    fn into_null_str(self) -> &'static str;
}

impl StrictSqlTypeExt for SqlType {
    fn into_strict_str(self) -> &'static str {
        match self {
            SqlType::Bool => "bool",
            SqlType::Int8 => "int8",
            SqlType::Int16 => "int16",
            SqlType::Int32 => "int32",
            SqlType::Int64 => "int64",
            SqlType::Float32 | SqlType::Float64 => "float64",
            SqlType::Text => "string",
            SqlType::Binary => "[]byte",
        }
    }
}

impl NullableSqlTypeExt for SqlType {
    fn into_null_str(self) -> &'static str {
        match self {
            SqlType::Bool => "sql.NullBool",
            SqlType::Int8 => "sql.NullInt8",
            SqlType::Int16 => "sql.NullInt16",
            SqlType::Int32 => "sql.NullInt32",
            SqlType::Int64 => "sql.NullInt64",
            SqlType::Float32 | SqlType::Float64 => "sql.NullFloat64",
            SqlType::Text => "sql.NullString",
            SqlType::Binary => "[]byte",
        }
    }
}
