use std::{cmp::max, ffi::OsStr, path::Path};

use crate::core::{NamedQuery, SqlType};

use super::{indent_lines, pascal_case, Codegen};

pub struct GoCodegen {
    pub package: String,
}

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

impl Default for GoCodegen {
    fn default() -> Self {
        Self {
            package: String::from("queries"),
        }
    }
}

impl From<&Path> for GoCodegen {
    fn from(path: &Path) -> Self {
        if !matches!(path.extension().and_then(OsStr::to_str), Some("go")) {
            return Self::default();
        }

        let package_name = path
            .parent()
            .and_then(Path::file_name)
            .or_else(|| path.file_stem())
            .and_then(OsStr::to_str);

        if let Some(package) = package_name {
            if !package.starts_with(|c: char| c.is_ascii_lowercase()) {
                return Self::default();
            }
            if package
                .chars()
                .any(|c| !matches!(c, 'a'..='z' | '0'..='9' | '_'))
            {
                return Self::default();
            }
            Self {
                package: package.to_string(),
            }
        } else {
            Self::default()
        }
    }
}

impl GoCodegen {
    fn header_comment(&self, s: &mut String) {
        s.push_str("// ");
        s.push_str(self.header());
        s.push_str("\n\n");
    }

    fn base_types(&self, s: &mut String) {
        s.push_str("package ");
        s.push_str(self.package.as_str());
        s.push_str("\n\n");
        s.push_str("import (\n");
        s.push_str("\t\"context\"\n");
        s.push_str("\t\"database/sql\"\n");
        s.push_str(")\n\n");
        s.push_str("type SqlQueryer interface {\n");
        s.push_str(
            "\tQueryContext(ctx context.Context, query string, args ...any) (*sql.Rows, error)\n",
        );
        s.push_str("}\n\n");
        s.push_str("type SqlExecer interface {\n");
        s.push_str(
            "\tExecContext(ctx context.Context, query string, args ...any) (sql.Result, error)\n",
        );
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
            if arg.nullable() {
                s.push_str(arg.sql_type().into_null_str());
            } else {
                s.push_str(arg.sql_type().into_strict_str());
            }
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
    }

    fn function(&self, s: &mut String, named_query: &NamedQuery) {
        let query_has_result = !named_query.query().projection().is_empty();
        let query_has_args = !named_query.args().is_empty();
        let function_name = pascal_case(named_query.name());
        let mut result_name = pascal_case(named_query.name());
        result_name.push_str("Result");
        let mut arg_name = pascal_case(named_query.name());
        arg_name.push_str("Arg");

        s.push_str("func ");
        s.push_str(function_name.as_str());
        if query_has_result {
            s.push_str("(ctx context.Context, db SqlQueryer");
        } else {
            s.push_str("(ctx context.Context, db SqlExecer");
        }
        if query_has_args {
            s.push_str(", arg ");
            s.push_str(arg_name.as_str());
        }
        s.push_str(") ");
        if query_has_result {
            s.push_str("([]");
            s.push_str(result_name.as_str());
            s.push_str(", error) {\n");
        } else {
            s.push_str("error {\n");
        }
        s.push_str("\tquery := `\n");
        s.push_str(indent_lines(named_query.raw(), "        ").as_str());
        s.push('\n');
        s.push_str("    `\n\n");

        if query_has_result {
            if query_has_args {
                s.push_str("\trows, err := db.QueryContext(ctx, query,\n");
                for arg in named_query.args() {
                    s.push_str("\t\targ.");
                    s.push_str(pascal_case(arg.ident()).as_str());
                    s.push_str(",\n")
                }
                s.push_str("\t)\n");
            } else {
                s.push_str("\trows, err := db.QueryContext(ctx, query)\n");
            }
            s.push_str("\tif err != nil {\n");
            s.push_str("\t\treturn nil, err\n");
            s.push_str("\t}\n\n");

            s.push_str("\tvar results []");
            s.push_str(result_name.as_str());
            s.push_str("\n\n");

            s.push_str("\tfor rows.Next() {\n");
            s.push_str("\t\tr := ");
            s.push_str(result_name.as_str());
            s.push_str("{}\n");
            s.push_str("\t\terr := rows.Scan(\n");
            for field in named_query.query().projection() {
                s.push_str("\t\t\t&r.");
                s.push_str(pascal_case(field.name()).as_str());
                s.push_str(",\n");
            }
            s.push_str("\t\t)\n");
            s.push_str("\t\tif err != nil {\n");
            s.push_str("\t\t\treturn nil, err\n");
            s.push_str("\t\t}\n");
            s.push_str("\t\tresults = append(results, r)\n");
            s.push_str("\t}\n\n");

            s.push_str("\treturn results, rows.Err()\n");
        } else {
            if query_has_args {
                s.push_str("\t_, err := db.ExecContext(ctx, query,\n");
                for arg in named_query.args() {
                    s.push_str("\t\targ.");
                    s.push_str(pascal_case(arg.ident()).as_str());
                    s.push_str(",\n");
                }
                s.push_str("\t)\n\n");
            } else {
                s.push_str("\t_, err := db.ExecContext(ctx, query)\n\n");
            }
            s.push_str("\treturn err\n");
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
