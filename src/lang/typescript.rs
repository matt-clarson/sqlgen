use crate::{
    core::{NamedQuery, SqlType},
    error::CodegenError,
};

use super::{Codegen, camel_case, indent_lines, pascal_case};

pub struct TSCodegen {}

impl Codegen for TSCodegen {
    fn codegen(&self, named_queries: &[NamedQuery]) -> Result<String, CodegenError> {
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

impl TSCodegen {
    fn header_comment(&self, s: &mut String) {
        s.push_str("/*\n");
        s.push_str(" * ");
        s.push_str(self.header());
        s.push('\n');
        s.push_str(" */\n\n");
    }

    fn base_types(&self, s: &mut String) {
        s.push_str("export interface Dispatcher {\n");
        s.push_str("    (query: string, args?: unknown[]): Promise<{\n");
        s.push_str("        keys: string[];\n");
        s.push_str("        rows: unknown[][];\n");
        s.push_str("    }>;\n");
        s.push_str("}\n\n");

        s.push_str("function mapRows<TResult>(keys: string[], rows: unknown[][]): TResult[] {\n");
        s.push_str("    const out = Array(rows.length)\n");
        s.push_str("    for (let i = 0; i < out.length; i++) {\n");
        s.push_str("        const row = rows[i];\n");
        s.push_str("        out[i] = Object.fromEntries(pairs(keys, row));\n");
        s.push_str("    }\n");
        s.push_str("    return out as TResult[];\n");
        s.push_str("}\n\n");

        s.push_str("function pairs<T, U>(xs: T[], ys: U[]): [T, U][] {\n");
        s.push_str("    const out = Array(xs.length)\n");
        s.push_str("    for (let i = 0; i < out.length; i++) {\n");
        s.push_str("        out[i] = [xs[i], ys[i]];\n");
        s.push_str("    }\n");
        s.push_str("    return out;\n");
        s.push_str("}\n\n");
    }

    fn arg_type(&self, s: &mut String, named_query: &NamedQuery) {
        let mut arg_name = pascal_case(named_query.name());
        arg_name.push_str("Arg");

        s.push_str("export type ");
        s.push_str(arg_name.as_str());
        s.push_str(" = {\n");

        for arg in named_query.args() {
            s.push_str("    ");
            s.push_str(camel_case(arg.ident()).as_str());
            s.push_str(": ");
            s.push_str(arg.sql_type().into_str());
            s.push_str(";\n");
        }
        s.push_str("};\n\n");
    }

    fn result_type(&self, s: &mut String, named_query: &NamedQuery) {
        let mut result_name = pascal_case(named_query.name());
        result_name.push_str("Result");

        s.push_str("export type ");
        s.push_str(result_name.as_str());
        s.push_str(" = {\n");

        for field in named_query.query().projection() {
            s.push_str("    ");
            s.push_str(camel_case(field.name()).as_str());
            s.push_str(": ");
            s.push_str(field.sqltype().into_str());
            if field.nullable() {
                s.push_str(" | null");
            }
            s.push_str(";\n");
        }
        s.push_str("};\n\n");
    }

    fn function(&self, s: &mut String, named_query: &NamedQuery) {
        let function_name = camel_case(named_query.name());
        let mut result_name = pascal_case(named_query.name());
        result_name.push_str("Result");
        let mut arg_name = pascal_case(named_query.name());
        arg_name.push_str("Arg");

        s.push_str("export async function ");
        s.push_str(function_name.as_str());
        s.push_str("(\n");
        s.push_str("    dispatch: Dispatcher,\n");
        if !named_query.args().is_empty() {
            s.push_str("    arg: ");
            s.push_str(arg_name.as_str());
            s.push_str(",\n");
        }
        s.push_str("): Promise<");
        if named_query.query().projection().is_empty() {
            s.push_str("void");
        } else {
            s.push_str(result_name.as_str());
            s.push_str("[]");
        }
        s.push_str("> {\n");

        s.push_str("    const query = `\n");
        s.push_str(indent_lines(named_query.raw(), "        ").as_str());
        s.push('\n');
        s.push_str("    `;\n\n");
        if named_query.query().projection().is_empty() {
            if named_query.args().is_empty() {
                s.push_str("    await dispatch(query);\n");
            } else {
                s.push_str("    await dispatch(query, [\n");
                for arg in named_query.args() {
                    s.push_str("        arg.");
                    s.push_str(camel_case(arg.ident()).as_str());
                    s.push_str(",\n");
                }
                s.push_str("    ]);\n");
            }
        } else {
            if named_query.args().is_empty() {
                s.push_str("    const result = await dispatch(query);\n");
            } else {
                s.push_str("    const result = await dispatch(query, [\n");
                for arg in named_query.args() {
                    s.push_str("        arg.");
                    s.push_str(camel_case(arg.ident()).as_str());
                    s.push_str(",\n");
                }
                s.push_str("    ]);\n")
            }
            s.push_str("    return mapRows<");
            s.push_str(result_name.as_str());
            s.push_str(">(result.keys, result.rows);\n");
        }
        s.push_str("}\n\n");
    }
}

trait SqlTypeExt {
    fn into_str(self) -> &'static str;
}

impl SqlTypeExt for SqlType {
    fn into_str(self) -> &'static str {
        match self {
            SqlType::Bool => "boolean",
            SqlType::Int8
            | SqlType::Int16
            | SqlType::Int32
            | SqlType::Int64
            | SqlType::Float32
            | SqlType::Float64 => "number",
            SqlType::Text => "string",
            SqlType::Binary => "ArrayBuffer",
        }
    }
}

