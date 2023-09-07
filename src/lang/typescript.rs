use crate::{
    core::{NamedQuery, SqlType},
    error::CodegenError,
};

use super::Codegen;

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
        s.push_str(
            "export type Dispatcher<TResult, TArg extends Record<string, unknown> = {}> = TResult extends void ? {\n",
        );
        s.push_str("    (query: string): Promise<void>;\n");
        s.push_str("    (query: string, args: Array<TArg[keyof TArg]>): Promise<void>;\n");
        s.push_str("} : {\n");
        s.push_str("    (query: string): Promise<TResult[]>;\n");
        s.push_str("    (query: string, args: Array<TArg[keyof TArg]>): Promise<TResult[]>;\n");
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
            s.push_str(arg.sql_type().into());
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
            s.push_str(field.sqltype().into());
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
        s.push_str("    dispatch: Dispatcher<");
        if named_query.query().projection().is_empty() {
            s.push_str("void");
        } else {
        s.push_str(result_name.as_str());
        }
        if !named_query.args().is_empty() {
            s.push_str(", ");
            s.push_str(arg_name.as_str());
        }
        s.push_str(">,\n");
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
            s.push_str("    await ");
        } else {
            s.push_str("    return ");
        }
        if named_query.args().is_empty() {
            s.push_str("dispatch(query);\n");
        } else {
            s.push_str("dispatch(query, [\n");
            for arg in named_query.args() {
                s.push_str("        arg.");
                s.push_str(camel_case(arg.ident()).as_str());
                s.push_str(",\n");
            }
            s.push_str("    ]);\n");
        }
        s.push_str("}\n\n");
    }
}

impl From<SqlType> for &'static str {
    fn from(sql_type: SqlType) -> Self {
        match sql_type {
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

/// Converts a string to pascal case. '-', '_', and whitespace characters are removed
/// character directly trailing these is upper-cased. First character is also upper-cased.
/// # Examples
///
/// ```
/// use sqlgen::lang::typescript::pascal_case;
///
/// assert_eq!("HelloWorld".to_string(), pascal_case("hello world"));
///
/// assert_eq!("WithUnderscores".to_string(), pascal_case("with_underscores"));
///
/// assert_eq!("PathLike".to_string(), pascal_case("path-like"));
/// ```
pub fn pascal_case<S: AsRef<str>>(s: S) -> String {
    let mut out = String::new();

    let mut upper_next = true;
    for c in s.as_ref().chars() {
        if matches!(c, '_' | '-' | ' ' | '\t' | '\n' | '\r') {
            upper_next = true;
            continue;
        }
        if upper_next {
            for c1 in c.to_uppercase() {
                out.push(c1);
            }
            upper_next = false;
        } else {
            out.push(c);
        }
    }

    out
}

/// Converts a string to camel case. '-', '_', and whitespace characters are removed, any
/// character directly trailing these is upper-cased.
/// # Examples
///
/// ```
/// use sqlgen::lang::typescript::camel_case;
///
/// assert_eq!("helloWorld".to_string(), camel_case("hello world"));
///
/// assert_eq!("withUnderscores".to_string(), camel_case("with_underscores"));
///
/// assert_eq!("pathLike".to_string(), camel_case("path-like"));
/// ```
pub fn camel_case<S: AsRef<str>>(s: S) -> String {
    let mut out = String::new();

    let mut upper_next = false;
    for c in s.as_ref().chars() {
        if matches!(c, '_' | '-' | ' ' | '\t' | '\n' | '\r') {
            upper_next = true;
            continue;
        }
        if upper_next {
            for c1 in c.to_uppercase() {
                out.push(c1);
            }
            upper_next = false;
        } else {
            out.push(c);
        }
    }

    out
}

/// Takes a string with newlines and indents each line with the same `indent` string.
///
/// # Example
///
/// ```
/// use sqlgen::lang::typescript::indent_lines;
///
/// let indent = "  "; // two spaces
/// assert_eq!(
///     "  hello\n  world\n  :)\n".to_string(),
///     indent_lines("hello\nworld\n:)\n", indent)
/// );
/// ```
pub fn indent_lines<S: AsRef<str>>(s: S, indent: S) -> String {
    let mut out = String::new();

    let mut do_indent = true;
    for c in s.as_ref().chars() {
        if do_indent {
            out.push_str(indent.as_ref());
            do_indent = false;
        }
        out.push(c);
        if c == '\n' {
            do_indent = true;
        }
    }

    out
}
