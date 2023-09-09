use crate::{core::NamedQuery, error::CodegenError};

pub mod golang;
pub mod typescript;

pub trait Codegen {
    fn codegen(&self, queries: &[NamedQuery]) -> Result<String, CodegenError>;

    fn header(&self) -> &'static str {
        "File generated by sqlgen. Do not edit."
    }
}

/// Converts a string to pascal case. '-', '_', and whitespace characters are removed
/// character directly trailing these is upper-cased. First character is also upper-cased.
/// # Examples
///
/// ```
/// use sqlgen::lang::pascal_case;
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
/// use sqlgen::lang::camel_case;
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
/// use sqlgen::lang::indent_lines;
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
