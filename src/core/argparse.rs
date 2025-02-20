use std::{
    iter::{Enumerate, Peekable},
    str::Chars,
};

use super::SqlType;

#[derive(Debug, Eq, PartialEq)]
pub struct Arg {
    arg_type: Option<ArgType>,
    ident: String,
    pos: usize,
    len: usize,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ArgType {
    Nullable(SqlType),
    NonNullable(SqlType),
}

impl Arg {
    pub fn arg_type(&self) -> Option<ArgType> {
        self.arg_type
    }

    pub fn ident(&self) -> &str {
        self.ident.as_ref()
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

pub fn args<S: AsRef<str>>(s: S) -> Vec<Arg> {
    ArgParse::from(s.as_ref()).collect()
}

struct ArgParse<'a> {
    len: usize,
    iter: Peekable<Enumerate<Chars<'a>>>,
}

impl ArgParse<'_> {
    fn arg(&mut self) -> Option<Arg> {
        let pos = self.dollar()?;
        let ident = self.ident()?;
        let arg_type = self.double_colon().and_then(|_| {
            self.question_mark()
                .and_then(|_| self.sql_type().map(ArgType::Nullable))
                .or_else(|| self.sql_type().map(ArgType::NonNullable))
        });
        let len = self.iter.peek().map(|n| n.0).unwrap_or(self.len) - pos;

        Some(Arg {
            arg_type,
            ident,
            pos,
            len,
        })
    }

    fn sql_type(&mut self) -> Option<SqlType> {
        self.ident().and_then(|ident| match ident.as_str() {
            "tinyint" => self
                .array_notation()
                .and(Some(SqlType::Int8Array))
                .or(Some(SqlType::Int8)),
            "smallint" => self
                .array_notation()
                .and(Some(SqlType::Int16Array))
                .or(Some(SqlType::Int16)),
            "int" => self
                .array_notation()
                .and(Some(SqlType::Int32Array))
                .or(Some(SqlType::Int32)),
            "bigint" => self
                .array_notation()
                .and(Some(SqlType::Int64Array))
                .or(Some(SqlType::Int64)),
            "float" => self
                .array_notation()
                .and(Some(SqlType::Float32Array))
                .or(Some(SqlType::Float32)),
            "double" => self
                .array_notation()
                .and(Some(SqlType::Float64Array))
                .or(Some(SqlType::Float64)),
            "bool" => self
                .array_notation()
                .and(Some(SqlType::BoolArray))
                .or(Some(SqlType::Bool)),
            "text" => self
                .array_notation()
                .and(Some(SqlType::TextArray))
                .or(Some(SqlType::Text)),
            "blob" => Some(SqlType::Binary),
            "datetime" => Some(SqlType::DateTime),
            _ => None,
        })
    }

    fn question_mark(&mut self) -> Option<usize> {
        self.iter.next_if(|n| n.1 == '?').map(|n| n.0)
    }

    fn double_colon(&mut self) -> Option<usize> {
        self.colon().and_then(|_| self.colon())
    }

    fn colon(&mut self) -> Option<usize> {
        self.iter.next_if(|n| n.1 == ':').map(|n| n.0)
    }

    fn ident(&mut self) -> Option<String> {
        let mut ident = String::new();
        while let Some((_, c)) = self
            .iter
            .next_if(|n| matches!(n.1, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_'))
        {
            ident.push(c);
        }
        if ident.is_empty() {
            None
        } else {
            Some(ident)
        }
    }

    fn array_notation(&mut self) -> Option<usize> {
        self.open_bracket().and(self.close_bracket())
    }

    fn open_bracket(&mut self) -> Option<usize> {
        self.iter.next_if(|n| n.1 == '[').map(|n| n.0)
    }

    fn close_bracket(&mut self) -> Option<usize> {
        self.iter.next_if(|n| n.1 == ']').map(|n| n.0)
    }

    fn dollar(&mut self) -> Option<usize> {
        self.iter.next_if(|n| n.1 == '$').map(|n| n.0)
    }

    fn take_non_dollar(&mut self) {
        while self.iter.next_if(|n| n.1 != '$').is_some() {}
    }
}

impl Iterator for ArgParse<'_> {
    type Item = Arg;
    fn next(&mut self) -> Option<Self::Item> {
        self.take_non_dollar();
        self.arg()
    }
}

impl<'a> From<&'a str> for ArgParse<'a> {
    fn from(value: &'a str) -> Self {
        Self {
            len: value.len(),
            iter: value.chars().enumerate().peekable(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn empty_string() {
        let expected: Vec<Arg> = vec![];

        let actual = args("");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_int_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Int32)),
            ident: "x".to_string(),
            pos: 0,
            len: 7,
        }];

        let actual = args("$x::int");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_int_array_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Int32Array)),
            ident: "x".to_string(),
            pos: 0,
            len: 9,
        }];

        let actual = args("$x::int[]");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_bool_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Bool)),
            ident: "x".to_string(),
            pos: 0,
            len: 8,
        }];

        let actual = args("$x::bool");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_bool_array_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::BoolArray)),
            ident: "x".to_string(),
            pos: 0,
            len: 10,
        }];

        let actual = args("$x::bool[]");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_bigint_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Int64)),
            ident: "x".to_string(),
            pos: 0,
            len: 10,
        }];

        let actual = args("$x::bigint");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_bigint_array_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Int64Array)),
            ident: "x".to_string(),
            pos: 0,
            len: 12,
        }];

        let actual = args("$x::bigint[]");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_smallint_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Int16)),
            ident: "x".to_string(),
            pos: 0,
            len: 12,
        }];

        let actual = args("$x::smallint");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_smallint_array_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Int16Array)),
            ident: "x".to_string(),
            pos: 0,
            len: 14,
        }];

        let actual = args("$x::smallint[]");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_tinyint_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Int8)),
            ident: "x".to_string(),
            pos: 0,
            len: 11,
        }];

        let actual = args("$x::tinyint");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_tinyint_array_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Int8Array)),
            ident: "x".to_string(),
            pos: 0,
            len: 13,
        }];

        let actual = args("$x::tinyint[]");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_float_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Float32)),
            ident: "x".to_string(),
            pos: 0,
            len: 9,
        }];

        let actual = args("$x::float");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_float_array_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Float32Array)),
            ident: "x".to_string(),
            pos: 0,
            len: 11,
        }];

        let actual = args("$x::float[]");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_double_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Float64)),
            ident: "x".to_string(),
            pos: 0,
            len: 10,
        }];

        let actual = args("$x::double");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_double_array_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Float64Array)),
            ident: "x".to_string(),
            pos: 0,
            len: 12,
        }];

        let actual = args("$x::double[]");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_text_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Text)),
            ident: "x".to_string(),
            pos: 0,
            len: 8,
        }];

        let actual = args("$x::text");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_text_array_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::TextArray)),
            ident: "x".to_string(),
            pos: 0,
            len: 10,
        }];

        let actual = args("$x::text[]");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_blob_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::Binary)),
            ident: "x".to_string(),
            pos: 0,
            len: 8,
        }];

        let actual = args("$x::blob");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_datetime_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::NonNullable(SqlType::DateTime)),
            ident: "x".to_string(),
            pos: 0,
            len: 12,
        }];

        let actual = args("$x::datetime");

        assert_eq!(expected, actual);
    }

    #[test]
    fn two_args() {
        let expected = vec![
            Arg {
                arg_type: Some(ArgType::NonNullable(SqlType::Text)),
                ident: "x".to_string(),
                pos: 0,
                len: 8,
            },
            Arg {
                arg_type: Some(ArgType::NonNullable(SqlType::Int32)),
                ident: "y".to_string(),
                pos: 9,
                len: 7,
            },
        ];

        let actual = args("$x::text $y::int");

        assert_eq!(expected, actual);
    }

    #[test]
    fn nullable_arg() {
        let expected = vec![Arg {
            arg_type: Some(ArgType::Nullable(SqlType::Text)),
            ident: "x".to_string(),
            pos: 0,
            len: 9,
        }];

        let actual = args("$x::?text");

        assert_eq!(expected, actual);
    }

    #[test]
    fn untyped_arg() {
        let expected = vec![Arg {
            arg_type: None,
            ident: "x".to_string(),
            pos: 0,
            len: 2,
        }];

        let actual = args("$x;");

        assert_eq!(expected, actual);
    }
}
