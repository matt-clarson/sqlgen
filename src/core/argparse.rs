use std::{
    iter::{Enumerate, Peekable},
    str::Chars,
};

use super::SqlType;

#[derive(Debug, Eq, PartialEq)]
pub struct Arg {
    sql_type: SqlType,
    ident: String,
    pos: usize,
    len: usize,
}

impl Arg {
    pub fn sql_type(&self) -> SqlType {
        self.sql_type
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

impl<'a> ArgParse<'a> {
    fn arg(&mut self) -> Option<Arg> {
        let pos = self.dollar()?;
        let ident = self.ident()?;
        let sql_type = self.double_colon().and_then(|_| self.sql_type())?;
        let len = self.iter.peek().map(|n| n.0).unwrap_or(self.len) - pos;

        Some(Arg {
            sql_type,
            ident,
            pos,
            len,
        })
    }

    fn sql_type(&mut self) -> Option<SqlType> {
        self.ident().and_then(|ident| match ident.as_str() {
            "tinyint" => Some(SqlType::Int8),
            "smallint" => Some(SqlType::Int16),
            "int" => Some(SqlType::Int32),
            "bigint" => Some(SqlType::Int64),
            "float" => Some(SqlType::Float32),
            "double" => Some(SqlType::Float64),
            "bool" => Some(SqlType::Bool),
            "text" => Some(SqlType::Text),
            "blob" => Some(SqlType::Binary),
            _ => None,
        })
    }

    fn double_colon(&mut self) -> Option<usize> {
        self.colon().and_then(|_| self.colon())
    }

    fn colon(&mut self) -> Option<usize> {
        self.iter.next_if(|n| n.1 == ':').map(|n| n.0)
    }

    fn ident(&mut self) -> Option<String> {
        let mut ident = String::new();
        loop {
            if let Some((_, c)) = self
                .iter
                .next_if(|n| matches!(n.1, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_'))
            {
                ident.push(c);
            } else {
                break;
            }
        }
        if ident.is_empty() {
            None
        } else {
            Some(ident)
        }
    }
    fn dollar(&mut self) -> Option<usize> {
        self.iter.next_if(|n| n.1 == '$').map(|n| n.0)
    }

    fn take_non_dollar(&mut self) {
        while let Some(_) = self.iter.next_if(|n| n.1 != '$') {}
    }
}

impl<'a> Iterator for ArgParse<'a> {
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
            sql_type: SqlType::Int32,
            ident: "x".to_string(),
            pos: 0,
            len: 7,
        }];

        let actual = args("$x::int");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_bool_arg() {
        let expected = vec![Arg {
            sql_type: SqlType::Bool,
            ident: "x".to_string(),
            pos: 0,
            len: 8,
        }];

        let actual = args("$x::bool");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_bigint_arg() {
        let expected = vec![Arg {
            sql_type: SqlType::Int64,
            ident: "x".to_string(),
            pos: 0,
            len: 10,
        }];

        let actual = args("$x::bigint");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_smallint_arg() {
        let expected = vec![Arg {
            sql_type: SqlType::Int16,
            ident: "x".to_string(),
            pos: 0,
            len: 12,
        }];

        let actual = args("$x::smallint");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_tinyint_arg() {
        let expected = vec![Arg {
            sql_type: SqlType::Int8,
            ident: "x".to_string(),
            pos: 0,
            len: 11,
        }];

        let actual = args("$x::tinyint");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_float_arg() {
        let expected = vec![Arg {
            sql_type: SqlType::Float32,
            ident: "x".to_string(),
            pos: 0,
            len: 9,
        }];

        let actual = args("$x::float");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_double_arg() {
        let expected = vec![Arg {
            sql_type: SqlType::Float64,
            ident: "x".to_string(),
            pos: 0,
            len: 10,
        }];

        let actual = args("$x::double");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_text_arg() {
        let expected = vec![Arg {
            sql_type: SqlType::Text,
            ident: "x".to_string(),
            pos: 0,
            len: 8,
        }];

        let actual = args("$x::text");

        assert_eq!(expected, actual);
    }

    #[test]
    fn valid_blob_arg() {
        let expected = vec![Arg {
            sql_type: SqlType::Binary,
            ident: "x".to_string(),
            pos: 0,
            len: 8,
        }];

        let actual = args("$x::blob");

        assert_eq!(expected, actual);
    }

    #[test]
    fn two_args() {
        let expected = vec![
            Arg {
                sql_type: SqlType::Text,
                ident: "x".to_string(),
                pos: 0,
                len: 8,
            },
            Arg {
                sql_type: SqlType::Int32,
                ident: "y".to_string(),
                pos: 9,
                len: 7,
            },
        ];

        let actual = args("$x::text $y::int");

        assert_eq!(expected, actual);
    }
}
