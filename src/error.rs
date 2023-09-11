use std::io;

#[derive(Debug, Eq, PartialEq)]
pub enum SqlgenBuilderError {
    SchemaFileMissing,
    QueryDirMissing,
    CodeGeneratorMissing,
}
impl std::fmt::Display for SqlgenBuilderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SchemaFileMissing => f.write_str("schema file path not provided"),
            Self::QueryDirMissing => f.write_str("queries dir file path not provided"),
            Self::CodeGeneratorMissing => f.write_str("code generator implementation not provided"),
        }
    }
}
impl std::error::Error for SqlgenBuilderError {}

#[derive(Debug, Eq, PartialEq)]
pub enum SqlgenError {
    EntityNotFound(String),
    EmptyQuery,
    CodegenError(CodegenError),
    QueriesError(FilesError),
    IoError(String),
    Unsupported(String),
    Unknown(String),
}
impl std::fmt::Display for SqlgenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EntityNotFound(msg) => write!(f, "entity not found: {msg}"),
            Self::EmptyQuery => f.write_str("query file has no sql statements"),
            Self::CodegenError(err) => write!(f, "codegen error: {err}"),
            Self::QueriesError(err) => write!(f, "queries error: {err}"),
            Self::IoError(err) => write!(f, "io error: {err}"),
            Self::Unsupported(msg) => write!(f, "unsupported sql: {msg}"),
            Self::Unknown(msg) => write!(f, "unknown error: {msg}"),
        }
    }
}
impl std::error::Error for SqlgenError {}
impl From<Box<dyn std::error::Error>> for SqlgenError {
    fn from(err: Box<dyn std::error::Error>) -> Self {
        Self::Unknown(err.to_string())
    }
}
impl From<CodegenError> for SqlgenError {
    fn from(err: CodegenError) -> Self {
        Self::CodegenError(err)
    }
}
impl From<FilesError> for SqlgenError {
    fn from(err: FilesError) -> Self {
        Self::QueriesError(err)
    }
}
impl From<io::Error> for SqlgenError {
    fn from(err: io::Error) -> Self {
        Self::IoError(err.to_string())
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum CodegenError {
    Unknown(String),
}
impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unknown(msg) => write!(f, "unknown error: {msg}"),
        }
    }
}
impl std::error::Error for CodegenError {}

#[derive(Debug, Eq, PartialEq)]
pub enum FilesError {
    IoError(String),
    PathError(String),
}
impl std::fmt::Display for FilesError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IoError(err) => write!(f, "io error: {err}"),
            Self::PathError(msg) => write!(f, "path error: {msg}"),
        }
    }
}
impl std::error::Error for FilesError {}
impl From<io::Error> for FilesError {
    fn from(err: io::Error) -> Self {
        Self::IoError(err.to_string())
    }
}
impl From<FilesError> for io::Error {
    fn from(value: FilesError) -> Self {
        Self::new(io::ErrorKind::Other, value.to_string())
    }
}
