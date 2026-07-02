//! A minimal S-expression reader for the `.prog` artifact format.
//!
//! The surface is tiny by design (see `Freigen/Ast/Sexp.lean` for the emitter): lists and bare
//! atoms (keywords, variables, names, decimal numbers).  Double-quoted strings are also read, but
//! the format currently emits none — they are reserved for guest-language string literals.
//! Whitespace — including the emitter's cosmetic indentation — is insignificant.

use std::fmt;

/// One S-expression node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sexp {
    /// A bare token: a keyword (`block`), a variable (`v3`), a name (`double`, `assert`) or a
    /// decimal number (`42`).
    Atom(String),
    /// A double-quoted string literal — reserved for guest-language strings; the format
    /// currently emits none.
    Str(String),
    /// A parenthesized list.
    List(Vec<Sexp>),
}

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexp::Atom(a) => write!(f, "{a}"),
            Sexp::Str(s) => write!(f, "\"{s}\""),
            Sexp::List(items) => {
                write!(f, "(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{item}")?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A reader error, with a byte offset into the source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SexpError {
    pub offset: usize,
    pub message: String,
}

impl fmt::Display for SexpError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "sexp error at byte {}: {}", self.offset, self.message)
    }
}

impl std::error::Error for SexpError {}

struct Reader<'a> {
    src: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn err<T>(&self, message: impl Into<String>) -> Result<T, SexpError> {
        Err(SexpError { offset: self.pos, message: message.into() })
    }

    fn skip_ws(&mut self) {
        while let Some(&c) = self.src.get(self.pos) {
            if c.is_ascii_whitespace() {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn read(&mut self) -> Result<Sexp, SexpError> {
        self.skip_ws();
        match self.src.get(self.pos) {
            None => self.err("unexpected end of input"),
            Some(b'(') => {
                self.pos += 1;
                let mut items = Vec::new();
                loop {
                    self.skip_ws();
                    match self.src.get(self.pos) {
                        None => return self.err("unclosed list"),
                        Some(b')') => {
                            self.pos += 1;
                            return Ok(Sexp::List(items));
                        }
                        Some(_) => items.push(self.read()?),
                    }
                }
            }
            Some(b')') => self.err("unexpected `)`"),
            Some(b'"') => {
                self.pos += 1;
                let start = self.pos;
                while let Some(&c) = self.src.get(self.pos) {
                    if c == b'"' {
                        let s = std::str::from_utf8(&self.src[start..self.pos])
                            .map_err(|_| SexpError {
                                offset: start,
                                message: "invalid utf-8 in string".into(),
                            })?
                            .to_owned();
                        self.pos += 1;
                        return Ok(Sexp::Str(s));
                    }
                    self.pos += 1;
                }
                self.err("unclosed string")
            }
            Some(_) => {
                let start = self.pos;
                while let Some(&c) = self.src.get(self.pos) {
                    if c.is_ascii_whitespace() || c == b'(' || c == b')' || c == b'"' {
                        break;
                    }
                    self.pos += 1;
                }
                let s = std::str::from_utf8(&self.src[start..self.pos]).map_err(|_| SexpError {
                    offset: start,
                    message: "invalid utf-8 in atom".into(),
                })?;
                Ok(Sexp::Atom(s.to_owned()))
            }
        }
    }
}

/// Read exactly one S-expression, requiring the rest of the input to be whitespace.
pub fn parse_sexp(src: &str) -> Result<Sexp, SexpError> {
    let mut r = Reader { src: src.as_bytes(), pos: 0 };
    let e = r.read()?;
    r.skip_ws();
    if r.pos != r.src.len() {
        return r.err("trailing input after S-expression");
    }
    Ok(e)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atoms_strings_lists() {
        assert_eq!(parse_sexp("foo").unwrap(), Sexp::Atom("foo".into()));
        assert_eq!(parse_sexp("  \"a b\"  ").unwrap(), Sexp::Str("a b".into()));
        assert_eq!(
            parse_sexp("(a (b 12) \"c\")").unwrap(),
            Sexp::List(vec![
                Sexp::Atom("a".into()),
                Sexp::List(vec![Sexp::Atom("b".into()), Sexp::Atom("12".into())]),
                Sexp::Str("c".into()),
            ])
        );
    }

    #[test]
    fn errors() {
        assert!(parse_sexp("(a").is_err());
        assert!(parse_sexp("a)").is_err());
        assert!(parse_sexp("\"a").is_err());
        assert!(parse_sexp("").is_err());
    }
}
