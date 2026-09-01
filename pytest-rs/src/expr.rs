//! Boolean expression evaluation for `-k` and `-m`.
//!
//! pytest compiles these to Python AST and evals them; we parse them once into
//! a tiny tree and evaluate against a matcher closure.  Grammar:
//!
//! ```text
//! expression: expr? EOF
//! expr:       and_expr ('or' and_expr)*
//! and_expr:   not_expr ('and' not_expr)*
//! not_expr:   'not' not_expr | '(' expr ')' | ident
//! ident:      a python identifier, or for -k any run of non-space characters
//! ```
//!
//! Marker expressions additionally support `name(arg=value, ...)` calls, which
//! match against the marker's keyword arguments.

use crate::error::{Error, Result};

#[derive(Debug, Clone)]
pub enum Expr {
    True,
    Ident(String),
    /// `mark(key=value, ...)` — only meaningful for `-m`.
    Call(String, Vec<(String, String)>),
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
}

pub struct Matcher<'a> {
    /// Returns whether a bare name matches.
    pub name: &'a dyn Fn(&str) -> bool,
    /// Returns whether `name(kwargs)` matches; `None` means unsupported.
    pub call: Option<&'a dyn Fn(&str, &[(String, String)]) -> bool>,
}

impl Expr {
    pub fn eval(&self, m: &Matcher<'_>) -> bool {
        match self {
            Expr::True => true,
            Expr::Ident(n) => (m.name)(n),
            Expr::Call(n, kwargs) => match m.call {
                Some(f) => f(n, kwargs),
                None => (m.name)(n),
            },
            Expr::Not(e) => !e.eval(m),
            Expr::And(a, b) => a.eval(m) && b.eval(m),
            Expr::Or(a, b) => a.eval(m) || b.eval(m),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Ident(String),
    And,
    Or,
    Not,
    LParen,
    RParen,
    Comma,
    Eq,
    Str(String),
    End,
}

/// `-k` allows arbitrary substrings (e.g. `test_foo[1-2]`), `-m` only allows
/// identifiers plus call syntax.
#[derive(Clone, Copy, PartialEq)]
pub enum Mode {
    Keyword,
    Mark,
}

struct Lexer {
    toks: Vec<Tok>,
    pos: usize,
}

fn lex(input: &str, mode: Mode) -> Result<Vec<Tok>> {
    let chars: Vec<char> = input.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        match c {
            '(' => {
                out.push(Tok::LParen);
                i += 1;
            }
            ')' => {
                out.push(Tok::RParen);
                i += 1;
            }
            ',' if mode == Mode::Mark => {
                out.push(Tok::Comma);
                i += 1;
            }
            '=' if mode == Mode::Mark => {
                out.push(Tok::Eq);
                i += 1;
            }
            '\'' | '"' if mode == Mode::Mark => {
                let quote = c;
                i += 1;
                let mut s = String::new();
                while i < chars.len() && chars[i] != quote {
                    s.push(chars[i]);
                    i += 1;
                }
                i += 1;
                out.push(Tok::Str(s));
            }
            _ => {
                let start = i;
                while i < chars.len() {
                    let ch = chars[i];
                    if ch.is_whitespace() || ch == '(' || ch == ')' {
                        break;
                    }
                    if mode == Mode::Mark && (ch == ',' || ch == '=') {
                        break;
                    }
                    i += 1;
                }
                let word: String = chars[start..i].iter().collect();
                match word.as_str() {
                    "and" => out.push(Tok::And),
                    "or" => out.push(Tok::Or),
                    "not" => out.push(Tok::Not),
                    _ => out.push(Tok::Ident(word)),
                }
            }
        }
    }
    out.push(Tok::End);
    Ok(out)
}

impl Lexer {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos]
    }
    fn next(&mut self) -> Tok {
        let t = self.toks[self.pos].clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn accept(&mut self, t: &Tok) -> bool {
        if self.peek() == t {
            self.next();
            true
        } else {
            false
        }
    }
}

pub fn parse(input: &str, mode: Mode) -> Result<Expr> {
    let toks = lex(input, mode)?;
    let mut lx = Lexer { toks, pos: 0 };
    if *lx.peek() == Tok::End {
        return Ok(Expr::True);
    }
    let e = parse_or(&mut lx, mode)?;
    if *lx.peek() != Tok::End {
        return Err(Error::usage(format!(
            "wrong expression passed to '-{}': {input}",
            if mode == Mode::Mark { "m" } else { "k" }
        )));
    }
    Ok(e)
}

fn parse_or(lx: &mut Lexer, mode: Mode) -> Result<Expr> {
    let mut left = parse_and(lx, mode)?;
    while lx.accept(&Tok::Or) {
        let right = parse_and(lx, mode)?;
        left = Expr::Or(Box::new(left), Box::new(right));
    }
    Ok(left)
}

fn parse_and(lx: &mut Lexer, mode: Mode) -> Result<Expr> {
    let mut left = parse_not(lx, mode)?;
    while lx.accept(&Tok::And) {
        let right = parse_not(lx, mode)?;
        left = Expr::And(Box::new(left), Box::new(right));
    }
    Ok(left)
}

fn parse_not(lx: &mut Lexer, mode: Mode) -> Result<Expr> {
    if lx.accept(&Tok::Not) {
        return Ok(Expr::Not(Box::new(parse_not(lx, mode)?)));
    }
    if lx.accept(&Tok::LParen) {
        let e = parse_or(lx, mode)?;
        if !lx.accept(&Tok::RParen) {
            return Err(Error::usage("expected ')'"));
        }
        return Ok(e);
    }
    match lx.next() {
        Tok::Ident(name) => {
            if mode == Mode::Mark && *lx.peek() == Tok::LParen {
                lx.next();
                let mut kwargs = Vec::new();
                loop {
                    if lx.accept(&Tok::RParen) {
                        break;
                    }
                    let key = match lx.next() {
                        Tok::Ident(k) => k,
                        other => return Err(Error::usage(format!("expected keyword, got {other:?}"))),
                    };
                    if !lx.accept(&Tok::Eq) {
                        return Err(Error::usage("expected '=' in marker argument"));
                    }
                    let val = match lx.next() {
                        Tok::Str(s) => s,
                        Tok::Ident(s) => s,
                        other => return Err(Error::usage(format!("expected value, got {other:?}"))),
                    };
                    kwargs.push((key, val));
                    if !lx.accept(&Tok::Comma) {
                        if !lx.accept(&Tok::RParen) {
                            return Err(Error::usage("expected ')'"));
                        }
                        break;
                    }
                }
                return Ok(Expr::Call(name, kwargs));
            }
            Ok(Expr::Ident(name))
        }
        other => Err(Error::usage(format!("unexpected token {other:?}"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eval(expr: &str, names: &[&str], mode: Mode) -> bool {
        let e = parse(expr, mode).unwrap();
        let f = |n: &str| names.iter().any(|x| *x == n);
        e.eval(&Matcher { name: &f, call: None })
    }

    #[test]
    fn keyword_expressions() {
        assert!(eval("foo", &["foo"], Mode::Keyword));
        assert!(!eval("not foo", &["foo"], Mode::Keyword));
        assert!(eval("foo or bar", &["bar"], Mode::Keyword));
        assert!(eval("foo and not bar", &["foo"], Mode::Keyword));
        assert!(!eval("foo and not bar", &["foo", "bar"], Mode::Keyword));
        assert!(eval("(a or b) and c", &["b", "c"], Mode::Keyword));
        assert!(eval("", &[], Mode::Keyword));
    }

    #[test]
    fn keyword_allows_brackets_in_ids() {
        // `-k 'test_x[1-2]'` must lex as one identifier.
        let e = parse("test_x[1-2]", Mode::Keyword).unwrap();
        match e {
            Expr::Ident(s) => assert_eq!(s, "test_x[1-2]"),
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn mark_calls() {
        let e = parse("supported(only_if='x')", Mode::Mark).unwrap();
        match e {
            Expr::Call(name, kw) => {
                assert_eq!(name, "supported");
                assert_eq!(kw, vec![("only_if".to_string(), "x".to_string())]);
            }
            other => panic!("{other:?}"),
        }
    }
}
