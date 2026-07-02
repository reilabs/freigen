//! Parse the uniform `.prog` S-expression format into the typed AST.
//!
//! The grammar is pinned in `Freigen/Ast/Sexp.lean` (the emitter); this module is its inverse.
//! Numeric literals are parsed *type-directed* from the binder annotation (`nat`, `(zmod p)`,
//! `(fin n)`), so a parsed [`Value`] is always fully typed — a field element knows its modulus.

use std::fmt;

use num_bigint::BigUint;

use crate::ast::*;
use crate::sexp::{parse_sexp, Sexp, SexpError};
use crate::value::Value;

/// A parse error: either malformed S-expression syntax or a well-formed S-expression that does
/// not match the `.prog` grammar.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseError {
    Sexp(SexpError),
    Grammar(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Sexp(e) => write!(f, "{e}"),
            ParseError::Grammar(m) => write!(f, "grammar error: {m}"),
        }
    }
}

impl std::error::Error for ParseError {}

impl From<SexpError> for ParseError {
    fn from(e: SexpError) -> Self {
        ParseError::Sexp(e)
    }
}

type Result<T> = std::result::Result<T, ParseError>;

fn err<T>(msg: impl Into<String>) -> Result<T> {
    Err(ParseError::Grammar(msg.into()))
}

fn as_list<'a>(s: &'a Sexp, what: &str) -> Result<&'a [Sexp]> {
    match s {
        Sexp::List(items) => Ok(items),
        _ => err(format!("expected {what} (a list), got `{s}`")),
    }
}

fn as_atom<'a>(s: &'a Sexp, what: &str) -> Result<&'a str> {
    match s {
        Sexp::Atom(a) => Ok(a),
        _ => err(format!("expected {what} (an atom), got `{s}`")),
    }
}

/// A name (`def`/`op`/`scope`/callee) is a bare token — its grammatical position disambiguates
/// it, so the format does not quote it.
fn as_name<'a>(s: &'a Sexp, what: &str) -> Result<&'a str> {
    as_atom(s, what)
}

fn as_u64(s: &Sexp, what: &str) -> Result<u64> {
    as_atom(s, what)?
        .parse()
        .map_err(|_| ParseError::Grammar(format!("expected {what} (a u64), got `{s}`")))
}

fn as_biguint(s: &Sexp, what: &str) -> Result<BigUint> {
    as_atom(s, what)?
        .parse()
        .map_err(|_| ParseError::Grammar(format!("expected {what} (a numeral), got `{s}`")))
}

fn as_var(s: &Sexp) -> Result<Var> {
    Ok(as_atom(s, "a variable")?.to_owned())
}

/// Parse an object type.
fn parse_tp(s: &Sexp) -> Result<Tp> {
    match s {
        Sexp::Atom(a) => match a.as_str() {
            "bool" => Ok(Tp::Bool),
            "nat" => Ok(Tp::Nat),
            "unit" => Ok(Tp::Unit),
            _ => err(format!("unknown type `{a}`")),
        },
        Sexp::List(items) => {
            let head = as_atom(items.first().ok_or_else(|| {
                ParseError::Grammar("empty list is not a type".into())
            })?, "a type head")?;
            match (head, &items[1..]) {
                ("zmod", [p]) => Ok(Tp::ZMod(as_biguint(p, "a modulus")?)),
                ("fin", [n]) => Ok(Tp::Fin(as_u64(n, "a Fin bound")?)),
                ("vec", [a, n]) => {
                    Ok(Tp::Vec(Box::new(parse_tp(a)?), as_u64(n, "a vector length")?))
                }
                ("array", [a]) => Ok(Tp::Array(Box::new(parse_tp(a)?))),
                ("prod", [a, b]) => Ok(Tp::Prod(Box::new(parse_tp(a)?), Box::new(parse_tp(b)?))),
                ("sum", [a, b]) => Ok(Tp::Sum(Box::new(parse_tp(a)?), Box::new(parse_tp(b)?))),
                ("fn", [a, b]) => Ok(Tp::Fn(Box::new(parse_tp(a)?), Box::new(parse_tp(b)?))),
                _ => err(format!("malformed type `{s}`")),
            }
        }
        Sexp::Str(_) => err(format!("expected a type, got string `{s}`")),
    }
}

/// Parse a literal value, directed by its object type.
fn parse_value(tp: &Tp, s: &Sexp) -> Result<Value> {
    match tp {
        Tp::Bool => match as_atom(s, "a bool literal")? {
            "true" => Ok(Value::Bool(true)),
            "false" => Ok(Value::Bool(false)),
            other => err(format!("expected a bool literal, got `{other}`")),
        },
        Tp::Nat => Ok(Value::Nat(as_biguint(s, "a nat literal")?)),
        Tp::Unit => match as_atom(s, "a unit literal")? {
            "unit" => Ok(Value::Unit),
            other => err(format!("expected `unit`, got `{other}`")),
        },
        Tp::ZMod(p) => {
            let v = as_biguint(s, "a field literal")?;
            Ok(Value::Field { val: v % p, modulus: p.clone() })
        }
        Tp::Fin(n) => {
            let v = as_u64(s, "a fin literal")?;
            if v < *n {
                Ok(Value::Fin { val: v, bound: *n })
            } else {
                err(format!("fin literal {v} out of bound {n}"))
            }
        }
        Tp::Vec(a, n) => {
            let elems = as_list(s, "a vec literal")?;
            if elems.len() as u64 != *n {
                return err(format!("vec literal has {} elements, type says {n}", elems.len()));
            }
            Ok(Value::Vec(elems.iter().map(|e| parse_value(a, e)).collect::<Result<Vec<_>>>()?))
        }
        Tp::Array(a) => {
            let elems = as_list(s, "an array literal")?;
            Ok(Value::Array(elems.iter().map(|e| parse_value(a, e)).collect::<Result<Vec<_>>>()?))
        }
        Tp::Prod(a, b) => {
            let items = as_list(s, "a pair literal")?;
            match items {
                [x, y] => Ok(Value::Pair(
                    Box::new(parse_value(a, x)?),
                    Box::new(parse_value(b, y)?),
                )),
                _ => err(format!("expected a two-element pair literal, got `{s}`")),
            }
        }
        Tp::Sum(a, b) => {
            let items = as_list(s, "a sum literal")?;
            match items {
                [head, x] if as_atom(head, "a literal head")? == "inl" => {
                    Ok(Value::Inl(Box::new(parse_value(a, x)?)))
                }
                [head, x] if as_atom(head, "a literal head")? == "inr" => {
                    Ok(Value::Inr(Box::new(parse_value(b, x)?)))
                }
                _ => err(format!("expected `(inl …)`/`(inr …)`, got `{s}`")),
            }
        }
        Tp::Fn(_, _) => match as_atom(s, "an opaque literal")? {
            "opaque" => Ok(Value::Opaque),
            other => err(format!("expected `opaque` for a fn literal, got `{other}`")),
        },
    }
}

fn parse_unop(s: &Sexp) -> Result<UnOp> {
    Ok(match as_atom(s, "a unary op")? {
        "not" => UnOp::Not,
        "fst" => UnOp::Fst,
        "snd" => UnOp::Snd,
        "inl" => UnOp::Inl,
        "inr" => UnOp::Inr,
        "to-array" => UnOp::ToArray,
        "fin-val" => UnOp::FinVal,
        other => return err(format!("unknown unary op `{other}`")),
    })
}

fn parse_binop(s: &Sexp) -> Result<BinOp> {
    Ok(match as_atom(s, "a binary op")? {
        "add" => BinOp::Add,
        "sub" => BinOp::Sub,
        "mul" => BinOp::Mul,
        "pow" => BinOp::Pow,
        "eq" => BinOp::Eq,
        "lt" => BinOp::Lt,
        "le" => BinOp::Le,
        "and" => BinOp::And,
        "or" => BinOp::Or,
        "addf" => BinOp::AddF,
        "subf" => BinOp::SubF,
        "mulf" => BinOp::MulF,
        "powf" => BinOp::PowF,
        "pair" => BinOp::Pair,
        other => return err(format!("unknown binary op `{other}`")),
    })
}

fn parse_pop(s: &Sexp) -> Result<POp> {
    match s {
        Sexp::Atom(a) => Ok(match a.as_str() {
            "vget" => POp::VGet,
            "vset" => POp::VSet,
            "aget" => POp::AGet,
            "aset" => POp::ASet,
            "select" => POp::Select,
            other => return err(format!("unknown partial op `{other}`")),
        }),
        Sexp::List(items) => match &items[..] {
            [head, n] if as_atom(head, "a partial-op head")? == "arr-to-vec" => {
                Ok(POp::ArrToVec(as_u64(n, "a vector length")?))
            }
            [head, n] if as_atom(head, "a partial-op head")? == "nat-to-fin" => {
                Ok(POp::NatToFin(as_u64(n, "a Fin bound")?))
            }
            _ => err(format!("malformed partial op `{s}`")),
        },
        Sexp::Str(_) => err(format!("expected a partial op, got string `{s}`")),
    }
}

/// Parse an expression; `tp` is the binder annotation (needed for type-directed literals).
fn parse_expr(tp: &Tp, s: &Sexp) -> Result<Expr> {
    let items = as_list(s, "an expression")?;
    let head = as_atom(
        items.first().ok_or_else(|| ParseError::Grammar("empty expression".into()))?,
        "an expression head",
    )?;
    match (head, &items[1..]) {
        ("lit", [v]) => Ok(Expr::Lit(parse_value(tp, v)?)),
        ("un", [o, a]) => Ok(Expr::Un(parse_unop(o)?, as_var(a)?)),
        ("bin", [o, a, b]) => Ok(Expr::Bin(parse_binop(o)?, as_var(a)?, as_var(b)?)),
        ("pop", [o, args @ ..]) => Ok(Expr::Pop(
            parse_pop(o)?,
            args.iter().map(as_var).collect::<Result<Vec<_>>>()?,
        )),
        ("vec", args) => Ok(Expr::MkVec(args.iter().map(as_var).collect::<Result<Vec<_>>>()?)),
        ("arr", args) => Ok(Expr::MkArr(args.iter().map(as_var).collect::<Result<Vec<_>>>()?)),
        ("fold", [n, init, binders, body]) => {
            let binders = as_list(binders, "fold binders")?;
            let [index, acc] = binders else {
                return err(format!("fold expects (index acc) binders, got `{s}`"));
            };
            Ok(Expr::Fold {
                count: as_u64(n, "a trip count")?,
                init: as_var(init)?,
                index: as_var(index)?,
                acc: as_var(acc)?,
                body: parse_block(body)?,
            })
        }
        ("vgen", [n, binders, body]) => {
            let binders = as_list(binders, "vgen binders")?;
            let [index] = binders else {
                return err(format!("vgen expects (index) binder, got `{s}`"));
            };
            Ok(Expr::VGen {
                count: as_u64(n, "a trip count")?,
                index: as_var(index)?,
                body: parse_block(body)?,
            })
        }
        ("op", [name, arg]) => Ok(Expr::Op {
            name: as_name(name, "an op name")?.to_owned(),
            arg: as_var(arg)?,
        }),
        ("self", [arg]) => Ok(Expr::SelfCall(as_var(arg)?)),
        ("call", [name, args @ ..]) => Ok(Expr::Call {
            name: as_name(name, "a callee name")?.to_owned(),
            args: args.iter().map(as_var).collect::<Result<Vec<_>>>()?,
        }),
        ("scope", [name, body]) => Ok(Expr::Scope {
            name: as_name(name, "a scope name")?.to_owned(),
            body: parse_block(body)?,
        }),
        _ => err(format!("malformed expression `{s}`")),
    }
}

fn parse_block(s: &Sexp) -> Result<Block> {
    let items = as_list(s, "a block")?;
    match items.split_first() {
        Some((head, rest)) if as_atom(head, "a block head")? == "block" && !rest.is_empty() => {
            let (term, stmts) = rest.split_last().unwrap();
            let stmts = stmts.iter().map(parse_stmt).collect::<Result<Vec<_>>>()?;
            Ok(Block { stmts, term: parse_term(term)? })
        }
        _ => err(format!("expected `(block … term)`, got `{s}`")),
    }
}

fn parse_stmt(s: &Sexp) -> Result<Stmt> {
    let items = as_list(s, "a statement")?;
    match items {
        [head, var, tp, expr] if as_atom(head, "a statement head")? == "let" => {
            let tp = parse_tp(tp)?;
            Ok(Stmt { var: as_var(var)?, expr: parse_expr(&tp, expr)?, tp })
        }
        _ => err(format!("expected `(let var tp expr)`, got `{s}`")),
    }
}

fn parse_term(s: &Sexp) -> Result<Term> {
    let items = as_list(s, "a terminator")?;
    let head = as_atom(
        items.first().ok_or_else(|| ParseError::Grammar("empty terminator".into()))?,
        "a terminator head",
    )?;
    match (head, &items[1..]) {
        ("ret", [v]) => Ok(Term::Ret(as_var(v)?)),
        ("if", [c, t, e]) => Ok(Term::If {
            cond: as_var(c)?,
            then_: Box::new(parse_block(t)?),
            else_: Box::new(parse_block(e)?),
        }),
        _ => err(format!("expected `(ret …)`/`(if …)`, got `{s}`")),
    }
}

fn parse_params(s: &Sexp) -> Result<Vec<(Var, Tp)>> {
    as_list(s, "a parameter list")?
        .iter()
        .map(|p| {
            let items = as_list(p, "a parameter")?;
            match items {
                [v, tp] => Ok((as_var(v)?, parse_tp(tp)?)),
                _ => err(format!("expected `(var tp)`, got `{p}`")),
            }
        })
        .collect()
}

/// Parse a whole `.prog` artifact.
pub fn parse_program(src: &str) -> Result<Program> {
    let sexp = parse_sexp(src)?;
    let items = as_list(&sexp, "a program")?;
    let Some((head, decls)) = items.split_first() else {
        return err("empty program");
    };
    if as_atom(head, "the program head")? != "program" {
        return err(format!("expected `(program …)`, got `{sexp}`"));
    }

    let mut defs = Vec::new();
    let mut main = None;
    for decl in decls {
        let items = as_list(decl, "a declaration")?;
        let head = as_atom(
            items.first().ok_or_else(|| ParseError::Grammar("empty declaration".into()))?,
            "a declaration head",
        )?;
        match (head, &items[1..]) {
            ("def" | "rec", [name, params, ret, body]) => {
                if main.is_some() {
                    return err("definition after main");
                }
                let params = parse_params(params)?;
                if head == "rec" && params.len() != 1 {
                    return err("a rec definition must take exactly one parameter");
                }
                defs.push(Def {
                    name: as_name(name, "a definition name")?.to_owned(),
                    params,
                    ret: parse_tp(ret)?,
                    body: parse_block(body)?,
                    recursive: head == "rec",
                });
            }
            ("main", [params, ret, body]) => {
                if main.is_some() {
                    return err("duplicate main");
                }
                main = Some(Def {
                    name: "main".to_owned(),
                    params: parse_params(params)?,
                    ret: parse_tp(ret)?,
                    body: parse_block(body)?,
                    recursive: false,
                });
            }
            _ => return err(format!("malformed declaration `{decl}`")),
        }
    }
    match main {
        Some(main) => Ok(Program { defs, main }),
        None => err("program has no main"),
    }
}
