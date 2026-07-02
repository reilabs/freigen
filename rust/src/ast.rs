//! The client-side AST for Freigen-compiled programs.
//!
//! This mirrors the Lean-side `Prog`/`Code` (see `Freigen/Ast/Basic.lean`) one-to-one, in the
//! shape a client compiler wants to consume: a program is a list of top-level definitions ending
//! in `main`; a definition body is a *block* — a straight-line sequence of single-assignment
//! `let`s ending in a return or a branch; every binder is annotated with its object type.
//!
//! Custom effects stay opaque: an `Expr::Op`/`Expr::Scope` carries the DSL-level name, and it is
//! the client's business (via [`crate::interp::Handler`] or its own backend) to give it meaning.

use num_bigint::BigUint;

use crate::value::Value;

/// The object-type universe (Lean's `Tp`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tp {
    Bool,
    Nat,
    Unit,
    /// A prime-field element `ZMod p` (the modulus is part of the type).
    ZMod(BigUint),
    /// A bounded natural `Fin n`.
    Fin(u64),
    /// A fixed-length vector.
    Vec(Box<Tp>, u64),
    /// A dynamically-sized array.
    Array(Box<Tp>),
    Prod(Box<Tp>, Box<Tp>),
    Sum(Box<Tp>, Box<Tp>),
    Fn(Box<Tp>, Box<Tp>),
}

/// Total unary primitives (Lean's `Un`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    /// Boolean negation.
    Not,
    /// First projection of a pair.
    Fst,
    /// Second projection of a pair.
    Snd,
    /// Left injection into a sum.
    Inl,
    /// Right injection into a sum.
    Inr,
    /// Total downcast: forget a vector's static length.
    ToArray,
    /// Total downcast: forget a `Fin`'s bound.
    FinVal,
}

/// Total binary primitives (Lean's `Bin`).  `Nat` subtraction is truncated at zero; the `…F`
/// variants are prime-field arithmetic (`PowF` takes a `Nat` exponent).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Pow,
    Eq,
    Lt,
    Le,
    And,
    Or,
    AddF,
    SubF,
    MulF,
    PowF,
    Pair,
}

/// Partial (proof-erased) primitives (Lean's `POp`).  Their proof obligations were erased at
/// reflection time, so at runtime they may **fail** (out-of-range index, size mismatch) — except
/// `Select`, which is total and lives here only for node-shape uniformity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum POp {
    /// `v[i]` on a vector (fails out of range).
    VGet,
    /// `v with [i] := x` on a vector (fails out of range).
    VSet,
    /// `a[i]` on an array (fails out of range).
    AGet,
    /// `a with [i] := x` on an array (fails out of range).
    ASet,
    /// Strict `c ? x : y` — both branches already evaluated; total.
    Select,
    /// Upcast `array → vec n` (fails unless the size is exactly `n`).
    ArrToVec(u64),
    /// Upcast `nat → fin n` (fails unless the value is `< n`).
    NatToFin(u64),
}

/// A variable name.  Names are machine-generated and unique within a definition (`x…` for
/// parameters, `v…` for lets, `i…`/`a…` for loop binders).
pub type Var = String;

/// The right-hand side of a `let`, or more generally one AST instruction.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    /// A host literal (already typed by the binder's annotation).
    Lit(Value),
    Un(UnOp, Var),
    Bin(BinOp, Var, Var),
    /// A partial primitive — the only failure point of the pure fragment.
    Pop(POp, Vec<Var>),
    /// Vector construction from element atoms.
    MkVec(Vec<Var>),
    /// Array construction from element atoms.
    MkArr(Vec<Var>),
    /// A bounded fold: `count` iterations from `init`, the body binding (`index : Fin count`,
    /// `acc`) and returning the next accumulator.  A first-class loop — never unrolled.
    Fold { count: u64, init: Var, index: Var, acc: Var, body: Block },
    /// A bounded generator (`Vector.ofFn`): run `body` once per `index : Fin count`, in order,
    /// collecting a vector.
    VGen { count: u64, index: Var, body: Block },
    /// A custom first-order effect — meaning supplied by the client.
    Op { name: String, arg: Var },
    /// The self-call inside a `rec` definition's body.
    SelfCall(Var),
    /// A call to a top-level definition.
    Call { name: String, args: Vec<Var> },
    /// A scoped construct carrying an in-monad block — meaning supplied by the client (the
    /// canonical interpreter runs the block inline by default).
    Scope { name: String, body: Block },
}

/// One statement: `(let var tp expr)`.
#[derive(Clone, Debug, PartialEq)]
pub struct Stmt {
    pub var: Var,
    pub tp: Tp,
    pub expr: Expr,
}

/// How a block ends.
#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    /// Return an atom.
    Ret(Var),
    /// A boolean branch in tail position.
    If { cond: Var, then_: Box<Block>, else_: Box<Block> },
}

/// A straight-line sequence of single-assignment `let`s ending in a terminator.
#[derive(Clone, Debug, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub term: Term,
}

/// A top-level definition (a `def`, a `rec`, or `main`).
#[derive(Clone, Debug, PartialEq)]
pub struct Def {
    pub name: String,
    pub params: Vec<(Var, Tp)>,
    pub ret: Tp,
    pub body: Block,
    /// `true` for a `rec` definition — its body may contain `Expr::SelfCall`.
    pub recursive: bool,
}

/// A whole program: the pulled-out definitions (in dependency order — a body only calls earlier
/// definitions or, if `recursive`, itself) and the entry point.
#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    pub defs: Vec<Def>,
    pub main: Def,
}

impl Program {
    /// Look up a non-`main` definition by name.
    pub fn def(&self, name: &str) -> Option<&Def> {
        self.defs.iter().find(|d| d.name == name)
    }
}
