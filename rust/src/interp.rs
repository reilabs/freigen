//! The canonical interpreter — the executable image of the Lean-side denotation `denoteProg`.
//!
//! The pure fragment (literals, primitives, collections, loops, calls, recursion) is interpreted
//! directly; the two extension slots of the source DSL stay *client-injectable*, exactly as in the
//! Lean semantics:
//!
//! * a custom first-order effect `(op "name" v)` dispatches to [`Handler::op`];
//! * a scoped construct `(scope "name" block)` dispatches to [`Handler::scope`], which receives
//!   the block as a runnable [`ScopeCall`] — run it inline (the default, mirroring `ofFree`),
//!   substitute another value, or fail.
//!
//! Failure is first-class: a partial primitive whose erased proof obligation does not hold
//! evaluates to [`Error::Fail`] — the interpreter image of `ITree.fail`.  (A *reflected* program
//! carries a proof that this cannot happen on the source's inputs.)

use std::collections::HashMap;

use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};

use crate::ast::*;
use crate::value::Value;

/// An interpreter error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    /// A partial primitive failed (out-of-range access, size mismatch) — `ITree.fail`.
    Fail,
    /// A custom op or scope denotation reported failure.
    Op { name: String, message: String },
    /// The self-call/call chain exceeded [`Interpreter::max_call_depth`].
    CallDepth,
    /// The program is malformed (unbound variable, arity/type mismatch): a broken artifact or
    /// wrong `main` inputs, never a mere failing computation.
    Malformed(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Fail => write!(f, "computation failed (erased proof obligation violated)"),
            Error::Op { name, message } => write!(f, "op `{name}` failed: {message}"),
            Error::CallDepth => write!(f, "call depth exceeded"),
            Error::Malformed(m) => write!(f, "malformed program: {m}"),
        }
    }
}

impl std::error::Error for Error {}

type Result<T> = std::result::Result<T, Error>;

fn malformed<T>(msg: impl Into<String>) -> Result<T> {
    Err(Error::Malformed(msg.into()))
}

/// The denotations a client injects for the DSL's two extension slots.
///
/// The type parameter of the whole design is *names*: ops and scopes arrive as the strings the
/// Lean `DSL` instance chose, and the handler pattern-matches on them.
pub trait Handler {
    /// Denote a custom first-order effect: `(op "name" arg)`.
    fn op(&mut self, name: &str, arg: Value) -> Result<Value>;

    /// Denote a scoped construct: `(scope "name" block)`.  The default runs the block inline —
    /// the canonical (`ofFree`) semantics, e.g. witness generation for a `hint`.  Override to
    /// erase the block, sandbox it, or substitute a value.
    fn scope(&mut self, name: &str, block: &mut ScopeCall<'_, '_>) -> Result<Value>
    where
        Self: Sized,
    {
        let _ = name;
        block.run(self)
    }
}

/// A handler for DSLs with no custom ops and no scoped constructs (or for programs that use
/// neither): every op is an error.
pub struct NoCustomOps;

impl Handler for NoCustomOps {
    fn op(&mut self, name: &str, _arg: Value) -> Result<Value> {
        Err(Error::Op { name: name.to_owned(), message: "no denotation injected".into() })
    }
}

/// The in-monad block of a scoped construct, packaged for [`Handler::scope`] as a runnable
/// closure over the enclosing environment.
pub struct ScopeCall<'a, 'p> {
    interp: &'a Interpreter<'p>,
    env: &'a mut Env,
    rec: Option<&'p Def>,
    depth: usize,
    block: &'p Block,
}

impl ScopeCall<'_, '_> {
    /// Run the block under the given handler (usually the receiving handler itself) and return
    /// its value.
    pub fn run<H: Handler>(&mut self, handler: &mut H) -> Result<Value> {
        self.interp.eval_block(handler, self.env, self.rec, self.depth, self.block)
    }
}

type Env = HashMap<Var, Value>;

/// The canonical interpreter over a parsed [`Program`].
pub struct Interpreter<'p> {
    program: &'p Program,
    defs: HashMap<&'p str, &'p Def>,
    /// Maximum call nesting (calls + self-calls); guards the Rust stack against runaway
    /// recursion (the interpreter recurses on the host stack).  Default: 128, safe for the
    /// standard 2 MiB test-thread stack; raise it together with the thread's stack size
    /// (`std::thread::Builder::stack_size`) for deeply recursive programs.
    pub max_call_depth: usize,
}

impl<'p> Interpreter<'p> {
    pub fn new(program: &'p Program) -> Self {
        let defs = program.defs.iter().map(|d| (d.name.as_str(), d)).collect();
        Interpreter { program, defs, max_call_depth: 128 }
    }

    /// Run `main` on the given argument values (one per parameter, in order).
    pub fn run_main<H: Handler>(&self, handler: &mut H, args: Vec<Value>) -> Result<Value> {
        self.call(handler, &self.program.main, args, 0)
    }

    fn call<H: Handler>(
        &self,
        handler: &mut H,
        def: &'p Def,
        args: Vec<Value>,
        depth: usize,
    ) -> Result<Value> {
        if depth >= self.max_call_depth {
            return Err(Error::CallDepth);
        }
        if args.len() != def.params.len() {
            return malformed(format!(
                "`{}` takes {} arguments, got {}",
                def.name,
                def.params.len(),
                args.len()
            ));
        }
        let mut env: Env =
            def.params.iter().map(|(v, _)| v.clone()).zip(args).collect();
        let rec = def.recursive.then_some(def);
        self.eval_block(handler, &mut env, rec, depth, &def.body)
    }

    fn eval_block<H: Handler>(
        &self,
        handler: &mut H,
        env: &mut Env,
        rec: Option<&'p Def>,
        depth: usize,
        block: &'p Block,
    ) -> Result<Value> {
        for stmt in &block.stmts {
            let v = self.eval_expr(handler, env, rec, depth, &stmt.expr)?;
            env.insert(stmt.var.clone(), v);
        }
        match &block.term {
            Term::Ret(v) => lookup(env, v),
            Term::If { cond, then_, else_ } => match lookup(env, cond)? {
                Value::Bool(true) => self.eval_block(handler, env, rec, depth, then_),
                Value::Bool(false) => self.eval_block(handler, env, rec, depth, else_),
                other => malformed(format!("if condition is not a bool: {other}")),
            },
        }
    }

    fn eval_expr<H: Handler>(
        &self,
        handler: &mut H,
        env: &mut Env,
        rec: Option<&'p Def>,
        depth: usize,
        expr: &'p Expr,
    ) -> Result<Value> {
        match expr {
            Expr::Lit(v) => Ok(v.clone()),
            Expr::Un(op, a) => eval_un(*op, lookup(env, a)?),
            Expr::Bin(op, a, b) => eval_bin(*op, lookup(env, a)?, lookup(env, b)?),
            Expr::Pop(op, args) => {
                let args =
                    args.iter().map(|a| lookup(env, a)).collect::<Result<Vec<_>>>()?;
                eval_pop(op, args)
            }
            Expr::MkVec(elems) => {
                Ok(Value::Vec(elems.iter().map(|e| lookup(env, e)).collect::<Result<_>>()?))
            }
            Expr::MkArr(elems) => {
                Ok(Value::Array(elems.iter().map(|e| lookup(env, e)).collect::<Result<_>>()?))
            }
            Expr::Fold { count, init, index, acc, body } => {
                let mut a = lookup(env, init)?;
                for i in 0..*count {
                    env.insert(index.clone(), Value::Fin { val: i, bound: *count });
                    env.insert(acc.clone(), a);
                    a = self.eval_block(handler, env, rec, depth, body)?;
                }
                Ok(a)
            }
            Expr::VGen { count, index, body } => {
                let mut out = Vec::with_capacity(*count as usize);
                for i in 0..*count {
                    env.insert(index.clone(), Value::Fin { val: i, bound: *count });
                    out.push(self.eval_block(handler, env, rec, depth, body)?);
                }
                Ok(Value::Vec(out))
            }
            Expr::Op { name, arg } => handler.op(name, lookup(env, arg)?),
            Expr::SelfCall(arg) => match rec {
                Some(def) => {
                    let arg = lookup(env, arg)?;
                    self.call(handler, def, vec![arg], depth + 1)
                }
                None => malformed("self-call outside a rec definition"),
            },
            Expr::Call { name, args } => match self.defs.get(name.as_str()) {
                Some(def) => {
                    let args =
                        args.iter().map(|a| lookup(env, a)).collect::<Result<Vec<_>>>()?;
                    self.call(handler, def, args, depth + 1)
                }
                None => malformed(format!("call to unknown definition `{name}`")),
            },
            Expr::Scope { name, body } => {
                let mut call = ScopeCall { interp: self, env, rec, depth, block: body };
                handler.scope(name, &mut call)
            }
        }
    }
}

fn lookup(env: &Env, v: &Var) -> Result<Value> {
    env.get(v).cloned().ok_or_else(|| Error::Malformed(format!("unbound variable `{v}`")))
}

fn as_nat(v: Value) -> Result<BigUint> {
    match v {
        Value::Nat(n) => Ok(n),
        other => malformed(format!("expected a nat, got {other}")),
    }
}

fn as_bool(v: Value) -> Result<bool> {
    match v {
        Value::Bool(b) => Ok(b),
        other => malformed(format!("expected a bool, got {other}")),
    }
}

fn as_field(v: Value) -> Result<(BigUint, BigUint)> {
    match v {
        Value::Field { val, modulus } => Ok((val, modulus)),
        other => malformed(format!("expected a field element, got {other}")),
    }
}

fn as_index(v: Value) -> Result<usize> {
    let n = as_nat(v)?;
    // An index beyond usize is certainly out of any collection's range: report `Fail`, the same
    // failure the in-range check would produce.
    n.to_usize().ok_or(Error::Fail)
}

fn eval_un(op: UnOp, a: Value) -> Result<Value> {
    match (op, a) {
        (UnOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
        (UnOp::Fst, Value::Pair(x, _)) => Ok(*x),
        (UnOp::Snd, Value::Pair(_, y)) => Ok(*y),
        (UnOp::Inl, x) => Ok(Value::Inl(Box::new(x))),
        (UnOp::Inr, x) => Ok(Value::Inr(Box::new(x))),
        (UnOp::ToArray, Value::Vec(xs)) => Ok(Value::Array(xs)),
        (UnOp::FinVal, Value::Fin { val, .. }) => Ok(Value::Nat(BigUint::from(val))),
        (op, a) => malformed(format!("unary op {op:?} applied to {a}")),
    }
}

fn eval_bin(op: BinOp, a: Value, b: Value) -> Result<Value> {
    match op {
        BinOp::Pair => Ok(Value::Pair(Box::new(a), Box::new(b))),
        BinOp::And => Ok(Value::Bool(as_bool(a)? && as_bool(b)?)),
        BinOp::Or => Ok(Value::Bool(as_bool(a)? || as_bool(b)?)),
        BinOp::Add => Ok(Value::Nat(as_nat(a)? + as_nat(b)?)),
        // Lean's Nat subtraction is truncated at zero.
        BinOp::Sub => {
            let (a, b) = (as_nat(a)?, as_nat(b)?);
            Ok(Value::Nat(if a >= b { a - b } else { BigUint::zero() }))
        }
        BinOp::Mul => Ok(Value::Nat(as_nat(a)? * as_nat(b)?)),
        BinOp::Pow => {
            let (a, b) = (as_nat(a)?, as_nat(b)?);
            let exp = b
                .to_u32()
                .ok_or_else(|| Error::Malformed("nat exponent too large".into()))?;
            Ok(Value::Nat(a.pow(exp)))
        }
        BinOp::Eq => Ok(Value::Bool(as_nat(a)? == as_nat(b)?)),
        BinOp::Lt => Ok(Value::Bool(as_nat(a)? < as_nat(b)?)),
        BinOp::Le => Ok(Value::Bool(as_nat(a)? <= as_nat(b)?)),
        BinOp::AddF | BinOp::SubF | BinOp::MulF => {
            let (x, p) = as_field(a)?;
            let (y, q) = as_field(b)?;
            if p != q {
                return malformed("field ops on mismatched moduli");
            }
            let r = match op {
                BinOp::AddF => (x + y) % &p,
                BinOp::SubF => (x + &p - y) % &p,
                BinOp::MulF => (x * y) % &p,
                _ => unreachable!(),
            };
            Ok(Value::Field { val: r, modulus: p })
        }
        BinOp::PowF => {
            let (x, p) = as_field(a)?;
            let e = as_nat(b)?;
            if p.is_one() {
                return Ok(Value::Field { val: BigUint::zero(), modulus: p });
            }
            let r = x.modpow(&e, &p);
            Ok(Value::Field { val: r, modulus: p })
        }
    }
}

fn eval_pop(op: &POp, mut args: Vec<Value>) -> Result<Value> {
    let arity = match op {
        POp::VGet | POp::AGet => 2,
        POp::VSet | POp::ASet | POp::Select => 3,
        POp::ArrToVec(_) | POp::NatToFin(_) => 1,
    };
    if args.len() != arity {
        return malformed(format!("partial op {op:?} expects {arity} arguments"));
    }
    match op {
        POp::VGet | POp::AGet => {
            let i = as_index(args.remove(1))?;
            let xs = as_elems(args.remove(0))?;
            xs.get(i).cloned().ok_or(Error::Fail)
        }
        POp::VSet | POp::ASet => {
            let x = args.remove(2);
            let i = as_index(args.remove(1))?;
            let coll = args.remove(0);
            let rebuild = |xs: Vec<Value>| -> Result<Vec<Value>> {
                let mut xs = xs;
                if i < xs.len() {
                    xs[i] = x;
                    Ok(xs)
                } else {
                    Err(Error::Fail)
                }
            };
            match coll {
                Value::Vec(xs) => Ok(Value::Vec(rebuild(xs)?)),
                Value::Array(xs) => Ok(Value::Array(rebuild(xs)?)),
                other => malformed(format!("set on a non-collection: {other}")),
            }
        }
        POp::Select => {
            let y = args.remove(2);
            let x = args.remove(1);
            let c = as_bool(args.remove(0))?;
            Ok(if c { x } else { y })
        }
        POp::ArrToVec(n) => match args.remove(0) {
            Value::Array(xs) if xs.len() as u64 == *n => Ok(Value::Vec(xs)),
            Value::Array(_) => Err(Error::Fail),
            other => malformed(format!("arr-to-vec on a non-array: {other}")),
        },
        POp::NatToFin(n) => {
            let m = as_nat(args.remove(0))?;
            match m.to_u64() {
                Some(val) if val < *n => Ok(Value::Fin { val, bound: *n }),
                _ => Err(Error::Fail),
            }
        }
    }
}

fn as_elems(v: Value) -> Result<Vec<Value>> {
    match v {
        Value::Vec(xs) | Value::Array(xs) => Ok(xs),
        other => malformed(format!("expected a collection, got {other}")),
    }
}
