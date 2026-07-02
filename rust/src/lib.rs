//! # Freigen Rust SDK
//!
//! Freigen (the Lean library at the repository root) compiles free-monadic Lean programs into a
//! dumb, typed imperative AST and emits it as a **uniform S-expression artifact** (`.prog`, the
//! grammar pinned in `Freigen/Ast/Sexp.lean`).  This crate is the consumer side:
//!
//! * [`parse_program`] — parse an artifact into the typed [`ast::Program`], ready for a client
//!   compiler to walk (every binder is type-annotated; custom effects are opaque named nodes);
//! * [`interp`] — a canonical interpreter mirroring the Lean denotation `denoteProg`, with the
//!   DSL's two extension slots (first-order ops, scoped constructs) injectable through
//!   [`interp::Handler`] — use it to execute compiled programs in tests.
//!
//! ```
//! use freigen::{parse_program, interp::{Handler, Interpreter, Error}, value::Value};
//!
//! // A circuit DSL: `assert` constrains a boolean; `hint` runs its block (witness generation).
//! struct Circuit;
//! impl Handler for Circuit {
//!     fn op(&mut self, name: &str, arg: Value) -> Result<Value, Error> {
//!         match (name, arg) {
//!             ("assert", Value::Bool(true)) => Ok(Value::Unit),
//!             ("assert", Value::Bool(false)) => {
//!                 Err(Error::Op { name: name.into(), message: "assertion failed".into() })
//!             }
//!             _ => Err(Error::Op { name: name.into(), message: "unknown op".into() }),
//!         }
//!     }
//!     // `hint` blocks use the default `scope`: run inline.
//! }
//!
//! let prog = parse_program(
//!     "(program
//!        (main ((x0 nat)) unit
//!          (block
//!            (let v1 nat (scope hint
//!              (block
//!                (let v0 nat (add x0 x0))
//!                (ret v0))))
//!            (let v2 nat (add x0 x0))
//!            (let v3 bool (eq v1 v2))
//!            (let v4 unit (op assert v3))
//!            (ret v4))))",
//! ).unwrap();
//! let interp = Interpreter::new(&prog);
//! let out = interp.run_main(&mut Circuit, vec![Value::nat(21u32)]).unwrap();
//! assert_eq!(out, Value::Unit);
//! ```

pub mod ast;
pub mod interp;
pub mod parse;
pub mod sexp;
pub mod value;

pub use parse::{parse_program, ParseError};

#[cfg(test)]
mod tests {
    use crate::interp::{Error, Handler, Interpreter, NoCustomOps, ScopeCall};
    use crate::parse_program;
    use crate::value::Value;

    fn run(src: &str, args: Vec<Value>) -> Result<Value, Error> {
        let prog = parse_program(src).expect("parse");
        Interpreter::new(&prog).run_main(&mut NoCustomOps, args)
    }

    #[test]
    fn pure_arithmetic_and_calls() {
        // A helper spilled into a def, called twice from main.
        let src = r#"
          (program
            (def double ((x0 nat)) nat
              (block
                (let v1 nat (add x0 x0))
                (ret v1)))
            (main ((x2 nat)) nat
              (block
                (let v3 nat (call double x2))
                (let v4 nat (call double v3))
                (ret v4))))"#;
        assert_eq!(run(src, vec![Value::nat(3u32)]).unwrap(), Value::nat(12u32));
    }

    #[test]
    fn truncated_nat_sub() {
        let src = r#"
          (program
            (main ((x0 nat) (x1 nat)) nat
              (block
                (let v2 nat (sub x0 x1))
                (ret v2))))"#;
        assert_eq!(
            run(src, vec![Value::nat(2u32), Value::nat(5u32)]).unwrap(),
            Value::nat(0u32)
        );
    }

    #[test]
    fn field_arithmetic() {
        // dbl in ZMod 5: 4 + 4 = 3 (mod 5).
        let src = r#"
          (program
            (main ((x0 (zmod 5))) (zmod 5)
              (block
                (let v1 (zmod 5) (addf x0 x0))
                (ret v1))))"#;
        assert_eq!(
            run(src, vec![Value::field(4u32, 5u32)]).unwrap(),
            Value::field(3u32, 5u32)
        );
    }

    #[test]
    fn fold_and_vgen() {
        // Sum the lanes of (vgen 4 i => i.val + 1) with a fold: 1+2+3+4 = 10.
        let src = r#"
          (program
            (main () nat
              (block
                (let v0 (vec nat 4) (vgen 4 (i1)
                  (block
                    (let v2 nat (fin-val i1))
                    (let v3 nat (lit 1))
                    (let v4 nat (add v2 v3))
                    (ret v4))))
                (let v5 nat (lit 0))
                (let v6 nat (fold 4 v5 (i7 a8)
                  (block
                    (let v9 nat (fin-val i7))
                    (let v10 nat (vget v0 v9))
                    (let v11 nat (add a8 v10))
                    (ret v11))))
                (ret v6))))"#;
        assert_eq!(run(src, vec![]).unwrap(), Value::nat(10u32));
    }

    #[test]
    fn out_of_range_get_fails() {
        let src = r#"
          (program
            (main ((x0 (vec nat 3)) (x1 nat)) nat
              (block
                (let v2 nat (vget x0 x1))
                (ret v2))))"#;
        let v = Value::Vec(vec![Value::nat(10u32), Value::nat(20u32), Value::nat(30u32)]);
        assert_eq!(run(src, vec![v.clone(), Value::nat(1u32)]).unwrap(), Value::nat(20u32));
        assert_eq!(run(src, vec![v, Value::nat(5u32)]).unwrap_err(), Error::Fail);
    }

    #[test]
    fn partial_upcasts() {
        let src = r#"
          (program
            (main ((x0 (array nat))) (vec nat 3)
              (block
                (let v1 (vec nat 3) (arr-to-vec 3 x0))
                (ret v1))))"#;
        let ok = Value::Array(vec![Value::nat(1u32), Value::nat(2u32), Value::nat(3u32)]);
        let bad = Value::Array(vec![Value::nat(1u32)]);
        assert_eq!(
            run(src, vec![ok]).unwrap(),
            Value::Vec(vec![Value::nat(1u32), Value::nat(2u32), Value::nat(3u32)])
        );
        assert_eq!(run(src, vec![bad]).unwrap_err(), Error::Fail);
    }

    #[test]
    fn branch_and_select() {
        let src = r#"
          (program
            (main ((x0 bool) (x1 nat) (x2 nat)) nat
              (block
                (let v3 nat (select x0 x1 x2))
                (if x0
                  (block
                    (ret v3))
                  (block
                    (let v4 nat (lit 100))
                    (let v5 nat (add v3 v4))
                    (ret v5))))))"#;
        let args = |b| vec![Value::Bool(b), Value::nat(1u32), Value::nat(2u32)];
        assert_eq!(run(src, args(true)).unwrap(), Value::nat(1u32));
        assert_eq!(run(src, args(false)).unwrap(), Value::nat(102u32));
    }

    #[test]
    fn recursion() {
        // sm n = n, by non-tail structural recursion.
        let src = r#"
          (program
            (rec sm ((x0 nat)) nat
              (block
                (let v1 nat (lit 0))
                (let v2 bool (eq x0 v1))
                (if v2
                  (block
                    (let v3 nat (lit 0))
                    (ret v3))
                  (block
                    (let v4 nat (lit 1))
                    (let v5 nat (sub x0 v4))
                    (let v6 nat (self v5))
                    (let v7 nat (lit 1))
                    (let v8 nat (add v6 v7))
                    (ret v8)))))
            (main ((x9 nat)) nat
              (block
                (let v10 nat (call sm x9))
                (ret v10))))"#;
        assert_eq!(run(src, vec![Value::nat(7u32)]).unwrap(), Value::nat(7u32));
        // Unbounded depth is caught, not a stack overflow.
        assert_eq!(run(src, vec![Value::nat(100_000u32)]).unwrap_err(), Error::CallDepth);
    }

    #[test]
    fn stateful_op_handler() {
        // The StoreOp DSL: a mutable Nat store addressed by Nat.
        struct Store(std::collections::HashMap<Value, Value>);
        impl Handler for Store {
            fn op(&mut self, name: &str, arg: Value) -> Result<Value, Error> {
                match (name, arg) {
                    ("get", a) => Ok(self
                        .0
                        .get(&a)
                        .cloned()
                        .unwrap_or(Value::nat(0u32))),
                    ("set", Value::Pair(a, v)) => {
                        self.0.insert(*a, *v);
                        Ok(Value::Unit)
                    }
                    _ => Err(Error::Op { name: name.into(), message: "unknown op".into() }),
                }
            }
        }
        let src = r#"
          (program
            (main () nat
              (block
                (let v0 (prod nat nat) (lit (0 42)))
                (let v1 unit (op set v0))
                (let v2 nat (lit 0))
                (let v3 nat (op get v2))
                (ret v3))))"#;
        let prog = parse_program(src).unwrap();
        let mut store = Store(Default::default());
        let out = Interpreter::new(&prog).run_main(&mut store, vec![]).unwrap();
        assert_eq!(out, Value::nat(42u32));
    }

    #[test]
    fn scope_denotation_is_injectable() {
        // A handler that *erases* hint blocks, substituting a fixed witness — the shape of a
        // constrained (conCirc-like) semantics rather than witness generation.
        struct Erasing;
        impl Handler for Erasing {
            fn op(&mut self, _name: &str, _arg: Value) -> Result<Value, Error> {
                Ok(Value::Unit)
            }
            fn scope(&mut self, name: &str, _block: &mut ScopeCall<'_, '_>) -> Result<Value, Error> {
                assert_eq!(name, "hint");
                Ok(Value::nat(999u32)) // fresh existential, block never run
            }
        }

        let src = r#"
          (program
            (main () nat
              (block
                (let v1 nat (scope hint
                  (block
                    (let v0 nat (lit 7))
                    (ret v0))))
                (ret v1))))"#;
        let prog = parse_program(src).unwrap();
        assert_eq!(
            Interpreter::new(&prog).run_main(&mut Erasing, vec![]).unwrap(),
            Value::nat(999u32)
        );
        // …while the default denotation runs the block.
        struct Running;
        impl Handler for Running {
            fn op(&mut self, _name: &str, _arg: Value) -> Result<Value, Error> {
                Ok(Value::Unit)
            }
        }
        assert_eq!(
            Interpreter::new(&prog).run_main(&mut Running, vec![]).unwrap(),
            Value::nat(7u32)
        );
    }
}
