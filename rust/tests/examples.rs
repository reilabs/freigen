//! End-to-end tests over the goldens project (`examples/client/`).
//!
//! The client project `#compile`s its programs into `.prog` artifacts; CI pins them as goldens in
//! `examples/client/expected/`.  These tests close the loop: parse each golden with the SDK and
//! **execute** it with the canonical interpreter under the circuit DSL's denotations, checking
//! the same results the Lean side pins (`runCirc` `#eval`s / the circomlib Poseidon vectors).

use std::fs;
use std::path::PathBuf;

use freigen::interp::{Error, Handler, Interpreter};
use freigen::parse_program;
use freigen::value::Value;

/// BN254 scalar-field prime (the modulus of the Poseidon circuit's `ZMod`).
const BN254_FR: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";

fn goldens_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../examples/client/expected")
}

fn read_golden(name: &str) -> String {
    let path = goldens_dir().join(name);
    fs::read_to_string(&path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()))
}

/// The `CircOp`/`HintS` denotations of witness generation (Lean's `runCirc`): `assert` fails on
/// `false`, a `hint` block is run inline (the default `scope`).
struct Circuit;

impl Handler for Circuit {
    fn op(&mut self, name: &str, arg: Value) -> Result<Value, Error> {
        match (name, arg) {
            ("assert", Value::Bool(true)) => Ok(Value::Unit),
            ("assert", Value::Bool(false)) => {
                Err(Error::Op { name: name.into(), message: "assertion failed".into() })
            }
            (_, arg) => Err(Error::Op {
                name: name.into(),
                message: format!("no denotation for argument {arg}"),
            }),
        }
    }
}

/// Every golden artifact must parse with the SDK.
#[test]
fn all_goldens_parse() {
    let mut count = 0;
    for entry in fs::read_dir(goldens_dir()).expect("goldens directory") {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "prog") {
            let src = fs::read_to_string(&path).unwrap();
            parse_program(&src)
                .unwrap_or_else(|e| panic!("{} does not parse: {e}", path.display()));
            count += 1;
        }
    }
    assert!(count >= 2, "expected at least the client's two artifacts, found {count}");
}

/// `myProgram`: hint x = 15, hint y = 2·x, assert (y == 30) — witness generation succeeds.
#[test]
fn my_program_runs() {
    let prog = parse_program(&read_golden("myProgram.prog")).unwrap();
    let out = Interpreter::new(&prog).run_main(&mut Circuit, vec![]).unwrap();
    assert_eq!(out, Value::Unit);
}

/// The Poseidon hash, executed from the compiled artifact, against the circomlib-pinned
/// known-answer vectors (the same ones `Client/Poseidon.lean` pins with `#eval runCirc`).
#[test]
fn poseidon_known_answer_vectors() {
    let prog = parse_program(&read_golden("poseidon.prog")).unwrap();
    let interp = Interpreter::new(&prog);

    let hash = |a: &str, b: &str| {
        interp
            .run_main(
                &mut Circuit,
                vec![Value::field_dec(a, BN254_FR), Value::field_dec(b, BN254_FR)],
            )
            .unwrap()
    };

    assert_eq!(
        hash("1", "2"),
        Value::field_dec(
            "7853200120776062878684798364095072458815029376092732009249414926327459813530",
            BN254_FR
        )
    );
    assert_eq!(
        hash("3", "4"),
        Value::field_dec(
            "14763215145315200506921711489642608356394854266165572616578112107564877678998",
            BN254_FR
        )
    );
}
