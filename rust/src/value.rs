//! Runtime values — the Rust image of `Tp.denote`.

use std::fmt;

use num_bigint::BigUint;

/// A runtime value of some object type.
///
/// Numbers are arbitrary-precision: `Nat` is an unbounded natural, `Field` a canonical
/// representative modulo its prime (the modulus travels with the value, so field arithmetic needs
/// no ambient typing).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Value {
    Bool(bool),
    Nat(BigUint),
    Field { val: BigUint, modulus: BigUint },
    Unit,
    Pair(Box<Value>, Box<Value>),
    Vec(Vec<Value>),
    Array(Vec<Value>),
    Inl(Box<Value>),
    Inr(Box<Value>),
    Fin { val: u64, bound: u64 },
    /// The image of a literal with no serializable payload (a function-typed literal).  Inspecting
    /// it in any primitive is a runtime error.
    Opaque,
}

impl Value {
    /// A `Nat` from anything convertible to a `BigUint`.
    pub fn nat(n: impl Into<BigUint>) -> Value {
        Value::Nat(n.into())
    }

    /// A field element, reduced into canonical range.
    pub fn field(val: impl Into<BigUint>, modulus: impl Into<BigUint>) -> Value {
        let modulus = modulus.into();
        Value::Field { val: val.into() % &modulus, modulus }
    }

    /// A field element with the modulus given in decimal (convenient for big primes).
    ///
    /// # Panics
    /// Panics if either string is not a decimal numeral.
    pub fn field_dec(val: &str, modulus: &str) -> Value {
        let val: BigUint = val.parse().expect("invalid decimal value");
        let modulus: BigUint = modulus.parse().expect("invalid decimal modulus");
        Value::Field { val: val % &modulus, modulus }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Nat(n) => write!(f, "{n}"),
            Value::Field { val, .. } => write!(f, "{val}"),
            Value::Unit => write!(f, "unit"),
            Value::Pair(a, b) => write!(f, "({a} {b})"),
            Value::Vec(xs) | Value::Array(xs) => {
                write!(f, "(")?;
                for (i, x) in xs.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{x}")?;
                }
                write!(f, ")")
            }
            Value::Inl(x) => write!(f, "(inl {x})"),
            Value::Inr(x) => write!(f, "(inr {x})"),
            Value::Fin { val, .. } => write!(f, "{val}"),
            Value::Opaque => write!(f, "opaque"),
        }
    }
}
