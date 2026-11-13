module

public import Mathlib

/-!
# The shared statement

This file is the single source of truth. Neither proof file may change it.

We work with the *generic* monic quintic
  `X^5 + a₄ X^4 + a₃ X^3 + a₂ X^2 + a₁ X + a₀`
whose coefficients `a₀, …, a₄` are independent indeterminates over `ℂ`.

A "formula in radicals" is a syntactic expression (`RadExpr`) built from the
coefficients, complex constants, field operations, and `n`-th roots.
`Value e y` says that `y` is one of the possible values of `e`, where every
`n`-th root may be any choice of `n`-th root. The statement says that no
choice of value of any radical expression is a root of the generic quintic.

Design note: the values live in an algebraic closure of the function field
`ℂ(a₀, …, a₄)`. That is the natural home for the Galois proof. The Arnold proof
works with multivalued analytic functions of complex coefficients, so it must
supply a bridge from these values to analytic continuation. See `Arnold.lean`.
-/

@[expose] public section

open Polynomial

namespace Quintic

/-- Polynomials in the five coefficient indeterminates. -/
abbrev R : Type := MvPolynomial (Fin 5) ℂ

/-- The coefficient field `ℂ(a₀, …, a₄)`. -/
abbrev K : Type := FractionRing R

/-- Where values of radical expressions live. -/
abbrev L : Type := AlgebraicClosure K

/-- The coefficient `aᵢ` as an element of `K`. -/
noncomputable def a (i : Fin 5) : K := algebraMap R K (MvPolynomial.X i)

/-- A complex constant as an element of `K`. -/
noncomputable def constK (c : ℂ) : K := algebraMap R K (MvPolynomial.C c)

/-- The generic monic quintic `X^5 + ∑ aᵢ X^i`. -/
noncomputable def genericQuintic : K[X] :=
  X ^ 5 + ∑ i : Fin 5, C (a i) * X ^ (i : ℕ)

/-- Formulas in radicals, as syntax. -/
inductive RadExpr : Type
  | var : Fin 5 → RadExpr
  | const : ℂ → RadExpr
  | add : RadExpr → RadExpr → RadExpr
  | neg : RadExpr → RadExpr
  | mul : RadExpr → RadExpr → RadExpr
  | inv : RadExpr → RadExpr
  | root : ℕ → RadExpr → RadExpr

/-- `Value e y`: `y` is a possible value of `e`, with any choice of `n`-th roots. -/
inductive Value : RadExpr → L → Prop
  | var (i : Fin 5) : Value (.var i) (algebraMap K L (a i))
  | const (c : ℂ) : Value (.const c) (algebraMap K L (constK c))
  | add {e f : RadExpr} {x y : L} : Value e x → Value f y → Value (.add e f) (x + y)
  | neg {e : RadExpr} {x : L} : Value e x → Value (.neg e) (-x)
  | mul {e f : RadExpr} {x y : L} : Value e x → Value f y → Value (.mul e f) (x * y)
  | inv {e : RadExpr} {x : L} : Value e x → Value (.inv e) x⁻¹
  | root {n : ℕ} {e : RadExpr} {x y : L} (hn : n ≠ 0) :
      Value e x → y ^ n = x → Value (.root n e) y

/-- **Abel–Ruffini, shared form.** No value of any formula in radicals is a root
of the generic quintic. -/
def QuinticUnsolvable : Prop :=
  ∀ (e : RadExpr) (y : L), Value e y → aeval y genericQuintic ≠ 0

end Quintic
