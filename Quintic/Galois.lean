module

public import Quintic.Statement

/-!
# The Galois-theoretic proof

Plan:
1. Every value of a radical expression lies in `solvableByRad K L` (done below).
2. `genericQuintic` is irreducible over `K` and its Galois group is `S₅`.
   This is the main missing input; Mathlib has `MvPolynomial.esymm` and
   symmetric-function machinery but, as far as we know, not this theorem.
3. `S₅` is not solvable (Mathlib: `Equiv.Perm.not_solvable`).
4. Mathlib's `isSolvable_gal_minpoly` says elements of `solvableByRad` have
   minimal polynomials with solvable Galois group. A root `y` of the generic
   quintic has minimal polynomial `genericQuintic`, so `y ∉ solvableByRad K L`.
-/

public section

open Polynomial

namespace Quintic

theorem value_mem_solvableByRad {e : RadExpr} {y : L} (h : Value e y) :
    y ∈ solvableByRad K L := by
  induction h with
  | var i => exact IntermediateField.algebraMap_mem _ _
  | const c => exact IntermediateField.algebraMap_mem _ _
  | add _ _ ihx ihy => exact add_mem ihx ihy
  | neg _ ih => exact neg_mem ih
  | mul _ _ ihx ihy => exact mul_mem ihx ihy
  | inv _ ih => exact inv_mem ih
  | root hn _ hy ih => exact solvableByRad.rad_mem hn (by rw [hy]; exact ih)

/-- Steps 2–4 of the plan. -/
theorem root_not_mem_solvableByRad {y : L} (hy : aeval y genericQuintic = 0) :
    y ∉ solvableByRad K L := by
  sorry

theorem quintic_unsolvable_galois : QuinticUnsolvable := by
  unfold QuinticUnsolvable
  intro e y he hroot
  exact root_not_mem_solvableByRad hroot (value_mem_solvableByRad he)

end Quintic
