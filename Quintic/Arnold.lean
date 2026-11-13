module

public import Quintic.Statement

/-!
# Arnold's topological proof

Plan:
1. Monodromy of the roots. Moving the five roots of a monic quintic around
   loops (and taking coefficients via Vieta) realizes every permutation, so the
   monodromy group of the roots over the space of coefficients with distinct
   roots is `S₅`.
2. Monodromy of radical expressions. Commutators of loops along which an
   expression returns to itself again return it to itself; by induction on
   `RadExpr`, iterated commutators eventually fix every branch. Hence radical
   expressions have solvable monodromy.
3. `S₅` has non-trivial iterated commutators (`A₅` is perfect), giving loops
   that fix every branch of `e` but move the roots.
4. Bridge (the point where the two proofs meet): relate `Value e y` in
   `AlgebraicClosure ℂ(a₀,…,a₄)` to germs of multivalued analytic functions of
   the coefficients, so that steps 1–3 apply. Alternatively, restate
   `QuinticUnsolvable` analytically and move the bridge to `Galois.lean`.
-/

public section

namespace Quintic

theorem quintic_unsolvable_arnold : QuinticUnsolvable := by
  sorry

end Quintic
