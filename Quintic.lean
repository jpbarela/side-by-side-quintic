module

public import Quintic.Statement
public import Quintic.Galois
public import Quintic.Arnold

/-!
# Two proofs, one statement

Both theorems below have type `Quintic.QuinticUnsolvable`, so Lean itself
certifies that the Galois-theoretic and the topological proof establish
literally the same proposition.
-/

public section

namespace Quintic

theorem quintic_unsolvable_both : QuinticUnsolvable ∧ QuinticUnsolvable :=
  ⟨quintic_unsolvable_galois, quintic_unsolvable_arnold⟩

end Quintic
