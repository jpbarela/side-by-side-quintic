module

public import Quintic.Statement

/-!
# The Galois-theoretic proof

Plan:
1. Every value of a radical expression lies in `solvableByRad K L`.
2. `genericQuintic` is irreducible over `K` and its Galois group contains `S₅`.
3. `S₅` is not solvable (Mathlib: `Equiv.Perm.not_isSolvable`).
4. Mathlib's `isSolvable_gal_minpoly` says elements of `solvableByRad` have
   minimal polynomials with solvable Galois group. A root `y` of the generic
   quintic has minimal polynomial `genericQuintic`, so `y ∉ solvableByRad K L`.

## Step 2: the universal splitting field

Let `x₀, …, x₄` be fresh indeterminates, `S = ℂ[x₀, …, x₄]` and `E = Frac S`.
Sending `aᵢ ↦ e₅₋ᵢ(x)` (elementary symmetric polynomial) is injective by the
fundamental theorem of symmetric polynomials, so it makes `E` a `K`-algebra,
and over `E` the generic quintic factors as `∏ⱼ (X + xⱼ)`.
Permuting the `xⱼ` fixes every `e₅₋ᵢ(x)`, so it gives automorphisms of `E` over `K`
that permute the roots `-xⱼ` in every possible way. This shows:
* `S₅` embeds in the Galois group of `genericQuintic`;
* every root of an irreducible factor of `genericQuintic` is conjugate to every
  `-xⱼ`, so that factor has degree `5`, i.e. `genericQuintic` is irreducible.
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

namespace Generic

/-- Index type for the roots. A synonym of `Fin 5`, kept distinct so that
`MvPolynomial Idx ℂ` is not syntactically the coefficient ring `R`. -/
@[expose] def Idx : Type := Fin 5

instance : Fintype Idx := inferInstanceAs (Fintype (Fin 5))
instance : DecidableEq Idx := inferInstanceAs (DecidableEq (Fin 5))

theorem card_Idx : Fintype.card Idx = 5 := Fintype.card_fin 5

/-- Polynomials in the roots `x₀, …, x₄`. -/
abbrev S : Type := MvPolynomial Idx ℂ

/-- The universal splitting field `ℂ(x₀, …, x₄)`. -/
abbrev E : Type := FractionRing S

/-- `aᵢ ↦ e₅₋ᵢ(x)`. -/
noncomputable def φ : R →ₐ[ℂ] S :=
  MvPolynomial.aeval fun i : Fin 5 => MvPolynomial.esymm Idx ℂ (5 - i)

theorem φ_X (i : Fin 5) : φ (MvPolynomial.X i) = MvPolynomial.esymm Idx ℂ (5 - i) :=
  MvPolynomial.aeval_X _ _

theorem φ_injective : Function.Injective φ := by
  have h : φ = (Subalgebra.val _).comp
      ((MvPolynomial.esymmAlgHom Idx ℂ 5).comp (MvPolynomial.rename Fin.rev)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [φ_X, AlgHom.comp_apply, MvPolynomial.rename_X, Subalgebra.coe_val,
      MvPolynomial.esymmAlgHom_apply, MvPolynomial.aeval_X, Fin.val_rev]
    congr 1
    have := i.isLt
    omega
  rw [h]
  exact Subtype.val_injective.comp
    ((MvPolynomial.esymmAlgHom_injective (σ := Idx) (R := ℂ) (n := 5) card_Idx.ge).comp
      (MvPolynomial.rename_injective _ Fin.rev_injective))

/-! ### Algebra structures: `R → S → E` and `R → K → E` -/

noncomputable instance : Algebra R S := φ.toRingHom.toAlgebra

theorem algebraMap_R_S : algebraMap R S = φ.toRingHom := rfl

instance : FaithfulSMul R E :=
  (faithfulSMul_iff_algebraMap_injective R E).mpr
    ((IsFractionRing.injective S E).comp φ_injective)

noncomputable instance : Algebra K E := FractionRing.liftAlgebra R E

instance : IsScalarTower R K E := FractionRing.isScalarTower_liftAlgebra R E

/-- The roots `-xⱼ ∈ E`. -/
noncomputable def root (j : Idx) : E := -algebraMap S E (MvPolynomial.X j)

theorem root_injective : Function.Injective root := fun i j h => by
  simpa [root] using h

theorem algebraMap_a (i : Fin 5) :
    algebraMap K E (a i) = algebraMap S E (MvPolynomial.esymm Idx ℂ (5 - i)) := by
  rw [a, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S E,
    algebraMap_R_S, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, φ_X]

/-- Over `E` the generic quintic is `∏ⱼ (X - (-xⱼ))`. -/
theorem map_genericQuintic :
    genericQuintic.map (algebraMap K E) = ∏ j, (X - C (root j)) := by
  have h := congrArg (Polynomial.map (algebraMap S E))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm (σ := Idx) (R := ℂ))
  simp only [Polynomial.map_prod, Polynomial.map_add, map_X,
    map_C, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, card_Idx] at h
  rw [Finset.prod_congr rfl fun j _ => (by rw [root, map_neg, sub_neg_eq_add] :
    X - C (root j) = X + C (algebraMap S E (MvPolynomial.X j))), h,
    ← Finset.sum_range_reflect]
  simp only [genericQuintic, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
    Polynomial.map_mul, map_C, algebraMap_a, Finset.sum_range_succ (n := 5),
    Fin.sum_univ_eq_sum_range (fun i => C (algebraMap S E (MvPolynomial.esymm Idx ℂ (5 - i))) *
      X ^ i) 5]
  rw [add_comm (X ^ 5)]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j hj => ?_) (by simp)
  have hj := Finset.mem_range.mp hj
  rw [show 5 + 1 - 1 - j = 5 - j by omega, show 5 - (5 - j) = j by omega]


theorem genericQuintic_eq_map_freeMonic :
    genericQuintic = (freeMonic ℂ 5).map (algebraMap R K) := by
  simp [genericQuintic, freeMonic, Polynomial.map_sum, a]

theorem genericQuintic_monic : genericQuintic.Monic := by
  rw [genericQuintic_eq_map_freeMonic]
  exact Polynomial.Monic.map (algebraMap R K) (monic_freeMonic ℂ 5)

theorem genericQuintic_natDegree : genericQuintic.natDegree = 5 := by
  rw [genericQuintic_eq_map_freeMonic, (monic_freeMonic ℂ 5).natDegree_map, natDegree_freeMonic]

theorem genericQuintic_ne_zero : genericQuintic ≠ 0 := genericQuintic_monic.ne_zero

instance factSplits : Fact ((genericQuintic.map (algebraMap K E)).Splits) :=
  ⟨by rw [map_genericQuintic]; exact Splits.prod fun j _ => Splits.X_sub_C _⟩

theorem aeval_root (j : Idx) : aeval (root j) genericQuintic = 0 := by
  rw [aeval_def, eval₂_eq_eval_map, map_genericQuintic, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)

theorem root_mem_rootSet (j : Idx) : root j ∈ genericQuintic.rootSet E :=
  mem_rootSet.mpr ⟨genericQuintic_ne_zero, aeval_root j⟩

/-! ### Permuting the roots -/

/-- Renaming variables by `σ` fixes the image of `R`, which consists of symmetric polynomials. -/
theorem rename_φ (σ : Equiv.Perm Idx) (r : R) : MvPolynomial.rename σ (φ r) = φ r := by
  have : (MvPolynomial.rename σ).comp φ = φ :=
    MvPolynomial.algHom_ext fun i => by
      simp only [AlgHom.comp_apply, φ_X]
      exact MvPolynomial.esymm_isSymmetric Idx ℂ _ σ
  exact DFunLike.congr_fun this r

/-- Renaming the roots by `σ`, as an automorphism of `S` over `R`. -/
@[expose] noncomputable def permAlgEquiv (σ : Equiv.Perm Idx) : S ≃ₐ[R] S :=
  AlgEquiv.ofRingEquiv (f := (MvPolynomial.renameEquiv ℂ σ).toRingEquiv) fun r => rename_φ σ r

theorem permAlgEquiv_apply (σ : Equiv.Perm Idx) (f : S) :
    permAlgEquiv σ f = MvPolynomial.rename σ f := rfl

noncomputable def permHom : Equiv.Perm Idx →* (S ≃ₐ[R] S) where
  toFun := permAlgEquiv
  map_one' := by
    ext f : 1
    simp [permAlgEquiv_apply]
  map_mul' σ τ := by
    ext f : 1
    simp [permAlgEquiv_apply, MvPolynomial.rename_rename, Equiv.Perm.coe_mul]

/-- `σ` acting on `E = ℂ(x₀, …, x₄)` over `K`. -/
noncomputable def autHom : Equiv.Perm Idx →* Gal(E/K) :=
  (IsFractionRing.fieldEquivOfAlgEquivHom K E).comp permHom

theorem autHom_root (σ : Equiv.Perm Idx) (j : Idx) : autHom σ (root j) = root (σ j) := by
  simp [autHom, permHom, root, permAlgEquiv_apply]

/-- `S₅` inside the Galois group of the generic quintic. -/
noncomputable def galHom : Equiv.Perm Idx →* genericQuintic.Gal :=
  (Gal.restrict genericQuintic E).comp autHom

theorem galHom_injective : Function.Injective galHom := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  ext j
  have h := Gal.restrict_smul (autHom σ) ⟨root j, root_mem_rootSet j⟩
  rw [show Gal.restrict genericQuintic E (autHom σ) = galHom σ from rfl, hσ, one_smul,
    autHom_root] at h
  simpa using (root_injective h).symm

theorem not_isSolvable_gal : ¬ Group.IsSolvable genericQuintic.Gal := fun h =>
  Equiv.Perm.not_isSolvable Idx (by simp [Cardinal.mk_fintype, card_Idx])
    (Group.isSolvable_of_isSolvable_injective galHom_injective)

end Generic

open Generic in
/-- Steps 2–4 of the plan. -/
theorem root_not_mem_solvableByRad {y : L} (hy : aeval y genericQuintic = 0) :
    y ∉ solvableByRad K L := by
  intro hmem
  have hint : IsIntegral K y := ⟨genericQuintic, genericQuintic_monic, by rwa [← aeval_def]⟩
  set q := minpoly K y with hq_def
  have hdvd : q ∣ genericQuintic := minpoly.dvd K y hy
  have hq0 : q.map (algebraMap K E) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hint)
  -- `q` has one of the roots `-xⱼ` as a root in `E`.
  obtain ⟨j₀, hj₀⟩ : ∃ j, aeval (root j) q = 0 := by
    have hmapdvd := Polynomial.map_dvd (algebraMap K E) hdvd
    have hsplit : (q.map (algebraMap K E)).Splits :=
      Splits.of_dvd factSplits.out (Polynomial.map_ne_zero genericQuintic_ne_zero) hmapdvd
    obtain ⟨z, hz⟩ := hsplit.exists_eval_eq_zero
      (by rw [degree_map]; exact (minpoly.degree_pos hint).ne')
    obtain ⟨g, hg⟩ := hmapdvd
    have hz' : eval z (genericQuintic.map (algebraMap K E)) = 0 := by
      rw [hg, eval_mul, hz, zero_mul]
    rw [map_genericQuintic, eval_prod, Finset.prod_eq_zero_iff] at hz'
    obtain ⟨j, -, hj⟩ := hz'
    refine ⟨j, ?_⟩
    have hzj : z = root j := by simpa [sub_eq_zero] using hj
    rw [aeval_def, eval₂_eq_eval_map, ← hzj]
    exact hz
  -- Applying automorphisms, every `-xⱼ` is a root of `q`.
  have hall (j : Idx) : aeval (root j) q = 0 := by
    have h := autHom_root (Equiv.swap j₀ j) j₀
    rw [Equiv.swap_apply_left] at h
    rw [← h, show (autHom (Equiv.swap j₀ j)) (root j₀) =
      ((autHom (Equiv.swap j₀ j) : E ≃ₐ[K] E) : E →ₐ[K] E) (root j₀) from rfl,
      aeval_algHom_apply, hj₀, map_zero]
  -- So `q` has degree at least `5`, hence `q = genericQuintic`.
  have hdeg : 5 ≤ q.natDegree := by
    calc 5 = (Finset.univ.image root).card := by
          rw [Finset.card_image_of_injective _ root_injective, Finset.card_univ, card_Idx]
      _ ≤ (q.map (algebraMap K E)).roots.toFinset.card := by
          refine Finset.card_le_card fun z hz => ?_
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
          rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, ← eval₂_eq_eval_map, ← aeval_def]
          exact hall j
      _ ≤ (q.map (algebraMap K E)).roots.card := Multiset.toFinset_card_le _
      _ ≤ (q.map (algebraMap K E)).natDegree := card_roots' _
      _ = q.natDegree := natDegree_map _
  have hq : genericQuintic = q :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) genericQuintic_monic hdvd
      (by rw [genericQuintic_natDegree]; exact hdeg)
  have hsolv := isSolvable_gal_minpoly hmem
  rw [← hq_def, ← hq] at hsolv
  exact not_isSolvable_gal hsolv

theorem quintic_unsolvable_galois : QuinticUnsolvable := by
  unfold QuinticUnsolvable
  intro e y he hroot
  exact root_not_mem_solvableByRad hroot (value_mem_solvableByRad he)

end Quintic
