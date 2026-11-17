/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Placement
import QICLean.Analysis.RootChannel
import QICLean.Channel.KrausCPTP

/-!
# The expectation onto a region

For a region `D` of a system of sites `X`, the region expectation
`E_D(A) = |X_{V∖D}|⁻¹ Tr_{V∖D}(A) ⊗ 1` is the normalized partial trace over the sites
outside `D`, placed back as an operator on all sites. It is the trace-preserving conditional
expectation onto the operators supported on `D`: its values are supported on `D`, it fixes
every operator supported on `D`, it is a bimodule map over them, and it is positive, unital
and contractive in operator norm.

These properties follow from one identity: `E_D(A) = ∑_p W_pᴴ A W_p`, where the `W_p` are
the operators `c^{-1/2} (1 ⊗ |y⟩⟨y'|)` for the configurations `y, y'` outside `D` and
`c = |X_{V∖D}|`. Each `W_p` acts as the identity on `D`, so it commutes with the operators
supported on `D`, and `∑_p W_pᴴ W_p = 1`.

No statement requires a basis type to be nonempty. If some basis type is empty, then the
system has no configurations, every matrix on it is zero, and the statements hold
trivially; this case is reduced once, by `IsEmpty (ComplConfig X D) → IsEmpty (Config X)`,
in the proofs of `ManyBody.regionExpectation_one` and `ManyBody.trace_regionExpectation`.

## Main definitions

* `ManyBody.regionExpectation` — the normalized partial trace onto a region.

## Main results

* `ManyBody.regionExpectation_apply` — the entries of the region expectation.
* `ManyBody.regionExpectation_mem_supportedOperators` — its values are supported on the
  region.
* `ManyBody.regionExpectation_mul_mul` — `E_D(B A C) = B E_D(A) C` for `B` and `C`
  supported on `D`.
* `ManyBody.regionExpectation_one`, `ManyBody.regionExpectation_of_mem_supportedOperators`,
  `ManyBody.regionExpectation_regionExpectation` — unitality, and idempotence onto the
  supported operators.
* `ManyBody.trace_regionExpectation`, `ManyBody.regionExpectation_conjTranspose`,
  `ManyBody.posSemidef_regionExpectation`, `ManyBody.regionExpectation_mono`,
  `ManyBody.norm_regionExpectation_le`.

## References

* The normalized partial trace onto a region is the expectation
  `E_K(B) = q^{-|Λ∖K|} Tr_{Λ∖K}(B) ⊗ 1_{Λ∖K}` of the quasi-local approximation in the
  two-dimensional area-law manuscript (`03-quasilocal.tex`, lines 19–25, `eq:quasilocal-ce`),
  there for one local dimension `q`; its properties as a conditional expectation are stated
  in lines 27–29.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {D : Finset V}

/-- The region expectation `E_D(A) = |X_{V∖D}|⁻¹ Tr_{V∖D}(A) ⊗ 1`: the partial trace of `A`
over the sites outside `D`, divided by the number of configurations outside `D` and placed
back on all sites.

Area-law manuscript, `03-quasilocal.tex`, lines 19–25 (`eq:quasilocal-ce`). -/
noncomputable def regionExpectation (D : Finset V) (A : Matrix (Config X) (Config X) ℂ) :
    Matrix (Config X) (Config X) ℂ :=
  (Fintype.card (ComplConfig X D) : ℂ)⁻¹ • place D (Matrix.of fun a b ↦
    ∑ y : ComplConfig X D, A ((cutEquiv X D).symm (a, y)) ((cutEquiv X D).symm (b, y)))

/-- Entries of the region expectation: `E_D(A)_{στ}` vanishes unless `σ` and `τ` agree
outside `D`, and is then the average over the configurations `y` outside `D` of the entries
of `A` at the parts of `σ` and `τ` on `D`, completed by `y`. -/
theorem regionExpectation_apply (D : Finset V) (A : Matrix (Config X) (Config X) ℂ)
    (σ τ : Config X) :
    regionExpectation D A σ τ = (Fintype.card (ComplConfig X D) : ℂ)⁻¹ *
      if ∀ v ∉ D, σ v = τ v then
        ∑ y : ComplConfig X D, A ((cutEquiv X D).symm ((cutEquiv X D σ).1, y))
          ((cutEquiv X D).symm ((cutEquiv X D τ).1, y))
      else 0 := by
  rw [regionExpectation, Matrix.smul_apply, place_apply, smul_eq_mul]
  rfl

/-- The values of the region expectation are supported on the region. -/
theorem regionExpectation_mem_supportedOperators (D : Finset V)
    (A : Matrix (Config X) (Config X) ℂ) :
    regionExpectation D A ∈ supportedOperators X D :=
  Subalgebra.smul_mem _ (place_mem_supportedOperators _) _

/-! ### The conjugation formula -/

section Conjugation

/-- The partial trace in cut coordinates is a sum of conjugations by `1 ⊗ |y⟩⟨y'|`. -/
private theorem sum_one_kronecker_single_mul_mul {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (M : Matrix (α × β) (α × β) ℂ) :
    ∑ y : β, ∑ y' : β, ((1 : Matrix α α ℂ) ⊗ₖ single y' y (1 : ℂ)) * M *
      ((1 : Matrix α α ℂ) ⊗ₖ single y y' (1 : ℂ)) =
      (Matrix.of fun a b ↦ ∑ y, M (a, y) (b, y)) ⊗ₖ (1 : Matrix β β ℂ) := by
  ext ⟨a, z⟩ ⟨b, z'⟩
  simp [Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
    one_apply, single_apply, ite_and, mul_ite, ite_mul, Finset.sum_ite_eq, eq_comm]

/-- The operator `c^{-1/2} (1 ⊗ |y⟩⟨y'|)` of the conjugation formula, for configurations
`y, y'` outside the region and `c` the number of such configurations. -/
private noncomputable def conjOp (D : Finset V) (p : ComplConfig X D × ComplConfig X D) :
    Matrix (Config X) (Config X) ℂ :=
  ((Real.sqrt (Fintype.card (ComplConfig X D)) : ℂ))⁻¹ •
    reindex (cutEquiv X D).symm (cutEquiv X D).symm
      ((1 : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) ⊗ₖ single p.1 p.2 (1 : ℂ))

private theorem conjOp_conjTranspose (p : ComplConfig X D × ComplConfig X D) :
    (conjOp D p)ᴴ = conjOp D (p.2, p.1) := by
  rw [conjOp, conjOp, conjTranspose_smul, star_inv₀, Complex.star_def, Complex.conj_ofReal,
    reindex_apply, conjTranspose_submatrix, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_single, star_one, reindex_apply]

private theorem sqrt_inv_mul_sqrt_inv (c : ℕ) :
    ((Real.sqrt c : ℂ))⁻¹ * ((Real.sqrt c : ℂ))⁻¹ = (c : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg c),
    Complex.ofReal_natCast]

/-- **The conjugation formula.** `E_D(A) = ∑_p W_pᴴ A W_p`. -/
private theorem regionExpectation_eq_sum_conj (A : Matrix (Config X) (Config X) ℂ) :
    regionExpectation D A = ∑ p, (conjOp D p)ᴴ * A * conjOp D p := by
  set e := cutEquiv X D
  set c := Fintype.card (ComplConfig X D)
  have hmul : ∀ M N : Matrix (RegionConfig X D × ComplConfig X D)
      (RegionConfig X D × ComplConfig X D) ℂ,
      reindex e.symm e.symm (M * N) = reindex e.symm e.symm M * reindex e.symm e.symm N :=
    fun M N ↦ by rw [← coe_reindexAlgEquiv ℂ ℂ, map_mul]
  have hsum : ∀ (s : Finset (ComplConfig X D × ComplConfig X D))
      (f : ComplConfig X D × ComplConfig X D →
        Matrix (RegionConfig X D × ComplConfig X D) (RegionConfig X D × ComplConfig X D) ℂ),
      reindex e.symm e.symm (∑ p ∈ s, f p) = ∑ p ∈ s, reindex e.symm e.symm (f p) :=
    fun s f ↦ by rw [← coe_reindexAlgEquiv ℂ ℂ, map_sum]
  have hA : reindex e.symm e.symm (reindex e e A) = A := by simp
  have hterm : ∀ p : ComplConfig X D × ComplConfig X D,
      (conjOp D p)ᴴ * A * conjOp D p = (c : ℂ)⁻¹ • reindex e.symm e.symm
        (((1 : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) ⊗ₖ single p.2 p.1 (1 : ℂ)) *
          reindex e e A *
            ((1 : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) ⊗ₖ single p.1 p.2 (1 : ℂ))) := by
    intro p
    rw [conjOp_conjTranspose, conjOp, conjOp, hmul, hmul, hA, ← sqrt_inv_mul_sqrt_inv]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rfl
  rw [Finset.sum_congr rfl fun p _ ↦ hterm p, ← Finset.smul_sum, ← hsum]
  simp only [Fintype.sum_prod_type]
  rw [sum_one_kronecker_single_mul_mul, regionExpectation, place]
  rfl

/-- Each operator of the conjugation formula acts as the identity on the region, so it
commutes with the placements on the region. -/
private theorem commute_conjOp_place (p : ComplConfig X D × ComplConfig X D)
    (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    Commute (conjOp D p) (place D K) := by
  refine Commute.smul_left ?_ _
  rw [place, ← coe_reindexAlgEquiv ℂ ℂ]
  refine Commute.map ?_ _
  change _ * _ = _ * _
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_one]

private theorem commute_conjOp_of_mem {B : Matrix (Config X) (Config X) ℂ}
    (hB : B ∈ supportedOperators X D) (p : ComplConfig X D × ComplConfig X D) :
    Commute (conjOp D p) B := by
  obtain ⟨K, rfl⟩ := exists_eq_place_of_mem_supportedOperators hB
  exact commute_conjOp_place p K

end Conjugation

/-! ### Conditional-expectation properties -/

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- If there is no configuration outside `D`, there is no configuration at all. -/
private theorem isEmpty_config_of_isEmpty_complConfig [IsEmpty (ComplConfig X D)] :
    IsEmpty (Config X) := by
  classical
  exact (cutEquiv X D).isEmpty_congr.mpr inferInstance

theorem regionExpectation_zero :
    regionExpectation D (0 : Matrix (Config X) (Config X) ℂ) = 0 := by
  simp [regionExpectation_eq_sum_conj]

theorem regionExpectation_add (A B : Matrix (Config X) (Config X) ℂ) :
    regionExpectation D (A + B) = regionExpectation D A + regionExpectation D B := by
  simp only [regionExpectation_eq_sum_conj, Matrix.mul_add, Matrix.add_mul,
    Finset.sum_add_distrib]

theorem regionExpectation_smul (c : ℂ) (A : Matrix (Config X) (Config X) ℂ) :
    regionExpectation D (c • A) = c • regionExpectation D A := by
  simp only [regionExpectation_eq_sum_conj, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem regionExpectation_sub (A B : Matrix (Config X) (Config X) ℂ) :
    regionExpectation D (A - B) = regionExpectation D A - regionExpectation D B := by
  simp only [regionExpectation_eq_sum_conj, Matrix.mul_sub, Matrix.sub_mul,
    Finset.sum_sub_distrib]

/-- The region expectation commutes with adjoints. -/
theorem regionExpectation_conjTranspose (A : Matrix (Config X) (Config X) ℂ) :
    regionExpectation D Aᴴ = (regionExpectation D A)ᴴ := by
  simp only [regionExpectation_eq_sum_conj, conjTranspose_sum, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The region expectation of a Hermitian operator is Hermitian. -/
theorem isHermitian_regionExpectation {A : Matrix (Config X) (Config X) ℂ}
    (hA : A.IsHermitian) : (regionExpectation D A).IsHermitian :=
  hA.apply_of_map_conjTranspose regionExpectation_conjTranspose

/-- The region expectation as a linear map, for the statements about linear maps of matrices
(conditional generators, Bochner integrals). Statements about the region expectation are
written with `ManyBody.regionExpectation`. -/
noncomputable def regionExpectationLM (D : Finset V) :
    Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config X) (Config X) ℂ where
  toFun := regionExpectation D
  map_add' := regionExpectation_add
  map_smul' := regionExpectation_smul

@[simp]
theorem regionExpectationLM_apply (D : Finset V) (A : Matrix (Config X) (Config X) ℂ) :
    regionExpectationLM D A = regionExpectation D A :=
  rfl

/-- The region expectation as a continuous linear map, in the operator norm. -/
noncomputable def regionExpectationCLM (D : Finset V) :
    Matrix (Config X) (Config X) ℂ →L[ℂ] Matrix (Config X) (Config X) ℂ :=
  LinearMap.toContinuousLinearMap (regionExpectationLM D)

@[simp]
theorem regionExpectationCLM_apply (D : Finset V) (A : Matrix (Config X) (Config X) ℂ) :
    regionExpectationCLM D A = regionExpectation D A :=
  rfl

/-- **Bimodule property.** For `B` and `C` supported on `D`, `E_D(B A C) = B E_D(A) C`. -/
theorem regionExpectation_mul_mul {A B C : Matrix (Config X) (Config X) ℂ}
    (hB : B ∈ supportedOperators X D) (hC : C ∈ supportedOperators X D) :
    regionExpectation D (B * A * C) = B * regionExpectation D A * C := by
  rw [regionExpectation_eq_sum_conj, regionExpectation_eq_sum_conj, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hBp : Commute (conjOp D p)ᴴ B := by
    rw [conjOp_conjTranspose]; exact commute_conjOp_of_mem hB _
  rw [show (conjOp D p)ᴴ * (B * A * C) * conjOp D p =
      ((conjOp D p)ᴴ * B) * A * (C * conjOp D p) by simp only [Matrix.mul_assoc],
    hBp.eq, (commute_conjOp_of_mem hC p).eq.symm]
  simp only [Matrix.mul_assoc]

/-- The region expectation is unital. -/
@[simp]
theorem regionExpectation_one :
    regionExpectation D (1 : Matrix (Config X) (Config X) ℂ) = 1 := by
  cases isEmpty_or_nonempty (ComplConfig X D) with
  | inl h =>
    have := isEmpty_config_of_isEmpty_complConfig (X := X) (D := D)
    exact Subsingleton.elim _ _
  | inr h =>
    have hc : (Fintype.card (ComplConfig X D) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hK : (Matrix.of fun a b : RegionConfig X D ↦ ∑ y : ComplConfig X D,
        (1 : Matrix (Config X) (Config X) ℂ) ((cutEquiv X D).symm (a, y))
          ((cutEquiv X D).symm (b, y))) = (Fintype.card (ComplConfig X D) : ℂ) • 1 := by
      ext a b
      simp only [of_apply, one_apply, (cutEquiv X D).symm.injective.eq_iff, Prod.mk.injEq,
        Matrix.smul_apply, smul_eq_mul]
      by_cases hab : a = b <;> simp [hab]
    rw [regionExpectation, hK, place_smul, place_one, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The region expectation fixes every operator supported on the region. -/
theorem regionExpectation_of_mem_supportedOperators {B : Matrix (Config X) (Config X) ℂ}
    (hB : B ∈ supportedOperators X D) : regionExpectation D B = B := by
  have h := regionExpectation_mul_mul (A := 1) hB (one_mem (supportedOperators X D))
  simpa using h

/-- The region expectation is idempotent. -/
@[simp]
theorem regionExpectation_regionExpectation (A : Matrix (Config X) (Config X) ℂ) :
    regionExpectation D (regionExpectation D A) = regionExpectation D A :=
  regionExpectation_of_mem_supportedOperators (regionExpectation_mem_supportedOperators D A)

/-- The region expectation preserves the trace. -/
theorem trace_regionExpectation (A : Matrix (Config X) (Config X) ℂ) :
    (regionExpectation D A).trace = A.trace := by
  cases isEmpty_or_nonempty (ComplConfig X D) with
  | inl h =>
    have := isEmpty_config_of_isEmpty_complConfig (X := X) (D := D)
    simp [Matrix.trace]
  | inr h =>
    have hc : (Fintype.card (ComplConfig X D) : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [regionExpectation, trace_smul, trace_place, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hc, one_mul]
    simp only [Matrix.trace, diag_apply, of_apply]
    rw [← Fintype.sum_prod_type', ← (cutEquiv X D).symm.sum_comp]

/-- The region expectation of a positive semidefinite operator is positive semidefinite. -/
theorem posSemidef_regionExpectation {A : Matrix (Config X) (Config X) ℂ} (hA : A.PosSemidef) :
    (regionExpectation D A).PosSemidef := by
  rw [regionExpectation_eq_sum_conj]
  exact posSemidef_sum _ fun p _ ↦ hA.conjTranspose_mul_mul_same _

/-- The region expectation is monotone. -/
theorem regionExpectation_mono {A B : Matrix (Config X) (Config X) ℂ} (h : A ≤ B) :
    regionExpectation D A ≤ regionExpectation D B := by
  rw [Matrix.le_iff, ← regionExpectation_sub]
  exact posSemidef_regionExpectation (Matrix.le_iff.mp h)

/-- The region expectation is a contraction in operator norm. -/
theorem norm_regionExpectation_le (A : Matrix (Config X) (Config X) ℂ) :
    ‖regionExpectation D A‖ ≤ ‖A‖ := by
  have hW : ∑ p, (conjOp (X := X) D p)ᴴ * conjOp D p = 1 := by
    simpa only [Matrix.mul_one] using
      (regionExpectation_eq_sum_conj (X := X) (D := D) 1).symm.trans
        regionExpectation_one
  rw [regionExpectation_eq_sum_conj]
  exact norm_sum_conjTranspose_mul_mul_le _ hW A

/-- **Best approximation up to a factor two.** For any `A₀` supported on `D`,
`‖A - E_D(A)‖ ≤ 2 ‖A - A₀‖`. -/
theorem norm_sub_regionExpectation_le_two_mul_norm_sub (D : Finset V)
    (A A₀ : Matrix (Config X) (Config X) ℂ) (hA₀ : A₀ ∈ supportedOperators X D) :
    ‖A - regionExpectation D A‖ ≤ 2 * ‖A - A₀‖ := by
  have h : A - regionExpectation D A = (A - A₀) - regionExpectation D (A - A₀) := by
    rw [regionExpectation_sub, regionExpectation_of_mem_supportedOperators hA₀]
    abel
  rw [h]
  calc
    _ ≤ ‖A - A₀‖ + ‖regionExpectation D (A - A₀)‖ := norm_sub_le _ _
    _ ≤ ‖A - A₀‖ + ‖A - A₀‖ := add_le_add le_rfl (norm_regionExpectation_le _)
    _ = 2 * ‖A - A₀‖ := by ring

/-- **The region expectation is a trace-preserving completely positive map.** Its Kraus
operators are the adjoints of the operators `c^{-1/2} (1 ⊗ |y⟩⟨y'|)` of the conjugation formula,
for the configurations `y, y'` outside the region. -/
theorem regionExpectationLM_isKrausCPTP (D : Finset V) :
    IsKrausCPTP (regionExpectationLM (X := X) D) := by
  classical
  let e := Fintype.equivFin (ComplConfig X D × ComplConfig X D)
  refine ⟨Fintype.card (ComplConfig X D × ComplConfig X D), fun i ↦ (conjOp D (e.symm i))ᴴ,
    fun A ↦ ?_, ?_⟩
  · rw [regionExpectationLM_apply, regionExpectation_eq_sum_conj]
    simp only [conjTranspose_conjTranspose]
    exact (e.symm.sum_comp fun p ↦ (conjOp D p)ᴴ * A * conjOp D p).symm
  · have hW : ∑ p, (conjOp (X := X) D p)ᴴ * conjOp D p = 1 := by
      simpa only [Matrix.mul_one] using
        (regionExpectation_eq_sum_conj (X := X) (D := D) 1).symm.trans regionExpectation_one
    simp only [conjTranspose_conjTranspose]
    rw [e.symm.sum_comp fun p ↦ conjOp D p * (conjOp D p)ᴴ, ← hW]
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun p ↦ ?_
    rw [conjOp_conjTranspose, conjOp_conjTranspose]
    rfl

end ManyBody
