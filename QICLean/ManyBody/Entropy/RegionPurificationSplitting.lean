/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.Entropy.MutualInformation.PurificationSplitting
import QICLean.ManyBody.Sites.ThreeRegion.Birth

/-!
# Purification splitting for finite regions

For two disjoint regions of a normalized finite-product pure state, an isometry
acting on their complement separates the state into two unit purifications. The
error is bounded by the square root of the regional mutual information. Local
basis dimensions may vary, and all three regions may be empty.

The reduced density and regional mutual information are the existing finite-product
constructions. The proof identifies their coordinate representation and applies
Uhlmann's purification-overlap theorem through `PurificationSplitting`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Lemma 6.4 (`lem:splitting`), `05-frames.tex:352–391`;
  source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

These proofs were written independently; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/
build/sections/05-frames.tex
Labels: lem:splitting.
-/

open scoped Matrix ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- Coordinates for two disjoint regions and their complement. The first two
factors use their canonical finite enumerations.

Source: PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex:352–359`. -/
noncomputable def splitTwoRegionsEquiv (T E : Finset V) (h : Disjoint T E) :
    ((v : V) → β v) ≃
      (Fin (Fintype.card (RegionConfig β T)) × Fin
          (Fintype.card (RegionConfig β E))) ×
        ComplConfig β (T ∪ E) :=
  (cutEquiv β (T ∪ E)).trans
    (((regionUnionEquiv (β := β) h).trans
      ((Fintype.equivFin (RegionConfig β T)).prodCongr
        (Fintype.equivFin (RegionConfig β E)))).prodCongr (Equiv.refl _))

/-- The physical state expressed in the coordinates of two regions and their
complement. This is a change of basis indices, with no truncation.

Source: PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex:352–359`. -/
noncomputable def splitTwoRegionsState (ψ : EuclideanSpace ℂ ((v : V) → β v))
    (T E : Finset V) (h : Disjoint T E) :
    (Fin (Fintype.card (RegionConfig β T)) × Fin
        (Fintype.card (RegionConfig β E))) ×
        ComplConfig β (T ∪ E) → ℂ :=
  fun x ↦ ψ ((splitTwoRegionsEquiv β T E h).symm x)

omit [∀ v, DecidableEq (β v)] in
/-- The right marginal in these coordinates is precisely the existing joint
regional density matrix.

Source: PEPS manuscript, proof of Lemma 6.4, `05-frames.tex:371–375`. -/
theorem partialTraceRight_splitTwoRegionsState
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (T E : Finset V) (h : Disjoint T E) :
    Matrix.partialTraceRight (Matrix.vecMulVec (splitTwoRegionsState β ψ T E h)
      (star (splitTwoRegionsState β ψ T E h))) = jointMatrix β ψ T E h := by
  rfl

omit [∀ v, DecidableEq (β v)] in
/-- Coordinate decomposition preserves normalization of the full pure state.

Source: PEPS manuscript, proof of Lemma 6.4, `05-frames.tex:371–389`. -/
theorem splitTwoRegionsState_unit (ψ : EuclideanSpace ℂ ((v : V) → β v))
    (hψ : ‖ψ‖ = 1) (T E : Finset V) (h : Disjoint T E) :
    star (splitTwoRegionsState β ψ T E h) ⬝ᵥ splitTwoRegionsState β ψ T E h
        = 1 := by
  rw [← Matrix.trace_partialTraceRight_vecMulVec,
    partialTraceRight_splitTwoRegionsState]
  dsimp only [jointMatrix]
  rw [Matrix.trace_submatrix_equiv]
  exact trace_regionState_eq_one hψ (D := (T ∪ E))

/-- Splitting a finite-product pure state on two disjoint regions and their
complement. The isometry is defined on the entire complement space, including
unused directions. The two output vectors are unit, and the error bound uses the
actual regional mutual information. No Hamiltonian or dimension bound is assumed.

Source: PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex:352–391`. -/
theorem exists_isIsometry_splitTwoRegionsState_norm_sub_le
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (T E : Finset V) (h : Disjoint T E) :
    ∃ (W : Matrix
        (Fin (Fintype.card (RegionConfig β T)) ×
          (Fin (Fintype.card (RegionConfig β E)) ⊕ ComplConfig β (T ∪ E)))
        (ComplConfig β (T ∪ E)) ℂ)
      (s : Fin (Fintype.card (RegionConfig β T)) ×
        Fin (Fintype.card (RegionConfig β T)) → ℂ)
      (s' : Fin (Fintype.card (RegionConfig β E)) ×
        (Fin (Fintype.card (RegionConfig β E)) ⊕ ComplConfig β (T ∪ E)) → ℂ),
      W.IsIsometry ∧ star s ⬝ᵥ s = 1 ∧ star s' ⬝ᵥ s' = 1 ∧
      ‖WithLp.toLp 2 ((((1 : Matrix _ _ ℂ) ⊗ₖ W) *ᵥ
        splitTwoRegionsState β ψ T E h) - Matrix.tensorPurification s s')‖ ≤
        √(2 * (1 - Real.exp (-(regionMutualInformation ψ T E / 2)))) ∧
      √(2 * (1 - Real.exp (-(regionMutualInformation ψ T E / 2)))) ≤
        √(regionMutualInformation ψ T E) := by
  simpa only [regionMutualInformation_eq_matrix β ψ T E h] using
    Matrix.exists_isIsometry_norm_sub_tensorPurification_le_mutualInformation
      (splitTwoRegionsState β ψ T E h) (splitTwoRegionsState_unit β ψ hψ T E h)
      (partialTraceRight_splitTwoRegionsState β ψ T E h)
      (jointMatrix_posSemidef β ψ T E h).isHermitian

/-- A mutual-information bound of `L⁻⁶⁰` gives a regional splitting error of
`L⁻³⁰`, with unit output vectors and an isometry on the entire complement space.

Source: PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex:366–367`. -/
theorem exists_isIsometry_splitTwoRegionsState_norm_sub_le_zpow
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (T E : Finset V) (h : Disjoint T E)
    {L : ℝ} (hL : 0 < L) (hb : regionMutualInformation ψ T E ≤ L ^ (-60 : ℤ)) :
    ∃ (W : Matrix
        (Fin (Fintype.card (RegionConfig β T)) ×
          (Fin (Fintype.card (RegionConfig β E)) ⊕ ComplConfig β (T ∪ E)))
        (ComplConfig β (T ∪ E)) ℂ)
      (s : Fin (Fintype.card (RegionConfig β T)) ×
        Fin (Fintype.card (RegionConfig β T)) → ℂ)
      (s' : Fin (Fintype.card (RegionConfig β E)) ×
        (Fin (Fintype.card (RegionConfig β E)) ⊕ ComplConfig β (T ∪ E)) → ℂ),
      W.IsIsometry ∧ star s ⬝ᵥ s = 1 ∧ star s' ⬝ᵥ s' = 1 ∧
      ‖WithLp.toLp 2 ((((1 : Matrix _ _ ℂ) ⊗ₖ W) *ᵥ
        splitTwoRegionsState β ψ T E h) - Matrix.tensorPurification s s')‖ ≤
        L ^ (-30 : ℤ) := by
  simpa only [regionMutualInformation_eq_matrix β ψ T E h] using
    Matrix.exists_isIsometry_norm_sub_tensorPurification_le_zpow
      (splitTwoRegionsState β ψ T E h) (splitTwoRegionsState_unit β ψ hψ T E h)
      (partialTraceRight_splitTwoRegionsState β ψ T E h)
      (jointMatrix_posSemidef β ψ T E h).isHermitian hL
      (by simpa only [regionMutualInformation_eq_matrix β ψ T E h] using hb)

end ManyBody

/-!
### The splitting lemma in three-region coordinates

The splitting lemma above is stated in the coordinates `splitTwoRegionsEquiv` of two disjoint
regions. For regions `A ⊆ B`, with the three regions `A`, `B \ A` and `Bᶜ` of
`ManyBody.threeCutEquiv`, it provides splitting data `ManyBody.SplittingData X A B` whose error
on a unit vector `Ω` is at most `√(2 (1 - e^{-b/2})) ≤ √b` for `b = I_Ω(A : B \ A)`. The proof
identifies the reduced state of `Ω` on `B` in the coordinates `(A, B \ A)` and its two marginals
with the regional states, so that the relative entropy of the splitting estimate is the
regional mutual information.

For two disjoint regions `T` and `E`, take `A = T` and `B = T ∪ E`: then `B \ A = E`
(`Finset.union_sdiff_cancel_left`), and the hypothesis on `I_Ω(T : E)` is the one of the source.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator ComplexOrder

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {A B : Finset V} (hAB : A ⊆ B)

omit [Fintype V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- The configurations outside `A` are pairs of configurations on `B \ A` and outside `B`. -/
private def complEquivOfSubset :
    RegionConfig X (B \ A) × ComplConfig X B ≃ ComplConfig X A where
  toFun p v := if hB : v.1 ∈ B then p.1 ⟨v, Finset.mem_sdiff.2 ⟨hB, v.2⟩⟩ else p.2 ⟨v, hB⟩
  invFun c := (fun v ↦ c ⟨v, (Finset.mem_sdiff.1 v.2).2⟩, fun v ↦ c ⟨v, fun h ↦ v.2 (hAB h)⟩)
  left_inv p := by
    obtain ⟨y, z⟩ := p
    refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
    · simp [(Finset.mem_sdiff.1 v.2).1]
    · simp [v.2]
  right_inv c := by
    funext v
    by_cases hB : v.1 ∈ B <;> simp [hB]

omit [Fintype V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
include hAB in
/-- The configurations outside `B \ A` are pairs of configurations on `A` and outside `B`. -/
private def complEquivOfSdiff :
    RegionConfig X A × ComplConfig X B ≃ ComplConfig X (B \ A) where
  toFun p v := if hA : v.1 ∈ A then p.1 ⟨v, hA⟩ else
    p.2 ⟨v, fun hB ↦ v.2 (Finset.mem_sdiff.2 ⟨hB, hA⟩)⟩
  invFun c := (fun v ↦ c ⟨v, fun h ↦ (Finset.mem_sdiff.1 h).2 v.2⟩,
    fun v ↦ c ⟨v, fun h ↦ v.2 (Finset.mem_sdiff.1 h).1⟩)
  left_inv p := by
    obtain ⟨x, z⟩ := p
    refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
    · simp [v.2]
    · simp [show (v : V) ∉ A from fun h ↦ v.2 (hAB h)]
  right_inv c := by
    funext v
    by_cases hA : v.1 ∈ A <;> simp [hA]

omit [Fintype V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- Gluing `x` on `A` with the configuration outside `A` built from `(y, z)` is gluing
`((x, y), z)` in three-way coordinates. -/
private theorem cutEquiv_symm_complEquivOfSubset (x : RegionConfig X A)
    (y : RegionConfig X (B \ A)) (z : ComplConfig X B) :
    (cutEquiv X A).symm (x, complEquivOfSubset hAB (y, z)) =
      (threeCutEquiv X hAB).symm ((x, y), z) := by
  funext v
  by_cases hA : v ∈ A
  · rw [cutEquiv_symm_apply_mem _ _ hA, threeCutEquiv_symm_apply_of_mem hAB hA]
  · rw [cutEquiv_symm_apply_not_mem _ _ hA]
    by_cases hB : v ∈ B
    · rw [threeCutEquiv_symm_apply_of_mem_sdiff hAB (Finset.mem_sdiff.2 ⟨hB, hA⟩)]
      simp [complEquivOfSubset, hB]
    · rw [threeCutEquiv_symm_apply_of_not_mem hAB hB]
      simp [complEquivOfSubset, hB]

omit [Fintype V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- Gluing `y` on `B \ A` with the configuration outside `B \ A` built from `(x, z)` is gluing
`((x, y), z)` in three-way coordinates. -/
private theorem cutEquiv_symm_complEquivOfSdiff (x : RegionConfig X A)
    (y : RegionConfig X (B \ A)) (z : ComplConfig X B) :
    (cutEquiv X (B \ A)).symm (y, complEquivOfSdiff hAB (x, z)) =
      (threeCutEquiv X hAB).symm ((x, y), z) := by
  funext v
  by_cases hM : v ∈ B \ A
  · rw [cutEquiv_symm_apply_mem _ _ hM, threeCutEquiv_symm_apply_of_mem_sdiff hAB hM]
  · rw [cutEquiv_symm_apply_not_mem _ _ hM]
    by_cases hA : v ∈ A
    · rw [threeCutEquiv_symm_apply_of_mem hAB hA]
      simp [complEquivOfSdiff, hA]
    · have hB : v ∉ B := fun hB ↦ hM (Finset.mem_sdiff.2 ⟨hB, hA⟩)
      rw [threeCutEquiv_symm_apply_of_not_mem hAB hB]
      simp [complEquivOfSdiff, hA]

omit [∀ v, DecidableEq (X v)] in
/-- The reduced state of `Ω` on `B`, in the coordinates `(x, y)` of `A` and `B \ A`, is the
reduced state of the coordinate vector `splitVec hAB Ω`. -/
theorem partialTraceRight_splitVec (Ω : EuclideanSpace ℂ (Config X)) :
    partialTraceRight (vecMulVec (splitVec hAB Ω) (star (splitVec hAB Ω))) =
      (regionState Ω B).submatrix (subsetSplitEquiv X hAB).symm
        (subsetSplitEquiv X hAB).symm := by
  ext p p'
  simp only [partialTraceRight_apply, vecMulVec_apply, Pi.star_apply, regionState,
    submatrix_apply, regionMatrix_apply, splitVec, threeCutEquiv_eq_trans]
  rfl

omit [∀ v, DecidableEq (X v)] in
/-- The marginal on `A` of the reduced state of `Ω` on `B` is the reduced state on `A`. -/
theorem partialTraceRight_partialTraceRight_splitVec (Ω : EuclideanSpace ℂ (Config X)) :
    partialTraceRight (partialTraceRight
      (vecMulVec (splitVec hAB Ω) (star (splitVec hAB Ω)))) = regionState Ω A := by
  ext x x'
  simp only [partialTraceRight_apply, vecMulVec_apply, Pi.star_apply, regionState,
    regionMatrix_apply]
  rw [← Fintype.sum_prod_type', ← (complEquivOfSubset (X := X) hAB).sum_comp]
  refine Fintype.sum_congr _ _ fun p ↦ ?_
  rcases p with ⟨y, z⟩
  rw [cutEquiv_symm_complEquivOfSubset, cutEquiv_symm_complEquivOfSubset]

omit [∀ v, DecidableEq (X v)] in
/-- The marginal on `B \ A` of the reduced state of `Ω` on `B` is the reduced state on
`B \ A`. -/
theorem partialTraceLeft_partialTraceRight_splitVec (Ω : EuclideanSpace ℂ (Config X)) :
    partialTraceLeft (partialTraceRight
      (vecMulVec (splitVec hAB Ω) (star (splitVec hAB Ω)))) = regionState Ω (B \ A) := by
  ext y y'
  simp only [partialTraceLeft_apply, partialTraceRight_apply, vecMulVec_apply, Pi.star_apply,
    regionState, regionMatrix_apply]
  rw [← (complEquivOfSdiff (X := X) hAB).sum_comp fun c ↦
    Ω.ofLp ((cutEquiv X (B \ A)).symm (y, c)) * star (Ω.ofLp ((cutEquiv X (B \ A)).symm (y', c)))]
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rcases p with ⟨x, z⟩
  rw [cutEquiv_symm_complEquivOfSdiff, cutEquiv_symm_complEquivOfSdiff]

/-- The relative entropy of the reduced state of `Ω` on `B`, in the coordinates of `A` and
`B \ A`, with respect to the product of its marginals is the regional mutual information
`I_Ω(A : B \ A)` (Lemma 2.2 `lem:fidelity`, `01-preliminaries.tex`, lines 92–139). -/
theorem quantumRelativeEntropy_splitVec_eq_regionMutualInformation
    (Ω : EuclideanSpace ℂ (Config X))
    {ρ : Matrix (RegionConfig X A × RegionConfig X (B \ A))
      (RegionConfig X A × RegionConfig X (B \ A)) ℂ}
    (hρ : partialTraceRight (vecMulVec (splitVec hAB Ω) (star (splitVec hAB Ω))) = ρ) :
    quantumRelativeEntropy ρ (partialTraceRight ρ ⊗ₖ partialTraceLeft ρ) =
      regionMutualInformation Ω A (B \ A) := by
  subst hρ
  have hpsd := (posSemidef_vecMulVec_self_star (splitVec hAB Ω)).partialTraceRight
  rw [quantumRelativeEntropy_product_marginals hpsd,
    vonNeumannEntropy_congr (partialTraceRight_partialTraceRight_splitVec hAB Ω) _
      (regionState_isHermitian A Ω),
    vonNeumannEntropy_congr (partialTraceLeft_partialTraceRight_splitVec hAB Ω) _
      (regionState_isHermitian (B \ A) Ω),
    vonNeumannEntropy_congr (partialTraceRight_splitVec hAB Ω) _
      ((isHermitian_submatrix_equiv _).mpr (regionState_isHermitian B Ω)),
    vonNeumannEntropy_submatrix_equiv _ _ (regionState_isHermitian B Ω),
    regionMutualInformation, Finset.union_sdiff_of_subset hAB]
  rfl

/-- **Splitting consequence in three-region coordinates** (Lemma 6.4 `lem:splitting`). Let
`A ⊆ B` be regions, `U = Bᶜ`, and `b = I_Ω(A : B \ A)` for a unit vector `Ω`. There are
splitting data with `‖(1 ⊗ V) Ω - s ⊗ s'‖ ≤ √(2(1 - e^{-b/2})) ≤ √b`. No bound on the
dimensions is imposed.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 352–368. -/
theorem SplittingData.exists_error_le {Ω : EuclideanSpace ℂ (Config X)} (hΩ : ‖Ω‖ = 1) :
    ∃ σ : SplittingData X A B,
      σ.error hAB Ω ≤
        √(2 * (1 - Real.exp (-(regionMutualInformation Ω A (B \ A) / 2)))) ∧
      √(2 * (1 - Real.exp (-(regionMutualInformation Ω A (B \ A) / 2)))) ≤
        √(regionMutualInformation Ω A (B \ A)) := by
  obtain ⟨V, s, s', hV, hs, hs', hnorm⟩ :=
    exists_isIsometry_norm_sub_tensorPurification_le (splitVec hAB Ω)
      (star_splitVec_dotProduct_splitVec hAB hΩ) rfl
  refine ⟨⟨V, s, s', hV, hs, hs'⟩, ?_, Real.sqrt_two_mul_one_sub_exp_neg_half_le_sqrt _⟩
  rw [← quantumRelativeEntropy_splitVec_eq_regionMutualInformation hAB Ω rfl]
  exact hnorm

/-- **Splitting at a polynomially small mutual information** (Lemma 6.4 `lem:splitting`, last
sentence). If `I_Ω(A : B \ A) ≤ L^{-60}`, the splitting error is at most `L^{-30}`.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 366–367. -/
theorem SplittingData.exists_error_le_zpow {Ω : EuclideanSpace ℂ (Config X)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ} (hI : regionMutualInformation Ω A (B \ A) ≤ L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData X A B, σ.error hAB Ω ≤ L ^ (-30 : ℤ) := by
  obtain ⟨σ, h₁, h₂⟩ := SplittingData.exists_error_le hAB hΩ
  refine ⟨σ, h₁.trans (h₂.trans ?_)⟩
  have hsq : L ^ (-60 : ℤ) = (L ^ (-30 : ℤ)) ^ 2 := by
    rw [← zpow_natCast, ← _root_.zpow_mul]; norm_num
  rw [← Real.sqrt_sq (Even.zpow_nonneg ⟨-15, by norm_num⟩ L), ← hsq]
  exact Real.sqrt_le_sqrt hI

/-- **Splitting at a polynomially small mutual information, any exponent** (Lemma 6.4
`lem:splitting`, last sentence, and the splitting step of Lemmas `lem:birth` and `lem:exchange` of
the one-dimensional note, `part2b_mps_protocol.tex`, lines 70–158). For `0 ≤ L` and any real
exponent `p`, if `I_Ω(A : B \ A) ≤ L^{-2p}`, the splitting error is at most `L^{-p}`.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 366–367, there
with `p = 30`. -/
theorem SplittingData.exists_error_le_rpow {Ω : EuclideanSpace ℂ (Config X)} (hΩ : ‖Ω‖ = 1)
    {L p : ℝ} (hL : 0 ≤ L) (hI : regionMutualInformation Ω A (B \ A) ≤ L ^ (-(2 * p))) :
    ∃ σ : SplittingData X A B, σ.error hAB Ω ≤ L ^ (-p) := by
  obtain ⟨σ, h₁, h₂⟩ := SplittingData.exists_error_le hAB hΩ
  refine ⟨σ, h₁.trans (h₂.trans ?_)⟩
  have hsq : L ^ (-(2 * p)) = (L ^ (-p)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL]
    congr 1
    push_cast
    ring
  rw [← Real.sqrt_sq (Real.rpow_nonneg hL _), ← hsq]
  exact Real.sqrt_le_sqrt hI

end ManyBody
