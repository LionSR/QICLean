/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaExcitationDecomposition
import QICLean.Analysis.ExcitationSubsetCounts
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Powerset

/-!
# Compression bounds from actual excitation components

For a vector in the spectral cutoff of the replica defect count, its actual
excitation components sum to that vector, and their squared norms sum to its
squared norm. A uniform quadratic-form bound on each retained component therefore
bounds the original quadratic form by the number of retained subsets times the
component bound. The positive operator need not commute with any excitation
projection.

The component estimate is an explicit hypothesis here. In particular, these
results do not assert the inverse-metric component estimate or the lower
comparison from the manuscript. They isolate the subsequent Cauchy--Schwarz and
subset-counting argument.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, `07-comparators.tex`, lines 577--590, immediately before and including
  `comparator:inverse-compression`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

section FiniteSum

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- Cauchy--Schwarz for the seminorm defined by a positive semidefinite matrix.
This is the finite-sum step preceding `comparator:inverse-compression` in
`07-comparators.tex`, lines 577--590. -/
theorem PosSemidef.re_dotProduct_sum_mulVec_le_card_sum
    {H : Matrix n n ℂ} (hH : H.PosSemidef) (s : Finset ι) (v : ι → n → ℂ) :
    (star (∑ i ∈ s, v i) ⬝ᵥ (H *ᵥ ∑ i ∈ s, v i)).re ≤
      (s.card : ℝ) * ∑ i ∈ s, (star (v i) ⬝ᵥ (H *ᵥ v i)).re := by
  let R := CFC.sqrt H
  have hR : Rᴴ = R := (CFC.sqrt_nonneg H).isSelfAdjoint.star_eq
  have hHGram : H = Rᴴ * R := by
    rw [hR]
    exact (CFC.sqrt_mul_sqrt_self H hH.nonneg).symm
  have hnorm (x : n → ℂ) :
      (star x ⬝ᵥ (H *ᵥ x)).re = ‖WithLp.toLp 2 (R *ᵥ x)‖ ^ 2 := by
    rw [hHGram, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    simpa only [PiLp.coe_symm_continuousLinearEquiv, RCLike.re_to_complex] using
      re_star_dotProduct_self_eq_norm_sq (R *ᵥ x)
  simp_rw [hnorm, mulVec_sum, WithLp.toLp_sum]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (norm_sum_le (E := EuclideanSpace ℂ n) s fun i => WithLp.toLp 2 (R *ᵥ v i)) 2).trans
    (sq_sum_le_card_mul_sum_sq (s := s)
      (f := fun i => ‖WithLp.toLp 2 (R *ᵥ v i)‖))

end FiniteSum

section Excitation

variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

local instance replicaExcitationCompression_decidableEqCopies (k : ℕ) :
    DecidableEq (Fin k → A) := Fintype.decidablePiFintype

/-- A uniform bound for the actual retained excitation components gives a bound
for a vector in the actual defect cutoff. The subset count is derived, and the
zero-copy and zero-fraction cases are included.
Source: `07-comparators.tex`, lines 577--590, `comparator:inverse-compression`.
The inverse-metric component estimate is not part of this conditional lemma. -/
theorem re_dotProduct_replicaDefectCutoff_le_of_component_bounds
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ)
    {τ c : ℝ} (hτ : 0 ≤ τ) (hτhalf : τ ≤ 1 / 2) (hc : 0 ≤ c)
    {H : Matrix ((Fin k → A) × C) ((Fin k → A) × C) ℂ}
    (hH : H.PosSemidef) (u : ((Fin k → A) × C) → ℂ)
    (hu : (cfc (fun r : ℝ => if r ≤ τ * k then 1 else 0)
      (replicaDefectCount Ω k) ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u = u)
    (hcomponent : ∀ B : Finset (Fin k), (B.card : ℝ) ≤ τ * k →
      let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u
      (star w ⬝ᵥ (H *ᵥ w)).re ≤ c * ‖WithLp.toLp 2 w‖ ^ 2) :
    (star u ⬝ᵥ (H *ᵥ u)).re ≤
      (((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c) *
        ‖WithLp.toLp 2 u‖ ^ 2 := by
  classical
  let I := Finset.univ.filter (fun B : Finset (Fin k) => (B.card : ℝ) ≤ τ * k)
  let w (B : Finset (Fin k)) :=
    (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u
  obtain ⟨hdecomp, hmass⟩ := replicaDefectCutoff_decomposition Ω hΩ k (τ * k) u hu
  have hdecomp' : u = ∑ B ∈ I, w B := hdecomp
  have hmass' : ∑ B : Finset (Fin k), ‖WithLp.toLp 2 (w B)‖ ^ 2 =
      ‖WithLp.toLp 2 u‖ ^ 2 := hmass
  have hretained : (∑ B ∈ I, ‖WithLp.toLp 2 (w B)‖ ^ 2) ≤
      ‖WithLp.toLp 2 u‖ ^ 2 := by
    rw [← hmass']
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
      (fun B _ _ => sq_nonneg _)
  have hcount : (I.card : ℝ) ≤
      ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) := by
    simpa only [I, Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_powerset_le_mul_exp_binEntropy
        (Finset.univ : Finset (Fin k)) hτ hτhalf
  calc
    (star u ⬝ᵥ (H *ᵥ u)).re =
        (star (∑ B ∈ I, w B) ⬝ᵥ (H *ᵥ ∑ B ∈ I, w B)).re := by
      rw [← hdecomp']
    _ ≤ (I.card : ℝ) * ∑ B ∈ I, (star (w B) ⬝ᵥ (H *ᵥ w B)).re :=
      hH.re_dotProduct_sum_mulVec_le_card_sum I w
    _ ≤ (I.card : ℝ) * ∑ B ∈ I, c * ‖WithLp.toLp 2 (w B)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun B hB => hcomponent B (Finset.mem_filter.mp hB).2)
        (Nat.cast_nonneg _)
    _ = (I.card : ℝ) * c * ∑ B ∈ I, ‖WithLp.toLp 2 (w B)‖ ^ 2 := by
      rw [← Finset.mul_sum, mul_assoc]
    _ ≤ (I.card : ℝ) * c * ‖WithLp.toLp 2 u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hretained (mul_nonneg (Nat.cast_nonneg _) hc)
    _ ≤ (((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c) *
        ‖WithLp.toLp 2 u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hc) (sq_nonneg _)

/-- Compression to any orthogonal subspace of the actual defect cutoff obeys
the subset-counting bound, provided the uniform component estimate holds for
vectors in that same subspace. No commutation of the positive operator with the
cutoff, the projection, or an individual excitation projection is required.

This is the conditional assembly at `comparator:inverse-compression`,
`07-comparators.tex`, lines 577--590. For the actual inverse metric, the component
estimate and the identification of the subspace must be proved separately. -/
theorem compression_le_of_replicaExcitationComponent_bounds
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ)
    {τ c : ℝ} (hτ : 0 ≤ τ) (hτhalf : τ ≤ 1 / 2) (hc : 0 ≤ c)
    {H P : Matrix ((Fin k → A) × C) ((Fin k → A) × C) ℂ}
    (hH : H.PosSemidef) (hP : IsStarProjection P)
    (hcut : (cfc (fun r : ℝ => if r ≤ τ * k then 1 else 0)
      (replicaDefectCount Ω k) ⊗ₖ (1 : Matrix C C ℂ)) * P = P)
    (hcomponent : ∀ u : ((Fin k → A) × C) → ℂ, P *ᵥ u = u →
      ∀ B : Finset (Fin k), (B.card : ℝ) ≤ τ * k →
      let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u
      (star w ⬝ᵥ (H *ᵥ w)).re ≤ c * ‖WithLp.toLp 2 w‖ ^ 2) :
    P * H * P ≤ (((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c) • P := by
  let L := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c
  have hPH : P.IsHermitian := hP.isSelfAdjoint.isHermitian
  have hleft : (P * H * P).IsHermitian := by
    simpa only [hPH.eq] using (hH.conjTranspose_mul_mul_same P).isHermitian
  have hright : (L • P).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, hPH.eq]
    simp
  have hdiff := hright.sub hleft
  apply Matrix.le_iff.mpr
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hdiff
  intro x
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hdiff.im_star_dotProduct_mulVec_self x).symm⟩
  have hPx : P *ᵥ (P *ᵥ x) = P *ᵥ x := by
    rw [mulVec_mulVec, hP.isIdempotentElem.eq]
  have hcutx : (cfc (fun r : ℝ => if r ≤ τ * k then 1 else 0)
      (replicaDefectCount Ω k) ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ (P *ᵥ x) = P *ᵥ x := by
    rw [mulVec_mulVec, hcut]
  have hbound := re_dotProduct_replicaDefectCutoff_le_of_component_bounds
    Ω hΩ k hτ hτhalf hc hH (P *ᵥ x) hcutx (hcomponent (P *ᵥ x) hPx)
  have hpair : star x ⬝ᵥ ((P * H * P) *ᵥ x) =
      star (P *ᵥ x) ⬝ᵥ (H *ᵥ (P *ᵥ x)) := by
    rw [hPH.star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec]
  have hnorm : (star x ⬝ᵥ (P *ᵥ x)).re = ‖WithLp.toLp 2 (P *ᵥ x)‖ ^ 2 := by
    have heq : star (P *ᵥ x) ⬝ᵥ (P *ᵥ x) = star x ⬝ᵥ (P *ᵥ x) := by
      rw [hPH.star_mulVec_dotProduct, hPx]
    rw [← heq]
    simpa only [PiLp.coe_symm_continuousLinearEquiv, RCLike.re_to_complex] using
      re_star_dotProduct_self_eq_norm_sq (P *ᵥ x)
  simpa only [sub_mulVec, dotProduct_sub, Complex.sub_re, smul_mulVec,
    dotProduct_smul, Complex.smul_re, smul_eq_mul, hpair, hnorm, sub_nonneg, L] using hbound

end Excitation
end Matrix
