/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.WeightedProjection
import QICLean.Analysis.ShiftedDensityTruncation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NoncommRing

/-!
# Spectral exponential weights and truncation excesses

Shifted exponential weights commute with the original spectral projections. Their low-energy
parts are contractive, and multiplication by the inverse weight bounds the high-energy
truncation excess. The resulting estimates apply to actual subspace restrictions.

These are supporting results for ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines873–886, and the proof of `t:ais`, lines1010–1024.
-/

section

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace Matrix

/-- Functional calculus for the real affine function x ↦ s(x-c).
Auxiliary to the weighted truncation argument for ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
private theorem IsHermitian.cfc_mul_sub_const
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (s c : ℝ) :
    cfc (fun x : ℝ ↦ s * (x - c)) A = s • (A - c • (1 : Matrix n n ℂ)) := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  rw [cfc_const_mul s _ A (hc _),
    cfc_sub (fun x : ℝ ↦ x) (fun _ : ℝ ↦ c) A (hc _) (hc _),
    cfc_id' ℝ A hA.isSelfAdjoint, cfc_const c A hA.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one]
end Matrix

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- The low part of the shifted exponential weight is contractive.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
private theorem norm_cfc_low_exponential_weight_le_one
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (s c : ℝ) (hs : 0 ≤ s) :
    ‖cfc (fun x : ℝ ↦ if c ≤ x then 0 else Real.exp (s * (x - c))) A‖ ≤ 1 := by
  refine norm_cfc_le zero_le_one fun x _ ↦ ?_
  by_cases hx : c ≤ x
  · simp only [ite_eq_left hx, norm_zero]
    exact zero_le_one
  · rw [ite_eq_right hx, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr (not_le.mp hx).le))
end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The shifted exponential is the functional calculus of its scalar
exponential. Auxiliary to the weighted truncation argument in ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
private theorem IsHermitian.exp_mul_sub_const_eq_cfc
    (hA : A.IsHermitian) (s c : ℝ) :
    NormedSpace.exp (s • (A - c • (1 : Matrix n n ℂ))) =
      cfc (fun x : ℝ ↦ Real.exp (s * (x - c))) A := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hself : IsSelfAdjoint (cfc (fun x : ℝ ↦ s * (x - c)) A) :=
    cfc_predicate _ A
  calc
    NormedSpace.exp (s • (A - c • (1 : Matrix n n ℂ))) =
        NormedSpace.exp (cfc (fun x : ℝ ↦ s * (x - c)) A) := by
      rw [hA.cfc_mul_sub_const s c]
    _ = cfc Real.exp (cfc (fun x : ℝ ↦ s * (x - c)) A) :=
      (CFC.real_exp_eq_normedSpace_exp hself).symm
    _ = cfc (fun x : ℝ ↦ Real.exp (s * (x - c))) A :=
      (cfc_comp' Real.exp (fun x : ℝ ↦ s * (x - c)) A
        Real.continuous_exp.continuousOn (hc _) hA.isSelfAdjoint).symm

/-- The low part of the actual shifted exponential weight equals its
strict-low scalar functional calculus. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
private theorem IsHermitian.exp_mul_sub_const_mul_lowProjection_eq_cfc
    (hA : A.IsHermitian) (s c : ℝ) :
    NormedSpace.exp (s • (A - c • (1 : Matrix n n ℂ))) *
        (1 - spectralProjectionGE A c) =
      cfc (fun x : ℝ ↦ if c ≤ x then 0 else Real.exp (s * (x - c))) A := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hI : (1 : Matrix n n ℂ) = cfc (fun _ : ℝ ↦ (1 : ℝ)) A := by
    rw [cfc_const (1 : ℝ) A hA.isSelfAdjoint, map_one]
  rw [hA.exp_mul_sub_const_eq_cfc s c, spectralProjectionGE, hI,
    ← cfc_sub (fun _ : ℝ ↦ (1 : ℝ))
      (fun x : ℝ ↦ if c ≤ x then 1 else 0) A (hc _) (hc _),
    ← _root_.cfc_mul _ _ A (hc _) (hc _)]
  congr 1
  funext x
  by_cases hx : c ≤ x
  · simp only [ite_eq_left hx, sub_self, mul_zero]
  · simp only [ite_eq_right hx, sub_zero, mul_one]

/-- The actual shifted exponential followed by its low spectral projection
is contractive for nonnegative time. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
theorem IsHermitian.norm_exp_mul_sub_const_mul_lowProjection_le_one
    (hA : A.IsHermitian) (s c : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp (s • (A - c • (1 : Matrix n n ℂ))) *
      (1 - spectralProjectionGE A c)‖ ≤ 1 := by
  rw [hA.exp_mul_sub_const_mul_lowProjection_eq_cfc s c]
  exact norm_cfc_low_exponential_weight_le_one A s c hs
end Matrix

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- The negative matrix exponential is a left inverse of the exponential.
Auxiliary to the weighted truncation argument of AKL14, arXiv:1406.3898,
Theorem lowspec, low70.tex, lines 1102–1168. -/
private theorem exp_neg_mul_exp_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) : NormedSpace.exp (-K) * NormedSpace.exp K = 1 := by
  have hK : K ∈ Metric.eball (0 : Matrix n n ℂ)
      (NormedSpace.expSeries ℂ (Matrix n n ℂ)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  let := NormedSpace.invertibleExpOfMemBall (𝕂 := ℂ) hK
  exact invOf_mul_self (NormedSpace.exp K)
end Matrix

namespace Matrix

/-- The actual exponential weight and original spectral cutoff satisfy
all commutation and inverse identities used in the weighted equation.
Commutation with the disconnected operator is derived from commutation
with the original regional Hamiltonian. Auxiliary to ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
theorem IsHermitian.regionalWeight_relations
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (X : Matrix n n ℂ) (hXA : Commute X A) (s c : ℝ) :
    let W := NormedSpace.exp (s • (A - c • (1 : Matrix n n ℂ)))
    let Winv := NormedSpace.exp (-(s • (A - c • (1 : Matrix n n ℂ))))
    let Q := spectralProjectionGE A c
    Commute W Q ∧ Commute X W ∧ Commute X Q ∧ Winv * W = 1 := by
  intro W Winv Q
  have hW : W = cfc (fun x : ℝ ↦ Real.exp (s * (x - c))) A :=
    hA.exp_mul_sub_const_eq_cfc s c
  refine ⟨?_, ?_, ?_, exp_neg_mul_exp_eq_one _⟩
  · rw [hW]
    exact cfc_commute_cfc _ (fun x : ℝ ↦ if c ≤ x then 1 else 0) A
  · rw [hW]
    exact (hXA.symm.cfc_real (fun x : ℝ ↦ Real.exp (s * (x - c)))).symm
  · exact (hXA.symm.cfc_real (fun x : ℝ ↦ if c ≤ x then 1 else 0)).symm
end Matrix

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- Compression by an orthogonal projection does not increase the norm of a
conjugated operator. Auxiliary to ALVV, arXiv:1602.08828v2, Theorem t:ais,
lines 1010–1024; no bound for the conjugated operator is assumed. -/
theorem norm_projection_conjugated_mul_projection_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q W Y Winv : Matrix n n ℂ) (hQ : IsStarProjection Q) :
    ‖Q * W * Y * Winv * Q‖ ≤ ‖W * Y * Winv‖ := by
  have hQnorm : ‖Q‖ ≤ 1 := IsStarProjection.norm_le Q hQ
  have hbound : ‖Q * (W * Y * Winv) * Q‖ ≤ 1 * ‖W * Y * Winv‖ * 1 :=
    norm_mul_le_of_le (norm_mul_le_of_le hQnorm le_rfl) hQnorm
  simpa only [one_mul, mul_one, mul_assoc] using hbound

/-- The forcing term is bounded by the conjugated operator times the low
part of the weight. Auxiliary to ALVV, arXiv:1602.08828v2, Theorem t:ais,
lines 1010–1024. The commuting weight and left-inverse identities are the
only additional algebraic hypotheses. -/
theorem norm_weighted_projection_forcing_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q W Y Winv : Matrix n n ℂ) (hQ : IsStarProjection Q)
    (hWQ : Commute W Q) (hInv : Winv * W = 1) :
    ‖W * Q * Y * (1 - Q)‖ ≤ ‖W * Y * Winv‖ * ‖W * (1 - Q)‖ := by
  have hfactor : W * Q * Y * (1 - Q) =
      (Q * (W * Y * Winv)) * (W * (1 - Q)) := by
    simpa only [mul_one, mul_assoc] using
      WeightedProjection.forcing_identity Y W Winv Q (1 : Matrix n n ℂ) hWQ hInv
  have hleft : ‖Q * (W * Y * Winv)‖ ≤ ‖W * Y * Winv‖ := by
    simpa only [one_mul] using
      norm_mul_le_of_le (IsStarProjection.norm_le Q hQ)
        (le_rfl : ‖W * Y * Winv‖ ≤ ‖W * Y * Winv‖)
  rw [hfactor]
  exact norm_mul_le_of_le hleft le_rfl
end Matrix

section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Real

/-- A shifted linear factor can be absorbed into an exponential weight.
This is a scalar consequence of the maximum of y exp(-y). -/
theorem sub_mul_exp_weight_le (s x t u : ℝ) (hs : 0 < s) :
    (x - t) * exp (-s * (x - u)) ≤ exp (-s * (t - u) - 1) / s := by
  apply (le_div_iff₀ hs).2
  have h := mul_le_mul_of_nonneg_right
    (mul_exp_neg_le_exp_neg_one (s * (x - t))) (exp_nonneg (-s * (t - u)))
  rw [mul_assoc, ← exp_add, ← exp_add] at h
  ring_nf at h ⊢
  exact h

/-- The positive part of the energy excess obeys the same exponential bound.
This is a scalar supporting estimate for AKL14, Theorem lowspec. -/
theorem posPart_sub_mul_exp_weight_le (s x t u : ℝ) (hs : 0 < s) :
    max (x - t) 0 * exp (-s * (x - u)) ≤ exp (-s * (t - u) - 1) / s := by
  rw [max_mul_of_nonneg _ _ (exp_nonneg _), zero_mul]
  exact max_le (sub_mul_exp_weight_le s x t u hs) (div_nonneg (exp_nonneg _) hs.le)
end Real

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- The exponentially weighted positive energy excess has a uniform norm bound.
This is a functional-calculus consequence of the scalar estimate supporting
AKL14, arXiv:1406.3898, Theorem lowspec, low70.tex, lines 1102–1168.
Its identification with an operator product is a separate statement. -/
private theorem norm_cfc_posPart_sub_exponential_weight_le
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (s t u : ℝ) (hs : 0 < s) :
    ‖cfc (fun x : ℝ ↦ max (x - t) 0 * Real.exp (-s * (x - u))) A‖ ≤
      Real.exp (-s * (t - u) - 1) / s := by
  refine norm_cfc_le (div_nonneg (Real.exp_nonneg _) hs.le) fun x _ ↦ ?_
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (le_max_right _ _) (Real.exp_nonneg _))]
  exact Real.posPart_sub_mul_exp_weight_le s x t u hs
end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The energy excess times the actual inverse exponential weight is the
functional calculus of the weighted positive part. Auxiliary to AKL14,
arXiv:1406.3898, Theorem lowspec, low70.tex, lines 1102–1168, and ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
private theorem IsHermitian.excess_mul_inverse_weight_eq_cfc
    (hA : A.IsHermitian) (s t u : ℝ) :
    (A - cfc (fun x : ℝ ↦ min x t) A) *
        NormedSpace.exp (-(s • (A - u • (1 : Matrix n n ℂ)))) =
      cfc (fun x : ℝ ↦ max (x - t) 0 * Real.exp (-s * (x - u))) A := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hexcess : A - cfc (fun x : ℝ ↦ min x t) A =
      cfc (fun x : ℝ ↦ max (x - t) 0) A := by
    conv_lhs => lhs; rw [← cfc_id' ℝ A hA.isSelfAdjoint]
    rw [← cfc_sub (fun x : ℝ ↦ x) (fun x : ℝ ↦ min x t) A (hc _) (hc _)]
    apply cfc_congr
    intro x _
    by_cases hx : x ≤ t
    · simp only [min_eq_left hx, sub_self, max_eq_right (sub_nonpos.mpr hx)]
    · have htx : t ≤ x := (not_le.mp hx).le
      simp only [min_eq_right htx, max_eq_left (sub_nonneg.mpr htx)]
  rw [hexcess, ← neg_smul, hA.exp_mul_sub_const_eq_cfc (-s) u,
    ← _root_.cfc_mul _ _ A (hc _) (hc _)]

/-- The actual positive energy excess followed by the inverse weight has
an exponentially small norm. Auxiliary to AKL14, arXiv:1406.3898,
Theorem lowspec, lines 1102–1168, and ALVV, arXiv:1602.08828v2,
Theorem `t:ais`, lines 1010–1024. -/
private theorem IsHermitian.norm_excess_mul_inverse_weight_le
    (hA : A.IsHermitian) (s t u : ℝ) (hs : 0 < s) :
    ‖(A - cfc (fun x : ℝ ↦ min x t) A) *
      NormedSpace.exp (-(s • (A - u • (1 : Matrix n n ℂ))))‖ ≤
      Real.exp (-s * (t - u) - 1) / s := by
  rw [hA.excess_mul_inverse_weight_eq_cfc s t u]
  exact norm_cfc_posPart_sub_exponential_weight_le A s t u hs
end Matrix

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- A clipped energy excess has no component below the smaller cutoff.
Auxiliary to AKL14, arXiv:1406.3898, Theorem lowspec, lines 1102–1168,
and ALVV, arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
private theorem IsHermitian.excess_mul_lowProjection_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {t u : ℝ} (hut : u ≤ t) :
    (A - cfc (fun x : ℝ ↦ min x t) A) * (1 - spectralProjectionGE A u) = 0 := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hD : A - cfc (fun x : ℝ ↦ min x t) A =
      cfc (fun x : ℝ ↦ x - min x t) A := by
    conv_lhs => lhs; rw [← cfc_id' ℝ A hA.isSelfAdjoint]
    rw [← cfc_sub (fun x : ℝ ↦ x) (fun x : ℝ ↦ min x t) A (hc _) (hc _)]
  have hI : (1 : Matrix n n ℂ) = cfc (fun _ : ℝ ↦ (1 : ℝ)) A := by
    rw [cfc_const (1 : ℝ) A hA.isSelfAdjoint, map_one]
  rw [hD, spectralProjectionGE, hI,
    ← cfc_sub (fun _ : ℝ ↦ (1 : ℝ))
      (fun x : ℝ ↦ if u ≤ x then 1 else 0) A (hc _) (hc _),
    ← _root_.cfc_mul _ _ A (hc _) (hc _),
    ← cfc_const_zero (R := ℝ) (a := A)]
  apply cfc_congr
  intro x _
  by_cases hx : u ≤ x
  · simp only [ite_eq_left hx, sub_self, mul_zero]
  · have hxt : x ≤ t := (not_le.mp hx).le.trans hut
    simp only [ite_eq_right hx, min_eq_left hxt, sub_self, zero_mul]
end Matrix

namespace ContinuousLinearMap

/-- The actual restriction of the discrepancy factors through the weighted
high-energy map. The support and inverse identities are algebraic inputs,
not norm or residual estimates. Auxiliary to AKL14, arXiv:1406.3898,
Theorem lowspec, lines 1102–1168, and ALVV, arXiv:1602.08828v2,
Theorem `t:ais`, lines 1010–1024. -/
private theorem domRestrict_eq_weighted_factor_of_projection_embedding
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (D Winv W Q : E →L[𝕜] E) {G U : Submodule 𝕜 E}
    (Z : G →L[𝕜] U)
    (hZ : U.subtypeL ∘L Z = (W * Q).domRestrict G)
    (hInv : Winv * W = 1) (hD : D * (1 - Q) = 0) :
    D.domRestrict G = (D * Winv) ∘L (U.subtypeL ∘L Z) := by
  have hfactor := mul_inverse_weight_mul_eq_of_right_support D Winv W Q hInv hD
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg (fun A : G →L[𝕜] E ↦ A x) hZ
  change (Z x : E) = (W * Q) (x : E) at hx
  change D (x : E) = (D * Winv) (Z x : E)
  rw [hx]
  exact (congrArg (fun A : E →L[𝕜] E ↦ A (x : E)) hfactor).symm

/-- The discrepancy on the actual low-energy domain is bounded by the
inverse-weight tail and the weighted high-energy map. Auxiliary to AKL14,
arXiv:1406.3898, Theorem lowspec, lines 1102–1168, and ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
private theorem norm_domRestrict_le_weighted_factor
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (D Winv W Q : E →L[𝕜] E) {G U : Submodule 𝕜 E}
    (Z : G →L[𝕜] U)
    (hZ : U.subtypeL ∘L Z = (W * Q).domRestrict G)
    (hInv : Winv * W = 1) (hD : D * (1 - Q) = 0) :
    ‖D.domRestrict G‖ ≤ ‖D * Winv‖ * ‖Z‖ := by
  have hnorm : ‖U.subtypeL ∘L Z‖ = ‖Z‖ := by
    simpa only [Submodule.subtypeₗᵢ_toContinuousLinearMap] using
      (LinearIsometry.norm_toContinuousLinearMap_comp U.subtypeₗᵢ (g := Z))
  rw [domRestrict_eq_weighted_factor_of_projection_embedding D Winv W Q Z hZ hInv hD]
  exact ((D * Winv).opNorm_comp_le (U.subtypeL ∘L Z)).trans (by rw [hnorm])
end ContinuousLinearMap

namespace Matrix

/-- The discrepancy of the actual spectral clipping, restricted to a
specified domain, is controlled by its actual weighted high-energy map.
Only the literal embedding identity specifies that map; no norm estimate
for the weight, discrepancy or map is supplied. Auxiliary to AKL14,
arXiv:1406.3898, Theorem lowspec, lines 1102–1168, and ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
theorem IsHermitian.norm_excess_domRestrict_le_actual_weighted_map
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (s t u : ℝ) (hs : 0 < s) (hut : u ≤ t)
    {G U : Submodule ℂ (EuclideanSpace ℂ n)} (Z : G →L[ℂ] U) :
    let ι := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
    let W := NormedSpace.exp (s • (A - u • (1 : Matrix n n ℂ)))
    let Q := spectralProjectionGE A u
    U.subtypeL ∘L Z = (ι W * ι Q).domRestrict G →
      ‖(ι (A - cfc (fun x : ℝ ↦ min x t) A)).domRestrict G‖ ≤
        (Real.exp (-s * (t - u) - 1) / s) * ‖Z‖ := by
  intro ι W Q hZ
  let D := A - cfc (fun x : ℝ ↦ min x t) A
  let Winv := NormedSpace.exp (-(s • (A - u • (1 : Matrix n n ℂ))))
  have hInvM : Winv * W = 1 := exp_neg_mul_exp_eq_one _
  have hInv : ι Winv * ι W = 1 := by
    rw [← map_mul, hInvM, map_one]
  have hDM : D * (1 - Q) = 0 := hA.excess_mul_lowProjection_eq_zero hut
  have hD : ι D * (1 - ι Q) = 0 := by
    rw [← map_one ι, ← map_sub, ← map_mul, hDM, map_zero]
  have htail : ‖ι D * ι Winv‖ ≤ Real.exp (-s * (t - u) - 1) / s := by
    calc
      ‖ι D * ι Winv‖ = ‖ι (D * Winv)‖ :=
        congrArg norm (map_mul ι D Winv).symm
      _ = ‖D * Winv‖ := (Matrix.cstar_norm_def (D * Winv)).symm
      _ ≤ Real.exp (-s * (t - u) - 1) / s :=
        hA.norm_excess_mul_inverse_weight_le s t u hs
  exact (ContinuousLinearMap.norm_domRestrict_le_weighted_factor
    (ι D) (ι Winv) (ι W) (ι Q) Z hZ hInv hD).trans
      (mul_le_mul_of_nonneg_right htail (norm_nonneg Z))
end Matrix
end
end
