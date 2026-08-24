/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import QICLean.Analysis.FiniteCoordinateNowosad.Yamagami

/-!
# Yamagami's two-maxima application of Nowosad's theorem

This file formalizes the conclusion of Yamagami's Theorem 1 for the normalized
generator `b = (S a) / s`.  Nowosad's theorem makes the functional constant
along `b^t`; pulling this curve back gives `x(t) = s S⁻¹(b^t)` in the original
coordinates.
-/

open scoped BigOperators Matrix
open Nowosad

namespace Yamagami

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pulled-back curve passes through the unit vector. -/
theorem pulledBackCurve_zero
    (S : Matrix ι ι ℝ) (s : ℝ) (b : ι → ℝ)
    (hS : IsUnit S.det) (hs : s ≠ 0)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ)) :
    pulledBackCurve S s b 0 = 1 := by
  have hpow : coordinateRpow b 0 = (1 : ι → ℝ) := by
    ext i
    simp [coordinateRpow]
  rw [pulledBackCurve, hpow, ← inverseOperator_apply,
    inverseOperator_apply_one S s hS hs hSone]
  ext i
  simp [hs]

/-- The tangent of Yamagami's pulled-back curve at the unit is
`s S⁻¹(log b)`. -/
theorem hasDerivAt_pulledBackCurve_zero
    (S : Matrix ι ι ℝ) (s : ℝ) (b : ι → ℝ)
    (hb : b ∈ positiveInvertibles) :
    ∀ i, HasDerivAt (fun t ↦ pulledBackCurve S s b t i)
      ((s • (S⁻¹ *ᵥ coordinateLog b)) i) 0 := by
  rw [mem_positiveInvertibles] at hb
  intro i
  have hsum : HasDerivAt
      (fun t : ℝ ↦ ∑ j, S⁻¹ i j * b j ^ t)
      (∑ j, S⁻¹ i j * Real.log (b j)) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    simpa using (((hasDerivAt_id' (x := (0 : ℝ))).const_rpow (hb j)).const_mul
      (S⁻¹ i j))
  have hscaled := hsum.const_mul s
  simpa [pulledBackCurve, coordinateRpow, coordinateLog,
    Matrix.mulVec, dotProduct] using hscaled

/-- Nowosad constancy for Yamagami's correctly transformed generator
`b = (S a)/s`: the functional `L_{S⁻¹}` is constant along `b^t`. -/
theorem lambdaT_coordinateRpow_eq_of_two_localMaxima
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (ha : a ∈ positiveInvertibles)
    (hmaxOne : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles 1)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    ∀ t : ℝ,
      lambdaT (inverseOperator S)
          (coordinateRpow (transformedGenerator S s a) t) =
        lambdaT (inverseOperator S) 1 := by
  let b := transformedGenerator S s a
  have hbpos : b ∈ positiveInvertibles :=
    transformedGenerator_mem_positiveInvertibles
      S s a hSnonneg hs hSone ha
  obtain ⟨hmaxOne', hmaxB⟩ := normalized_localMaxima
    S s a hS hSnonneg hs hSone ha hmaxOne hmaxA
  intro t
  let q : laurentSubalgebra ((1 : ι → ℝ)⁻¹ * b) :=
    ⟨coordinateRpow b t, by
      simpa using coordinateRpow_mem_laurentSubalgebra b t⟩
  have hq : ∀ i, (q : ι → ℝ) i ≠ 0 := by
    rw [mem_positiveInvertibles] at hbpos
    intro i
    exact (Real.rpow_pos_of_pos (hbpos i) t).ne'
  have hconst := lambdaT_eq_on_laurentSubalgebra_of_two_localMaxOn
    (inverseOperator S) (1 : ι → ℝ) b (by simp) hbpos
    hmaxOne' hmaxB q hq
  simpa [q, b] using hconst

/-- Pulling the power curve back by `S` gives exactly Yamagami's curve
`x(t) = s S⁻¹(b^t)`, along which the original composed functional is
constant. -/
theorem composed_lambdaT_pulledBackCurve_eq_of_two_localMaxima
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (ha : a ∈ positiveInvertibles)
    (hmaxOne : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles 1)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    ∀ t : ℝ,
      lambdaT (inverseOperator S)
          (S *ᵥ pulledBackCurve S s (transformedGenerator S s a) t) =
        lambdaT (inverseOperator S) (S *ᵥ (1 : ι → ℝ)) := by
  intro t
  have hconst := lambdaT_coordinateRpow_eq_of_two_localMaxima
    S s a hS hSnonneg hs hSone ha hmaxOne hmaxA t
  have hcurve :
      S *ᵥ pulledBackCurve S s (transformedGenerator S s a) t =
        s • coordinateRpow (transformedGenerator S s a) t := by
    unfold pulledBackCurve
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv S hS, Matrix.one_mulVec]
  rw [hcurve, lambdaT_smul _ s (ne_of_gt hs), hSone,
    lambdaT_smul _ s (ne_of_gt hs)]
  exact hconst

/-- The tangent `s S⁻¹(log b)` of the pulled-back curve equals `log b`.
This is the multiplication conclusion of Nowosad's theorem applied to the
Laurent-algebra element `log b`. -/
theorem pulledBackTangent_eq_coordinateLog_of_two_localMaxima
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (ha : a ∈ positiveInvertibles)
    (hmaxOne : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles 1)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    s • (S⁻¹ *ᵥ coordinateLog (transformedGenerator S s a)) =
      coordinateLog (transformedGenerator S s a) := by
  let b := transformedGenerator S s a
  change s • (S⁻¹ *ᵥ coordinateLog b) = coordinateLog b
  have hbpos : b ∈ positiveInvertibles :=
    transformedGenerator_mem_positiveInvertibles
      S s a hSnonneg hs hSone ha
  obtain ⟨hmaxOne', hmaxB⟩ := normalized_localMaxima
    S s a hS hSnonneg hs hSone ha hmaxOne hmaxA
  let q : laurentSubalgebra ((1 : ι → ℝ)⁻¹ * b) :=
    ⟨coordinateLog b, by
      simpa using coordinateLog_mem_laurentSubalgebra b⟩
  have hmul := multiplication_on_laurentSubalgebra_of_two_localMaxOn
    (inverseOperator S) (1 : ι → ℝ) b (by simp) hbpos
    hmaxOne' hmaxB q
  have heigen : S⁻¹ *ᵥ coordinateLog b = s⁻¹ • coordinateLog b := by
    rw [← inverseOperator_apply]
    simpa [q, inverseOperator_apply_one S s hS (ne_of_gt hs) hSone] using hmul
  rw [heigen]
  ext i
  simp [ne_of_gt hs]

end Yamagami
