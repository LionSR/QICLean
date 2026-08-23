/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Determinant.Bound

/-!
# Determinant under composition

This file formalizes the algebraic and monotonicity parts of Wolf's determinant
composition discussion.  The order is the one in Wolf Equation (6.22):
`T₁.comp T₂` is the map denoted by `T₁ T₂` there.

## Main statements

* `channelDet_comp` — Wolf Equation (6.22), determinant multiplicativity.
* `channelDet_norm_comp_eq_iff` — the exact algebraic equality split.
* `channelDet_norm_comp_le_of_positive_tracePreserving` — the inequality in
  Wolf's determinant-monotonicity corollary.

The source's geometric replacement of `‖channelDet T₂‖ = 1` by
"unitary conjugation or matrix transposition" depends on the still-missing
positive trace-preserving saturation classification.  It is deliberately not
claimed here.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Equation (6.22) and
  the determinant-monotonicity corollary in Section 6.1.1][Wolf2012QChannels]

## Tags

quantum channel, determinant, composition, monotonicity
-/
open scoped Matrix ComplexOrder MatrixOrder

variable {d : ℕ}

local notation "MatrixEnd" => ChannelDeterminant.Internal.MatrixEnd

/-- Wolf Equation (6.22): the channel determinant is multiplicative under
composition.  Lean's `T₁.comp T₂` has the same order as Wolf's `T₁ T₂`.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 338--342. -/
@[simp]
theorem channelDet_comp (T₁ T₂ : MatrixEnd d) :
    channelDet (T₁.comp T₂) = channelDet T₁ * channelDet T₂ := by
  simp only [channelDet_eq_linearMap_det, LinearMap.det_comp]

/-- The algebraic equality case behind Wolf's determinant-monotonicity
corollary: equality after right composition holds exactly when the left factor
has zero determinant or the right factor has determinant of modulus one.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 409--414,
using Equation (6.22).  The further positive-map saturation classification is
kept as a separate dependency. -/
theorem channelDet_norm_comp_eq_iff (T₁ T₂ : MatrixEnd d) :
    ‖channelDet (T₁.comp T₂)‖ = ‖channelDet T₁‖ ↔
      channelDet T₁ = 0 ∨ ‖channelDet T₂‖ = 1 := by
  rw [channelDet_comp, norm_mul]
  constructor
  · intro h
    by_cases hT₁ : channelDet T₁ = 0
    · exact Or.inl hT₁
    · exact Or.inr ((mul_eq_left₀ (norm_ne_zero_iff.mpr hT₁)).mp h)
  · rintro (hT₁ | hT₂)
    · simp only [hT₁, norm_zero, zero_mul]
    · simp only [hT₂, mul_one]

/-- The inequality in Wolf's determinant-monotonicity corollary: for positive
trace-preserving `T₁` and `T₂`, right composition by `T₂` cannot increase
the modulus of the determinant of `T₁`.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 409--414.
The hypotheses on `T₁` are retained to match the source statement, although
the determinant bound needed by the algebraic proof applies only to `T₂`. -/
theorem channelDet_norm_comp_le_of_positive_tracePreserving
    (T₁ T₂ : MatrixEnd d)
    (_hPos₁ : IsPositiveMap T₁) (_hTP₁ : IsTracePreservingMap T₁)
    (hPos₂ : IsPositiveMap T₂) (hTP₂ : IsTracePreservingMap T₂) :
    ‖channelDet (T₁.comp T₂)‖ ≤ ‖channelDet T₁‖ := by
  rw [channelDet_comp, norm_mul]
  calc
    ‖channelDet T₁‖ * ‖channelDet T₂‖ ≤ ‖channelDet T₁‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (channelDet_norm_le_one_of_positive_tracePreserving hPos₂ hTP₂)
        (norm_nonneg _)
    _ = ‖channelDet T₁‖ := mul_one _
