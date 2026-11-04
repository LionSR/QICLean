/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.ChoiTypeMap.Indecomposable

/-! Boundary applications and kernel axiom guards for Wolf Example 3.1. -/

open scoped Matrix ComplexOrder

namespace Matrix

-- The first nonempty source range, including Ha's empty beta sum.
example : IsIndecomposablePositiveMap (choiTypeMap 3 1) :=
  choiTypeMap_isIndecomposable (by norm_num) (by norm_num) (by norm_num)

-- A genuine middle parameter, beyond the two endpoint positivity proofs.
example : IsIndecomposablePositiveMap (choiTypeMap 5 2) :=
  choiTypeMap_isIndecomposable (by norm_num) (by norm_num) (by norm_num)

-- The entire upper endpoint, without fixing the dimension.
example {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    IsIndecomposablePositiveMap (choiTypeMap d (d - 2)) :=
  choiTypeMap_isIndecomposable hd (by omega) le_rfl

-- Exact arbitrary-parameter statements with no supplied positivity or witness premise.
example {d n : ℕ} [NeZero d] (hd : 3 ≤ d) (hn₁ : 1 ≤ n) (hn₂ : n ≤ d - 2) :
    ¬ IsDecomposablePositiveMap (choiTypeMap d n) :=
  choiTypeMap_not_isDecomposablePositiveMap hd hn₁ hn₂

example {d n : ℕ} [NeZero d] (hd : 3 ≤ d) (hn₁ : 1 ≤ n) (hn₂ : n ≤ d - 2) :
    IsIndecomposablePositiveMap (choiTypeMap d n) :=
  choiTypeMap_isIndecomposable hd hn₁ hn₂

-- The actual swapped witness is PPT in the smallest dimension.
example : (tensorFactorSwap (haAGamma 3 (1 / 2))).PosSemidef ∧
    IsPPT (tensorFactorSwap (haAGamma 3 (1 / 2))) :=
  ⟨(tensorFactorSwap_haAGamma_hasSchmidtNumberLE_two (1 / 2)).posSemidef,
    (partialTransposeLeft_tensorFactorSwap_haAGamma_hasSchmidtNumberLE_two
      (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2)).posSemidef⟩

-- Preserve the source normalization and sign at a middle parameter.
example : ((5 : ℂ) *
      (star (omegaVec 5) ⬝ᵥ
        (tensorMapId (choiTypeMapFin 5 2) (tensorFactorSwap (haAGamma 5 (1 / 2))) *ᵥ
          omegaVec 5))).re < 0 :=
  choiTypeMapFin_haAGamma_omegaVec_quadraticForm_re_neg
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Matrix

/-- info:
'Matrix.choiTypeMapFin_not_isDecomposablePositiveMap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.choiTypeMapFin_not_isDecomposablePositiveMap

/-- info:
'Matrix.choiTypeMap_not_isDecomposablePositiveMap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.choiTypeMap_not_isDecomposablePositiveMap

/-- info:
'Matrix.choiTypeMap_isIndecomposable' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.choiTypeMap_isIndecomposable
