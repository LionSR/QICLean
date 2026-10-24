/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProbabilityEntropyGeometricTails

/-! Finite boundary applications of the same entropy theorem. -/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped BigOperators

/-- The zero-scale case has no restrictions on the unused tail majorants. -/
example {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    Entropy.probabilityEntropy p ≤ Real.log ((N + 1 : ℕ) : ℝ) + Real.log 2 := by
  have h := Entropy.probabilityEntropy_le_of_rankTailBounds (M := 0)
    p (fun _ ↦ N + 1) (fun _ ↦ (-7 : ℝ)) hp hsum
    (by omega) (by intro i hi; omega) (by omega) (by intro i hi; omega)
  simpa using h

private def rankTailBoundaryP (a : Fin 2) : ℝ := if a.val = 0 then 0 else 1

private def rankTailBoundaryR (i : ℕ) : ℕ :=
  if i < 2 then 1 else if i = 2 then 3 else 0

/-- The probability vector is increasing and has a zero entry. The first two
cutoffs coincide, the final cutoff exceeds the dimension, and the unused
subsequent cutoffs decrease to zero. Only finite adjacent monotonicity is used. -/
example :
    Entropy.probabilityEntropy rankTailBoundaryP ≤
      Real.log (rankTailBoundaryR 0 : ℝ) +
        Real.log 2 * (1 + ∑ _i ∈ Finset.range 2, (1 : ℝ)) +
        ∑ i ∈ Finset.range 2,
          (1 : ℝ) * Real.log
            ((rankTailBoundaryR (i + 1) : ℝ) / (rankTailBoundaryR i : ℝ)) := by
  apply Entropy.probabilityEntropy_le_of_rankTailBounds
    rankTailBoundaryP rankTailBoundaryR (fun _ ↦ (1 : ℝ))
  · intro a
    dsimp [rankTailBoundaryP]
    split_ifs <;> norm_num
  · norm_num [rankTailBoundaryP, Fin.sum_univ_two]
  · norm_num [rankTailBoundaryR]
  · intro i hi
    have hc : i = 0 ∨ i = 1 := by omega
    rcases hc with rfl | rfl <;> norm_num [rankTailBoundaryR]
  · norm_num [rankTailBoundaryR]
  · intro i hi
    norm_num [rankTailBoundaryR, hi, rankTailBoundaryP,
      Finset.sum_filter, Fin.sum_univ_two]

/-- An initial cutoff beyond the dimension makes all tail bounds zero. -/
example {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    Entropy.probabilityEntropy p ≤ Real.log ((N + 1 : ℕ) : ℝ) + Real.log 2 := by
  have hempty : (Finset.univ : Finset (Fin N)).filter
      (fun a ↦ N + 1 ≤ a.val) = ∅ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    omega
  have h := Entropy.probabilityEntropy_le_of_rankTailBounds (M := 2)
    p (fun _ ↦ N + 1) (fun _ ↦ (0 : ℝ)) hp hsum
    (by omega) (by intro i hi; exact le_rfl) (by omega)
    (by intro i hi; simpa only [hempty, Finset.sum_empty] using (le_rfl : (0 : ℝ) ≤ 0))
  simpa using h

/-- info:
'Entropy.probabilityEntropy_le_of_rankTailBounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.probabilityEntropy_le_of_rankTailBounds

namespace GeometricEntropyBoundary

private theorem zero_tail_singleton :
    Entropy.probabilityEntropy (fun _ : Fin 1 ↦ (1 : ℝ)) ≤
      ((0 : ℕ) : ℝ) * Real.log ((1 : ℕ) : ℝ) +
        (Real.log 2 + 0 * Real.log ((1 : ℕ) : ℝ)) / (1 - 0) := by
  apply Entropy.probabilityEntropy_le_of_geometricRankTailBounds
    (fun _ : Fin 1 ↦ (1 : ℝ)) 0 0 1 0
  all_goals norm_num [Fin.sum_univ_one]

end GeometricEntropyBoundary

/-- info:
'Entropy.probabilityEntropy_le_of_geometricRankTailBounds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.probabilityEntropy_le_of_geometricRankTailBounds
