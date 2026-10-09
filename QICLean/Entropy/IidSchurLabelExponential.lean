/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaPermutationCovariance
import QICLean.Analysis.SurprisalFunctionalCalculus
import QICLean.Entropy.IidSurprisalExponential
import QICLean.Representation.SchurLabelTails

/-!
# Exponential Schur-label tails for independent copies

For a fixed density matrix, the mass of Schur labels of logarithmic dimension
larger than the copy number times an entropy upper bound plus one decreases
exponentially. Permutation invariance follows from the literal tensor power.
The supported comparison with surprisal permits a kernel in the density.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 332–343,
  `comparator:rough-overlap`, manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped BigOperators Matrix Kronecker ComplexOrder Matrix.Norms.L2Operator
open PermutationRepresentation TensorPower

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

/-- The actual independent-copy density has exponentially small Schur mass
above any fixed entropy upper bound plus one. No permutation-invariance,
positive-definiteness, or concentration hypothesis is added.

OpenAI area-law manuscript, `07-comparators.tex`, lines 339–343. -/
theorem PosSemidef.exists_re_trace_one_sub_labelCutoff_finKronecker_le_exp
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {s : ℝ}
    (hs : vonNeumannEntropy ρ hρ.isHermitian ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      let ρk := finKronecker (fun _ : Fin k ↦ ρ)
      (ρk * (1 - labelCutoff (copyPerm n k) ((k : ℝ) * (s + 1)))).trace.re ≤
        Real.exp (-c * (k : ℝ)) := by
  classical
  obtain ⟨c, hc, htail⟩ := hρ.exists_re_trace_surprisal_upper_tail_finKronecker_le_exp htr
  refine ⟨c, hc, ?_⟩
  intro k hk
  let ρk := finKronecker (fun _ : Fin k ↦ ρ)
  have hρk : ρk.PosSemidef :=
    finKronecker_posSemidef (fun _ : Fin k ↦ ρ) (fun _ ↦ hρ)
  have htrk : ρk.trace = 1 := by
    change (∑ x : Fin k → n, ∏ j, ρ (x j) (x j)) = 1
    rw [← Fintype.prod_sum (fun (_ : Fin k) (i : n) ↦ ρ i i)]
    change (∏ _ : Fin k, ρ.trace) = 1
    simp only [htr, Finset.prod_const_one]
  have hcompare := re_trace_mul_one_sub_labelCutoff_le (copyPerm n k) hρk htrk
    (fun σ ↦ (commute_finKronecker_const_permOp ρ k σ).symm)
    ((k : ℝ) * (s + 1))
  rw [← hρk.isHermitian.cfc_neg_log_eq
    (fun t : ℝ ↦ if (k : ℝ) * (s + 1) < t then 1 else 0)] at hcompare
  have hthreshold :
      (k : ℝ) * (vonNeumannEntropy ρ hρ.isHermitian + 1) ≤ (k : ℝ) * (s + 1) :=
    mul_le_mul_of_nonneg_left (add_le_add hs le_rfl) (Nat.cast_nonneg k)
  have hmono :
      (ρk * cfc (fun t : ℝ ↦ if (k : ℝ) * (s + 1) < t then 1 else 0)
        (-CFC.log ρk)).trace.re ≤
      (ρk * cfc (fun t : ℝ ↦
        if (k : ℝ) * (vonNeumannEntropy ρ hρ.isHermitian + 1) < t then 1 else 0)
        (-CFC.log ρk)).trace.re := by
    dsimp only [ρk]
    rw [hρ.re_trace_finKronecker_mul_cfc_surprisal,
      hρ.re_trace_finKronecker_mul_cfc_surprisal]
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _
      (Finset.prod_nonneg fun j _ ↦ hρ.eigenvalues_nonneg (x j))
    split_ifs with ha hb hb
    · exact le_rfl
    · exact False.elim (hb (hthreshold.trans_lt ha))
    · norm_num
    · exact le_rfl
  exact hcompare.trans (hmono.trans (htail k hk))

end Matrix
