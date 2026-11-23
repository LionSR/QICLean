/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Norm.KroneckerOperatorNorm
import QICLean.Algebra.Kronecker.PiKronecker

/-!
# The operator norm of a Kronecker product of a finite family

The Kronecker product `⊗ₖ K k` of a finite family of rectangular complex matrices has operator
norm at most the product of the operator norms of its factors; in particular a Kronecker product
of contractions is a contraction.

## Main results

* `Matrix.piKronecker_eq_reindex_kronecker` — one factor split off along `Equiv.piSplitAt`.
* `Matrix.l2_opNorm_piKronecker_le`, `Matrix.l2_opNorm_piKronecker_le_one`.
-/

open scoped Kronecker Matrix.Norms.L2Operator

namespace Matrix

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {ι κ : ν → Type*}

/-- The Kronecker product of a family with one factor split off along `Equiv.piSplitAt`. -/
theorem piKronecker_eq_reindex_kronecker (K : (k : ν) → Matrix (ι k) (κ k) ℂ) (v : ν) :
    piKronecker K =
      reindex (Equiv.piSplitAt v ι).symm (Equiv.piSplitAt v κ).symm
        (K v ⊗ₖ piKronecker fun j : {j // j ≠ v} ↦ K j) := by
  ext x y
  simp only [piKronecker_apply, reindex_apply, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply, Equiv.piSplitAt_apply]
  exact Fintype.prod_eq_mul_prod_subtype_ne _ v

/-- **The operator norm of a Kronecker product is at most the product of the operator norms of
its factors.** -/
theorem l2_opNorm_piKronecker_le [∀ k, Fintype (ι k)] [∀ k, Fintype (κ k)]
    [∀ k, DecidableEq (κ k)] (K : (k : ν) → Matrix (ι k) (κ k) ℂ) :
    ‖piKronecker K‖ ≤ ∏ k, ‖K k‖ := by
  classical
  induction h : Fintype.card ν generalizing ν with
  | zero =>
    have : IsEmpty ν := Fintype.card_eq_zero_iff.mp h
    have e : piKronecker K = reindex (Equiv.ofUnique Unit _) (Equiv.ofUnique Unit _)
        (1 : Matrix Unit Unit ℂ) := by
      ext x y
      simp
    rw [e, Finset.univ_eq_empty, Finset.prod_empty]
    refine (l2_opNorm_reindex_le _ _ _).trans ?_
    rw [CStarRing.norm_one]
  | succ n ih =>
    obtain ⟨v⟩ : Nonempty ν := Fintype.card_pos_iff.mp (h ▸ Nat.succ_pos n)
    have hcard : Fintype.card {j // j ≠ v} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, h, Nat.add_sub_cancel]
    rw [piKronecker_eq_reindex_kronecker K v, Fintype.prod_eq_mul_prod_subtype_ne _ v]
    refine (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_kronecker_le _ _).trans ?_)
    exact mul_le_mul_of_nonneg_left (ih (fun j : {j // j ≠ v} ↦ K j) hcard) (norm_nonneg _)

/-- A Kronecker product of contractions is a contraction. -/
theorem l2_opNorm_piKronecker_le_one [∀ k, Fintype (ι k)] [∀ k, Fintype (κ k)]
    [∀ k, DecidableEq (κ k)] {K : (k : ν) → Matrix (ι k) (κ k) ℂ} (hK : ∀ k, ‖K k‖ ≤ 1) :
    ‖piKronecker K‖ ≤ 1 :=
  (l2_opNorm_piKronecker_le K).trans
    (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun k _ ↦ hK k)

end Matrix
