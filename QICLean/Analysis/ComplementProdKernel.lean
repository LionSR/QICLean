/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DetectabilityLemma

/-!
# Fixed vectors of a product of complementary projections

The fixed space of a finite product of orthogonal projections is the
intersection of their fixed spaces, even when they do not commute.
For the complementary product this is the common kernel of the original
projections. This is the kernel identity used in the frustration-free
truncation of ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`,
lines 1467–1487 and 1543–1550.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A vector is fixed by the actual product of complementary projections
exactly when every original factor annihilates it. Commutativity is not
required. This is the common-kernel step for ALVV, arXiv:1602.08828v2,
`def:FF-tH` and `thm:FF-tH`, lines 1467–1487 and 1543–1550. -/
theorem complementProd_apply_eq_self_iff
    {h : ℕ → E →L[𝕜] E} (hh : ∀ k, IsStarProjection (h k)) (n : ℕ) (x : E) :
    complementProd h n x = x ↔ ∀ k < n, h k x = 0 := by
  constructor
  · intro hfix
    have hsum : ∑ k ∈ Finset.range n, ‖h k (complementProd h k x)‖ ^ 2 = 0 := by
      rw [sum_norm_sq_apply_complementProd hh, hfix, sub_self]
    have hzero (k : ℕ) (hk : k < n) : h k (complementProd h k x) = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_hj : j ∈ Finset.range n) ↦ sq_nonneg ‖h j (complementProd h j x)‖)).mp
          hsum k (Finset.mem_range.mpr hk)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    have hprefix : ∀ k ≤ n, complementProd h k x = x := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hkn
        rw [complementProd_succ_apply, hzero k (Nat.lt_of_succ_le hkn), sub_zero,
          ih ((Nat.le_succ k).trans hkn)]
    intro k hk
    exact (congrArg (h k) (hprefix k hk.le)).symm.trans (hzero k hk)
  · intro hx
    have hprefix : ∀ k ≤ n, complementProd h k x = x := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hkn
        rw [complementProd_succ_apply, ih ((Nat.le_succ k).trans hkn),
          hx k (Nat.lt_of_succ_le hkn), sub_zero]
    exact hprefix n le_rfl

end ContinuousLinearMap
