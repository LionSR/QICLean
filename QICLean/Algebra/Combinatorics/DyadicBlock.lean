/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Fintype.Basic

/-!
# Dyadic blocks of a finite set

Moved from TNLean at commit `2417e0a2e4d8a1dc2db0a14e0c9cae4ca735829e`.
`TNLean/MPS/AreaLaw/Spectral/SupersiteHierarchy.lean`.
The block and its inclusion and disjointness lemmas are in the `Finset` namespace.
-/

namespace Finset

variable {ι : Type*} [Fintype ι]

/-- The sites of block `k` at level `m`: those whose supersite has quotient `k` by `2^m`. -/
def dyadicBlock (blk : ι → ℕ) (m k : ℕ) : Finset ι :=
  Finset.univ.filter fun i ↦ blk i / 2 ^ m = k

theorem mem_dyadicBlock {blk : ι → ℕ} {m k : ℕ} {i : ι} :
    i ∈ dyadicBlock blk m k ↔ blk i / 2 ^ m = k := by
  simp [dyadicBlock]

theorem dyadicBlock_two_mul_subset (blk : ι → ℕ) (m k : ℕ) :
    dyadicBlock blk m (2 * k) ⊆ dyadicBlock blk (m + 1) k := fun i hi ↦ by
  rw [mem_dyadicBlock] at hi ⊢
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hi]
  omega

theorem dyadicBlock_two_mul_add_one_subset (blk : ι → ℕ) (m k : ℕ) :
    dyadicBlock blk m (2 * k + 1) ⊆ dyadicBlock blk (m + 1) k := fun i hi ↦ by
  rw [mem_dyadicBlock] at hi ⊢
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hi]
  omega

theorem disjoint_dyadicBlock_two_mul (blk : ι → ℕ) (m k : ℕ) :
    Disjoint (dyadicBlock blk m (2 * k)) (dyadicBlock blk m (2 * k + 1)) :=
  Finset.disjoint_left.mpr fun i h₁ h₂ ↦ by
    rw [mem_dyadicBlock] at h₁ h₂
    omega

end Finset
