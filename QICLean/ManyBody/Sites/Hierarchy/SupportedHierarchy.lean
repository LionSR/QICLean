/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Twirl
import QICLean.Spectral.LowEnergy.HierarchyLevels
import QICLean.Algebra.Combinatorics.DyadicBlock

/-!
# Support of projections in a dyadic hierarchy

Each projection in the hierarchy acts on its own block. The projections on sibling
blocks therefore commute.

Moved from TNLean at commit `2417e0a2e4d8a1dc2db0a14e0c9cae4ca735829e`.
`TNLean/MPS/AreaLaw/Spectral/SupersiteHierarchy.lean`. The hierarchy is described using `Finset.dyadicBlock`.
-/

open Matrix Finset
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace ManyBody

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The window projection of an operator acting on `S` acts on `S`. -/
theorem windowProjection_mem_supportedOperators {S : Finset ι}
    {M : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hM : M ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) (c x : ℝ) :
    Matrix.windowProjection M c x ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S :=
  ManyBody.cfc_mem_supportedOperators _ (sub_mem hM
    (SMulMemClass.smul_mem _ (one_mem (ManyBody.supportedOperators _ S))))

/-- The window projection inside the range of `Q` acts on `S` when `Q` and `M` do. -/
theorem compressedWindowProjection_mem_supportedOperators {S : Finset ι}
    {Q M : Matrix (ι → Fin d) (ι → Fin d) ℂ}
    (hQ : Q ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S)
    (hM : M ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S) (c x : ℝ) :
    Matrix.compressedWindowProjection Q M c x ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) S :=
  mul_mem hQ (windowProjection_mem_supportedOperators
    (mul_mem (mul_mem hQ hM) hQ) c x)

/-- **Each projection acts on its block.** If `P 0 k = 1`, `P (m + 1) k` is the window of
`M m k` inside the range of `P m (2k) P m (2k + 1)`, and the pair operator `M m k` acts on the
block `k` of level `m + 1`, then `P m k` acts on the block `k` of level `m`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 609–628 and 668–685. -/
theorem mem_supportedOperators_hierarchy (blk : ι → ℕ)
    (P M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      Matrix.compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hMsupp : ∀ m k,
        M m k ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (dyadicBlock blk (m + 1) k)) :
    ∀ m k, P m k ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (dyadicBlock blk m k) := by
  intro m
  induction m with
  | zero =>
    intro k
    rw [hP0]
    exact (one_mem (ManyBody.supportedOperators _ _))
  | succ m ih =>
    intro k
    rw [hstep]
    exact compressedWindowProjection_mem_supportedOperators
      (mul_mem
        (ManyBody.supportedOperators_mono (dyadicBlock_two_mul_subset blk m k) (ih (2 * k)))
        (ManyBody.supportedOperators_mono (dyadicBlock_two_mul_add_one_subset blk m k)
          (ih (2 * k + 1))))
      (hMsupp m k) _ _

/-- **The halves of a block commute.** In the hierarchy of `mem_supportedOperators_hierarchy`,
the projections of the two halves of each block act on the disjoint blocks `2k` and `2k + 1` of
their level, so they commute. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 609–628 and 668–685. -/
theorem commute_hierarchy_halves (blk : ι → ℕ)
    (P M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      Matrix.compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hMsupp : ∀ m k,
        M m k ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (dyadicBlock blk (m + 1) k)) :
    ∀ m k, Commute (P m (2 * k)) (P m (2 * k + 1)) := by
  have hsupp := mem_supportedOperators_hierarchy blk P M c x hP0 hstep hMsupp
  exact fun m k ↦ ManyBody.commute_of_mem_supportedOperators_of_disjoint (hsupp m (2 * k))
      (hsupp m (2 * k + 1)) (disjoint_dyadicBlock_two_mul blk m k)

/-- **All levels on supersites.** The bound of `Matrix.norm_sub_hierarchy_le`, with the commutation
of the two halves of each block derived from the supports: each pair operator `M m k` acts on the
block `k` of level `m + 1`, as the operators `M_{k,k+1}` joining two neighbouring supersites
do. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 609–707. -/
theorem norm_sub_hierarchy_le_of_mem_supportedOperators (blk : ι → ℕ)
    (P M : ℕ → ℕ → Matrix (ι → Fin d) (ι → Fin d) ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      Matrix.compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hMsupp : ∀ m k,
      M m k ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) (dyadicBlock blk (m + 1) k))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 < x m)
    {ψ : EuclideanSpace ℂ (ι → Fin d)} (hψ : ‖ψ‖ = 1) {ε K : ℝ}
    (hres : ∀ m k, ‖toEuclideanLin (M m k - (c m k : ℂ) • 1) ψ‖ ≤ ε)
    (hK : ∀ m k, ‖M m k - (c m k : ℂ) • 1‖ ≤ K) :
    ∀ m k, IsStarProjection (P m k) ∧
      ‖ψ - toEuclideanLin (P m k) ψ‖ ≤ Real.hierarchyDeficiency ε K x m :=
  Matrix.norm_sub_hierarchy_le P M c x hP0 hstep
    (commute_hierarchy_halves blk P M c x hP0 hstep hMsupp) hM hx hψ hres hK

end ManyBody
