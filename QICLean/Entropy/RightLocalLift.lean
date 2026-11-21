/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterMoment
import QICLean.ManyBody.Sites.RegionState
import QICLean.Entropy.SupportedMarginalTails

/-!
# Operators on the complementary cut factor

In the coordinates of a bipartition, an operator of the form `1 ⊗ R` is supported
on the complementary region. This follows by identifying it with the existing
local lift on that region. No configuration or local dimension is assumed nonempty.

This support fact is used in the product replacement argument of
arXiv:0705.0292v2, the footnote at lines 436–470 of `paper_v2.tex`.
-/

open Matrix
open scoped Kronecker

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- An operator on the right cut factor is a local lift on the complement. -/
private theorem rightCut_eq_localLift_compl (D : Finset V)
    (R : Matrix ((v : {v : V // v ∉ D}) → Fin (n v))
      ((v : {v : V // v ∉ D}) → Fin (n v)) ℂ) :
    reindex (ManyBody.cutEquiv (fun v ↦ Fin (n v)) D).symm
        (ManyBody.cutEquiv (fun v ↦ Fin (n v)) D).symm
      ((1 : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
          (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ) ⊗ₖ R) =
    ManyBody.place Dᶜ
      (R.reindex (ManyBody.complementEquiv (fun v ↦ Fin (n v)) D)
        (ManyBody.complementEquiv (fun v ↦ Fin (n v)) D)) := by
  classical
  ext σ τ
  simp [ManyBody.place, ManyBody.place, ManyBody.cutEquiv, Equiv.piEquivPiSubtypeProd,
    ManyBody.complementEquiv, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, funext_iff, Subtype.forall, mul_comm]

/-- An operator on the right cut factor is supported on the complementary sites. -/
theorem isSupportedOn_rightCut (D : Finset V)
    (R : Matrix ((v : {v : V // v ∉ D}) → Fin (n v))
      ((v : {v : V // v ∉ D}) → Fin (n v)) ℂ) :
    ManyBody.IsSupportedOn
      (reindex (ManyBody.cutEquiv (fun v ↦ Fin (n v)) D).symm
          (ManyBody.cutEquiv (fun v ↦ Fin (n v)) D).symm
        ((1 : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
            (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ) ⊗ₖ R)) Dᶜ := by
  rw [rightCut_eq_localLift_compl]
  exact ManyBody.place_mem_supportedOperators _

end Entropy
