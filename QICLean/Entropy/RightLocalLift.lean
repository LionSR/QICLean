/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.LocalLift
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

/-- The complementary configuration type written with membership in the complement. -/
private def rightConfigComplEquiv (D : Finset V) :
    ((v : {v : V // v ∉ D}) → Fin (n v)) ≃ Entropy.RegionConfig n Dᶜ where
  toFun x v := x ⟨v.1, Finset.mem_compl.mp v.2⟩
  invFun x v := x ⟨v.1, Finset.mem_compl.mpr v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An operator on the right cut factor is a local lift on the complement. -/
private theorem rightCut_eq_localLift_compl (D : Finset V)
    (R : Matrix ((v : {v : V // v ∉ D}) → Fin (n v))
      ((v : {v : V // v ∉ D}) → Fin (n v)) ℂ) :
    reindex (Entropy.cutEquiv n D).symm (Entropy.cutEquiv n D).symm
      ((1 : Matrix (Entropy.RegionConfig n D) (Entropy.RegionConfig n D) ℂ) ⊗ₖ R) =
    Entropy.localLift Dᶜ
      (R.reindex (rightConfigComplEquiv (n := n) D) (rightConfigComplEquiv (n := n) D)) := by
  classical
  ext σ τ
  simp [Entropy.localLift, Entropy.cutEquiv, Equiv.piEquivPiSubtypeProd,
    rightConfigComplEquiv, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, funext_iff, Subtype.forall, mul_comm]

/-- An operator on the right cut factor is supported on the complementary sites. -/
theorem isSupportedOn_rightCut (D : Finset V)
    (R : Matrix ((v : {v : V // v ∉ D}) → Fin (n v))
      ((v : {v : V // v ∉ D}) → Fin (n v)) ℂ) :
    Entropy.IsSupportedOn
      (reindex (Entropy.cutEquiv n D).symm (Entropy.cutEquiv n D).symm
        ((1 : Matrix (Entropy.RegionConfig n D) (Entropy.RegionConfig n D) ℂ) ⊗ₖ R)) Dᶜ := by
  rw [rightCut_eq_localLift_compl]
  exact Entropy.isSupportedOn_localLift _

end Entropy
