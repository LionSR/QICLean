/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Eigenvector matrix elements controlled by commutators

These estimates are the generic eigenvector calculation in Hastings,
arXiv:cond-mat/0508554v3, lines 1678–1690.
-/

open scoped InnerProductSpace

namespace ApproximateDiagonalization

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **Matrix elements between eigenvectors from a commutator.** If `A` is self-adjoint with
`A v = r v` and `A w = s w`, then `|r - s| ‖⟪v, B w⟫‖ ≤ ‖[A, B]‖ ‖v‖ ‖w‖` for every `B`, since
`⟪v, [A, B] w⟫ = (r - s) ⟪v, B w⟫`. Hastings, arXiv:cond-mat/0508554v3, lines 1678–1690. -/
theorem abs_sub_mul_norm_inner_le_norm_commutator {A : E →L[𝕜] E} (hA : IsSelfAdjoint A)
    (B : E →L[𝕜] E) {v w : E} {r s : ℝ} (hv : A v = (r : 𝕜) • v) (hw : A w = (s : 𝕜) • w) :
    |r - s| * ‖⟪v, B w⟫_𝕜‖ ≤ ‖A * B - B * A‖ * ‖v‖ * ‖w‖ := by
  have hkey : ⟪v, (A * B - B * A) w⟫_𝕜 = ((r - s : ℝ) : 𝕜) * ⟪v, B w⟫_𝕜 := by
    have hsymm : ⟪v, A (B w)⟫_𝕜 = ⟪A v, B w⟫_𝕜 := (hA.isSymmetric v (B w)).symm
    simp only [_root_.sub_apply, mul_apply_eq_comp, inner_sub_right,
      hsymm, hv, hw, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
    push_cast
    ring
  calc |r - s| * ‖⟪v, B w⟫_𝕜‖ = ‖⟪v, (A * B - B * A) w⟫_𝕜‖ := by
        rw [hkey, norm_mul, RCLike.norm_ofReal]
    _ ≤ ‖v‖ * ‖(A * B - B * A) w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖A * B - B * A‖ * ‖w‖) := by gcongr; exact (A * B - B * A).le_opNorm w
    _ = _ := by ring

/-- **Off-diagonal elements in an eigenbasis.** If `A` is self-adjoint with `A v = r v`,
`A w = s w` and `r ≠ s`, then `‖⟪v, B w⟫‖ ≤ ‖[A, B]‖ ‖v‖ ‖w‖ / |r - s|` for every `B`. With
`A = P M_j P`, `B = P M_i P` and unit ground vectors `v`, `w`, this is Hastings' bound
`o(i) ≤ ‖[P M_i P, P M_j P]‖ / δλ_j` on the off-diagonal elements of `M_i` in a basis of the
ground space diagonalizing `M_j`, arXiv:cond-mat/0508554v3, lines 1678–1690. -/
theorem norm_inner_le_norm_commutator_div {A : E →L[𝕜] E} (hA : IsSelfAdjoint A)
    (B : E →L[𝕜] E) {v w : E} {r s : ℝ} (hv : A v = (r : 𝕜) • v) (hw : A w = (s : 𝕜) • w)
    (hrs : r ≠ s) :
    ‖⟪v, B w⟫_𝕜‖ ≤ ‖A * B - B * A‖ * ‖v‖ * ‖w‖ / |r - s| := by
  rw [le_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hrs)), mul_comm]
  exact abs_sub_mul_norm_inner_le_norm_commutator hA B hv hw

end ApproximateDiagonalization
