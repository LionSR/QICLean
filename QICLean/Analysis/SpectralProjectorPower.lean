/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceSpectralProjector
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Powers of a spectral improving operator

The actual low spectral target is unchanged under taking powers. Low
spectral eigenvalues remain at least one, rather than being required to
equal one, and squared high spectral suppression is raised to the same
power. These facts support the repeated improvement in ALVV,
arXiv:1602.08828v2, `def:spectral-AGSP`, lines 570–581, and `l:er`, lines 597–622.

**Local fix (closed cutoffs and the sign of the filter):** These are powers
of the closed spectral conditions, without a positivity assumption on the
unsquared filter. See `docs/paper-gaps/alvv16_spectral_projector_boundary.tex`
and `docs/paper-gaps/alvv16_chebyshev_filter_positivity.tex`.
-/

namespace Submodule

variable {𝕜 E n : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype n]

/-- Taking the actual operator power preserves its low spectral target and
raises the squared suppression to that power. Low eigenvalues need only be
at least one. Supporting ALVV, arXiv:1602.08828v2,
`def:spectral-AGSP`, lines 570–581, and `l:er`, lines 597–622. -/
theorem IsSpectralProjector.pow {K H : E →L[𝕜] E} {b : OrthonormalBasis n 𝕜 E}
    {h k : n → ℝ} {eta0 eta1 Delta : ℝ}
    (hK : IsSpectralProjector K H b h k eta0 eta1 Delta) (r : ℕ) :
    IsSpectralProjector (K ^ r) H b h (fun j ↦ k j ^ r) eta0 eta1 (Delta ^ r) := by
  refine ⟨hK.apply_H, ?_, ?_, ?_⟩
  · intro j
    have heigen : Module.End.HasEigenvector (K : Module.End 𝕜 E) (k j : 𝕜) (b j) :=
      ⟨Module.End.mem_eigenspace_iff.mpr (hK.apply_K j), b.toBasis.ne_zero j⟩
    change ((K ^ r : E →L[𝕜] E) : Module.End 𝕜 E) (b j) = _
    rw [ContinuousLinearMap.toLinearMap_pow]
    simpa only [RCLike.ofReal_pow] using heigen.pow_apply r
  · intro j hj
    exact one_le_pow₀ (hK.one_le j hj)
  · intro j hj
    rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg (k j)) (hK.sq_le j hj) r

end Submodule
