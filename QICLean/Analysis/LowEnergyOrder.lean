/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyPerturbation

/-!
# Order of closed low-energy subspaces

Increasing an energy cutoff enlarges its closed spectral span. This is
used in the nested spectral targets of ALVV, arXiv:1602.08828v2,
Proposition `prop:albootstrap-ld`, lines 1112–1128, as well as the
finite cutoff comparisons at lines 955–968 and 1020.
-/

namespace Submodule

/-- Monotonicity of a closed low-energy span, used in the finite cutoff
comparison in ALVV, arXiv:1602.08828v2, lines 955–968 and 1020. -/
theorem spectralSpanLE_mono_cutoff
    {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]
    (b : OrthonormalBasis ι ℂ F) (a : ι → ℝ) {c d : ℝ} (hcd : c ≤ d) :
    spectralSpanLE b a c ≤ spectralSpanLE b a d := by
  apply span_mono
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨j, hj.trans hcd, rfl⟩

end Submodule
