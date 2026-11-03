/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SampledOperatorImage
import QICLean.Analysis.ViableNodeParameters

/-!
# The cubic bound for an actual sampled word image

This dimension estimate concerns every Haar unitary, before imposing a
success event. It supports ALVV, arXiv:1602.08828v2, error reduction,
lines 597–622, and the degenerate-ground-space merge analysis,
lines 1777–1817. The ordered words and input sample are the actual ones.
-/

namespace Submodule

variable {M iota : Type*} [Fintype iota]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]

/-- A family of at most `D²` actual operators, powered at the upper integer
logarithm, gives the cubic count for every literal sampled-word image.
Supporting ALVV, arXiv:1602.08828v2, error reduction, lines 597–622,
and merge analysis, lines 1777–1817. -/
lemma finrank_sampledWordImage_le_cubic {D s : ℕ} (hD : 2 ≤ D) (hs : 1 ≤ s)
    (F : iota → M →L[ℂ] M) (hF : Fintype.card iota ≤ D ^ 2)
    (W : Submodule ℂ M) (U : Matrix.unitaryGroup (Fin (Module.finrank ℂ W)) ℂ) :
    Module.finrank ℂ (sampledWordImage F (Nat.clog D (D ^ 2 * s)) s W U) ≤ D ^ 6 * s ^ 3 := by
  let power := Nat.clog D (D ^ 2 * s)
  calc
    _ ≤ Fintype.card iota ^ power * min s (Module.finrank ℂ W) :=
      finrank_sampledWordImage_le F power s W U
    _ ≤ (D ^ 2) ^ power * min s (Module.finrank ℂ W) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hF power)
    _ ≤ (D ^ 2) ^ power * s := Nat.mul_le_mul_left _ (Nat.min_le_left _ _)
    _ = (D ^ power) ^ 2 * s := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 power]
    _ ≤ D ^ 6 * s ^ 3 := (Nat.viable_node_power_bounds hD hs).2.2.2

end Submodule
