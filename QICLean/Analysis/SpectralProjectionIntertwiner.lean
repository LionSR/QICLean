/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedDensityTruncation
import QICLean.Entropy.ConditionalMovement.LogCompression

/-!
# Nonnegative spectral projections on intertwined ranges

A positive semidefinite matrix has nonnegative closed spectral projection equal
to the identity. If a Hermitian left action intertwines with a positive right
action, the left nonnegative spectral projection fixes the entire range of the
intertwiner. No injectivity, nonzero range or projection hypothesis is needed.

These are auxiliary spectral facts for the compatible physical-label argument
in OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 515–522, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The physical intertwining identity
must be derived separately; it is not asserted in this module.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-decomposition.
-/

/-- The closed nonnegative spectral projection of a positive matrix is the
identity, including a nontrivial kernel and empty coordinate sets. Auxiliary
spectral fact for OpenAI, `07-comparators.tex`, lines 515–522. -/
theorem PosSemidef.spectralProjectionGE_zero {B : Matrix n n ℂ} (hB : B.PosSemidef) :
    spectralProjectionGE B 0 = 1 := by
  rw [spectralProjectionGE]
  calc cfc (fun t : ℝ => if 0 ≤ t then 1 else 0) B = cfc (fun _ : ℝ => 1) B := by
        apply cfc_congr
        intro x hx
        rw [hB.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        simp [hB.eigenvalues_nonneg i]
    _ = 1 := by rw [cfc_const (1 : ℝ) B hB.isHermitian.isSelfAdjoint]; simp

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-decomposition.
-/

omit [DecidableEq n] in
/-- A Hermitian left action intertwined with a positive right action has only
nonnegative spectrum on the intertwiner's range. The intertwiner may be
rectangular, noninjective or zero. Auxiliary spectral fact for OpenAI,
`07-comparators.tex`, lines 515–522; a physical application must derive the
intertwining identity from its actual label actions. -/
theorem spectralProjectionGE_zero_mul_of_intertwine
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.PosSemidef) (V : Matrix m n ℂ) (hV : A * V = V * B) :
    spectralProjectionGE A 0 * V = V := by
  classical
  have h := ConditionalMovement.QuantumSSA.cfc_intertwine hA hB.isHermitian V hV
    (fun t : ℝ => if 0 ≤ t then 1 else 0)
  change spectralProjectionGE A 0 * V = V * spectralProjectionGE B 0 at h
  simpa [hB.spectralProjectionGE_zero] using h
end Matrix
