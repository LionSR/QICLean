/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Channel.Schwarz.UnitaryComparison

/-!
# Monotone trace functions

Wolf's Proposition "Monotone trace functions" (Chapter 5, Equation (5.55)) states that for a
continuously differentiable non-decreasing function `f` on an open interval `I` and Hermitian
matrices `A ≤ B` with spectra in `I`,

`tr f(A) ≤ tr f(B)`.

Wolf proves it by differentiating `x ↦ tr f(A + x(B - A))`. We instead deduce it from the
corrected unitary comparison `f(A) ≤ U f(B) U†` (Equation (5.57)), which Wolf derives right
afterwards from Weyl's monotonicity theorem. That route needs neither differentiability nor
openness of the interval: monotonicity of `f` on an order-connected set containing both spectra
suffices. The source hypotheses imply ours, so the theorem below contains Wolf's proposition.

## Main results

* `Matrix.IsHermitian.trace_cfc_le_trace_cfc_of_le`: Equation (5.55), in the complex order on
  traces.
* `Matrix.IsHermitian.re_trace_cfc_le_re_trace_cfc_of_le`: the same inequality for real parts.

## Reference

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 5,
  Proposition "Monotone trace functions", Equation (5.55)][Wolf2012QChannels];
  `Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 1103–1117.
-/

open scoped ComplexOrder MatrixOrder

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Wolf's monotone trace functions, Equation (5.55).** If `A ≤ B` are Hermitian and `f` is
non-decreasing on an order-connected set `I` containing both spectra, then
`tr f(A) ≤ tr f(B)`.

Wolf, Chapter 5, Proposition "Monotone trace functions", lines 1103–1117, additionally assumes
that `I` is open and that `f` is continuously differentiable; those hypotheses are not needed
here, so this statement contains the source proposition. -/
theorem trace_cfc_le_trace_cfc_of_le {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A ≤ B) {I : Set ℝ} (hI : I.OrdConnected) {f : ℝ → ℝ}
    (hf : MonotoneOn f I) (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) :
    (cfc f A).trace ≤ (cfc f B).trace := by
  obtain ⟨U, hU⟩ := hA.exists_unitary_cfc_le_cfc_of_le hB hAB
  have hle := hU I f hI hAI hBI hf
  have hpsd := (Matrix.le_iff.mp hle).trace_nonneg
  rw [Matrix.trace_sub, sub_nonneg] at hpsd
  refine hpsd.trans_eq ?_
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

/-- Real-part form of `Matrix.IsHermitian.trace_cfc_le_trace_cfc_of_le`, Wolf's
Equation (5.55). -/
theorem re_trace_cfc_le_re_trace_cfc_of_le {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A ≤ B) {I : Set ℝ} (hI : I.OrdConnected) {f : ℝ → ℝ}
    (hf : MonotoneOn f I) (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) :
    (cfc f A).trace.re ≤ (cfc f B).trace.re :=
  (Complex.le_def.mp (hA.trace_cfc_le_trace_cfc_of_le hB hAB hI hf hAI hBI)).1

end Matrix.IsHermitian
