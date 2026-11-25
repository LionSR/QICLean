/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Optimization.SemidefiniteProgram
import QICLean.Analysis.TraceNorm.TraceNormContractivity

/-!
# Quantum Neyman–Pearson: optimal discrimination of two states

Wolf, *Quantum Channels & Operations*, Section 8.5, Theorem "Quantum
Neyman–Pearson", Equations (8.40)–(8.42),
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 525–566.

Two hypotheses `ρ` and `σ` with priors `p` and `1 - p` are tested by a
two-outcome measurement with effects `P` and `1 - P`. The average error
probability is Equation (8.40),
`e(P) = p tr[ρ(1 - P)] + (1 - p) tr[σ P]`. For every effect `0 ≤ P ≤ 1`,
Equation (8.41) gives `e(P) ≥ (1 - ‖pρ - (1 - p)σ‖₁) / 2`.

## Correction of the equality clause

Wolf states that equality holds iff `P` is the projection onto the positive
part of `A = pρ - (1 - p)σ`. That fails when `A` has a nonzero kernel: the
action of `P` there does not change the error. For `p = 1/2` and `ρ = σ`
every effect is optimal (`Matrix.hypothesisTestError_half_self`). The proof
in the source (lines 562–563, after Equation (8.42)) gives the correct
condition `P A₊ = A₊` and `P A₋ = 0`, which is
`Matrix.hypothesisTestError_eq_iff`. The printed clause holds when `A` is invertible
(`Matrix.hypothesisTestError_eq_iff_eq_posPartSupportProj`). See
`docs/paper-gaps/wolf_ch8_neyman_pearson_kernel.tex`.

The trace norm is `Re tr |A|`, written through `CFC.abs`, so the index type is
an arbitrary finite type; `Matrix.hypothesisTestError_ge_traceNorm` restates
the bound with `Matrix.traceNorm` on `Fin D`. The states need only be
Hermitian of unit trace and the prior `p` is an arbitrary real number; in
particular every pair of density matrices and every prior in `[0, 1]` is
covered.

## Main results

* `Matrix.hypothesisTestError`: Equation (8.40).
* `Matrix.hypothesisTestError_sub_eq`: the exact excess error over the bound.
* `Matrix.hypothesisTestError_ge`: Equation (8.41).
* `Matrix.hypothesisTestError_eq_iff`: the corrected equality condition.
* `Matrix.isLeast_hypothesisTestError`: the bound is the minimum error,
  attained by the support projection of the positive part.
-/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The average error probability of the two-outcome test `{P, 1 - P}`
guessing `ρ` on outcome `P`, with prior `p` for `ρ` and `1 - p` for `σ`:
`e(P) = p tr[ρ(1 - P)] + (1 - p) tr[σ P]`.

Wolf, Equation (8.40), `ch08_distance_measures.tex`, lines 543–546. -/
def hypothesisTestError (p : ℝ) (ρ σ P : Matrix n n ℂ) : ℝ :=
  p * (ρ * (1 - P)).trace.re + (1 - p) * (σ * P).trace.re

/-- The support projection of the positive part fixes the positive part. -/
lemma IsHermitian.posPartSupportProj_mul_posPart {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : hA.posPartSupportProj * A⁺ = A⁺ := by
  rw [← hA.posPartSupportProj_mul_self, ← Matrix.mul_assoc,
    hA.posPartSupportProj_mul_posPartSupportProj]

/-- The support projection of the positive part annihilates the negative
part. -/
lemma IsHermitian.posPartSupportProj_mul_negPart {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : hA.posPartSupportProj * A⁻ = 0 := by
  have h := congrArg (hA.posPartSupportProj * ·)
    (CFC.posPart_sub_negPart A (isSelfAdjoint_iff.mpr hA))
  simp only [Matrix.mul_sub, hA.posPartSupportProj_mul_self,
    hA.posPartSupportProj_mul_posPart] at h
  exact sub_eq_self.mp h

omit [DecidableEq n] in
private lemma re_trace_smul (r : ℝ) (X : Matrix n n ℂ) :
    (r • X).trace.re = r * X.trace.re := by
  rw [trace_smul, Complex.smul_re, smul_eq_mul]

/-- **Excess error of a test.** For Hermitian `ρ, σ` of unit trace, a real
prior `p`, and every matrix `P`, with `A = pρ - (1 - p)σ`,
`e(P) - (1 - ‖A‖₁)/2 = tr[(1 - P) A₊] + tr[P A₋]`.

This is the computation in Wolf's proof of Theorem "Quantum Neyman–Pearson",
Equation (8.42) and the following lines, `ch08_distance_measures.tex`,
lines 557–564. -/
theorem hypothesisTestError_sub_eq {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (p : ℝ)
    (P : Matrix n n ℂ) :
    hypothesisTestError p ρ σ P -
        (1 - (CFC.abs (p • ρ - (1 - p) • σ)).trace.re) / 2 =
      ((1 - P) * (p • ρ - (1 - p) • σ)⁺).trace.re +
        (P * (p • ρ - (1 - p) • σ)⁻).trace.re := by
  set A := p • ρ - (1 - p) • σ with hAdef
  have hA : A.IsHermitian :=
    (hρ.smul (IsSelfAdjoint.all p)).sub (hσ.smul (IsSelfAdjoint.all (1 - p)))
  have hsa : IsSelfAdjoint A := isSelfAdjoint_iff.mpr hA
  have habs : (CFC.abs A).trace.re = (A⁺).trace.re + (A⁻).trace.re := by
    rw [← CFC.posPart_add_negPart A hsa, trace_add, Complex.add_re]
  have hdiff := congrArg (fun X : Matrix n n ℂ ↦ X.trace.re)
    (CFC.posPart_sub_negPart A hsa)
  have hdiffP := congrArg (fun X : Matrix n n ℂ ↦ (P * X).trace.re)
    (CFC.posPart_sub_negPart A hsa)
  simp only [trace_sub, Complex.sub_re, Matrix.mul_sub] at hdiff hdiffP
  rw [hAdef, trace_sub, Complex.sub_re, re_trace_smul, re_trace_smul, hρ1, hσ1,
    Complex.one_re] at hdiff
  rw [hAdef, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, trace_sub,
    Complex.sub_re, re_trace_smul, re_trace_smul, trace_mul_comm P ρ,
    trace_mul_comm P σ] at hdiffP
  rw [hypothesisTestError, habs, Matrix.sub_mul, Matrix.one_mul, trace_sub,
    Complex.sub_re, Matrix.mul_sub, Matrix.mul_one, trace_sub, Complex.sub_re,
    hρ1, Complex.one_re]
  linarith

/-- **Quantum Neyman–Pearson bound.** For Hermitian `ρ, σ` of unit trace, a
real prior `p`, and an effect `0 ≤ P ≤ 1`,
`e(P) ≥ (1 - ‖pρ - (1 - p)σ‖₁) / 2`.

Wolf, Theorem "Quantum Neyman–Pearson", Equation (8.41),
`ch08_distance_measures.tex`, lines 548–555. -/
theorem hypothesisTestError_ge {ρ σ P : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (p : ℝ)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    (1 - (CFC.abs (p • ρ - (1 - p) • σ)).trace.re) / 2 ≤
      hypothesisTestError p ρ σ P := by
  have h := hypothesisTestError_sub_eq hρ hσ hρ1 hσ1 p P
  have h₁ := (Matrix.le_iff.mp hP1).re_trace_mul_nonneg
    (nonneg_iff_posSemidef.mp (CFC.posPart_nonneg (p • ρ - (1 - p) • σ)))
  have h₂ := (nonneg_iff_posSemidef.mp hP0).re_trace_mul_nonneg
    (nonneg_iff_posSemidef.mp (CFC.negPart_nonneg (p • ρ - (1 - p) • σ)))
  linarith

omit [DecidableEq n] in
/-- Two positive-semidefinite matrices whose trace pairing has zero real part
have zero product. -/
private lemma PosSemidef.mul_eq_zero_of_re_trace_mul_eq_zero {X Y : Matrix n n ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (h : (X * Y).trace.re = 0) :
    X * Y = 0 := by
  apply hX.mul_eq_zero_of_trace_mul_eq_zero hY
  have him := (Complex.nonneg_iff.mp (hX.trace_mul_nonneg hY)).2
  exact Complex.ext h him.symm

/-- **Corrected equality clause of quantum Neyman–Pearson.** An effect
`0 ≤ P ≤ 1` attains the bound of Equation (8.41) iff `P A₊ = A₊` and
`P A₋ = 0`, where `A = pρ - (1 - p)σ`. The action of `P` on the kernel of `A`
is unconstrained.

Wolf, proof of Theorem "Quantum Neyman–Pearson",
`ch08_distance_measures.tex`, lines 562–563. **Local fix (kernel freedom in
the equality clause):** the printed statement (line 554) asserts that `P`
must be the projection onto the positive part; see
`docs/paper-gaps/wolf_ch8_neyman_pearson_kernel.tex`. -/
theorem hypothesisTestError_eq_iff {ρ σ P : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (p : ℝ)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    hypothesisTestError p ρ σ P =
        (1 - (CFC.abs (p • ρ - (1 - p) • σ)).trace.re) / 2 ↔
      P * (p • ρ - (1 - p) • σ)⁺ = (p • ρ - (1 - p) • σ)⁺ ∧
        P * (p • ρ - (1 - p) • σ)⁻ = 0 := by
  set A := p • ρ - (1 - p) • σ with hAdef
  have h := hypothesisTestError_sub_eq hρ hσ hρ1 hσ1 p P
  rw [← hAdef] at h
  have hQ : (1 - P).PosSemidef := Matrix.le_iff.mp hP1
  have hPpsd : P.PosSemidef := nonneg_iff_posSemidef.mp hP0
  have hpos : (A⁺).PosSemidef := nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)
  have hneg : (A⁻).PosSemidef := nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)
  have h₁ := hQ.re_trace_mul_nonneg hpos
  have h₂ := hPpsd.re_trace_mul_nonneg hneg
  constructor
  · intro heq
    have h₁' : ((1 - P) * A⁺).trace.re = 0 := by linarith
    have h₂' : (P * A⁻).trace.re = 0 := by linarith
    refine ⟨?_, PosSemidef.mul_eq_zero_of_re_trace_mul_eq_zero hPpsd hneg h₂'⟩
    have h0 := PosSemidef.mul_eq_zero_of_re_trace_mul_eq_zero hQ hpos h₁'
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h0
    exact h0.symm
  · rintro ⟨hp, hn⟩
    rw [Matrix.sub_mul, Matrix.one_mul, hp, sub_self, hn] at h
    simp only [trace_zero, Complex.zero_re, add_zero] at h
    linarith

/-- The support projection of the positive part of `pρ - (1 - p)σ` attains
the bound of Equation (8.41).

Wolf, Theorem "Quantum Neyman–Pearson", `ch08_distance_measures.tex`,
lines 554 and 562–563. -/
theorem hypothesisTestError_posPartSupportProj {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) (p : ℝ)
    (hA : (p • ρ - (1 - p) • σ).IsHermitian) :
    hypothesisTestError p ρ σ hA.posPartSupportProj =
      (1 - (CFC.abs (p • ρ - (1 - p) • σ)).trace.re) / 2 :=
  (hypothesisTestError_eq_iff hρ hσ hρ1 hσ1 p
    (nonneg_iff_posSemidef.mpr hA.posPartSupportProj_posSemidef)
    hA.posPartSupportProj_le_one).mpr
    ⟨hA.posPartSupportProj_mul_posPart, hA.posPartSupportProj_mul_negPart⟩

/-- **Optimal error of binary discrimination.** Over all effects
`0 ≤ P ≤ 1`, the least average error is `(1 - ‖pρ - (1 - p)σ‖₁) / 2`.

Wolf, Theorem "Quantum Neyman–Pearson" and Equation (8.42),
`ch08_distance_measures.tex`, lines 548–566. -/
theorem isLeast_hypothesisTestError {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) (p : ℝ) :
    IsLeast {e | ∃ P : Matrix n n ℂ, 0 ≤ P ∧ P ≤ 1 ∧ hypothesisTestError p ρ σ P = e}
      ((1 - (CFC.abs (p • ρ - (1 - p) • σ)).trace.re) / 2) := by
  have hA : (p • ρ - (1 - p) • σ).IsHermitian :=
    (hρ.smul (IsSelfAdjoint.all p)).sub (hσ.smul (IsSelfAdjoint.all (1 - p)))
  refine ⟨⟨hA.posPartSupportProj,
    nonneg_iff_posSemidef.mpr hA.posPartSupportProj_posSemidef,
    hA.posPartSupportProj_le_one,
    hypothesisTestError_posPartSupportProj hρ hσ hρ1 hσ1 p hA⟩, ?_⟩
  rintro e ⟨P, hP0, hP1, rfl⟩
  exact hypothesisTestError_ge hρ hσ hρ1 hσ1 p hP0 hP1

/-- **The printed equality clause for invertible `pρ - (1 - p)σ`.** When
`A = pρ - (1 - p)σ` is invertible, an effect attains the bound of
Equation (8.41) iff it is the projection onto the positive part of `A`.

Wolf, Theorem "Quantum Neyman–Pearson", `ch08_distance_measures.tex`,
line 554. **Scope restriction (invertible difference):** without
invertibility the clause fails; see
`docs/paper-gaps/wolf_ch8_neyman_pearson_kernel.tex` and
`Matrix.hypothesisTestError_half_self`. -/
theorem hypothesisTestError_eq_iff_eq_posPartSupportProj {ρ σ P : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) (p : ℝ) (hA : (p • ρ - (1 - p) • σ).IsHermitian)
    (hunit : IsUnit (p • ρ - (1 - p) • σ)) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    hypothesisTestError p ρ σ P =
        (1 - (CFC.abs (p • ρ - (1 - p) • σ)).trace.re) / 2 ↔
      P = hA.posPartSupportProj := by
  constructor
  · intro heq
    obtain ⟨hp, hn⟩ := (hypothesisTestError_eq_iff hρ hσ hρ1 hσ1 p hP0 hP1).mp heq
    have hsa : IsSelfAdjoint (p • ρ - (1 - p) • σ) := isSelfAdjoint_iff.mpr hA
    have hPA : P * (p • ρ - (1 - p) • σ) =
        hA.posPartSupportProj * (p • ρ - (1 - p) • σ) := by
      rw [hA.posPartSupportProj_mul_self]
      conv_lhs => rw [← CFC.posPart_sub_negPart _ hsa]
      rw [Matrix.mul_sub, hp, hn, sub_zero]
    exact (hunit.mul_left_inj).mp hPA
  · rintro rfl
    exact hypothesisTestError_posPartSupportProj hρ hσ hρ1 hσ1 p hA

/-- **Kernel freedom in the equality clause.** With equal priors and equal
hypotheses every effect attains the bound of Equation (8.41), although the
projection onto the positive part of `pρ - (1 - p)σ = 0` is zero.

This is the counterexample to the printed equality clause of Wolf, Theorem
"Quantum Neyman–Pearson", `ch08_distance_measures.tex`, line 554; see
`docs/paper-gaps/wolf_ch8_neyman_pearson_kernel.tex`. -/
theorem hypothesisTestError_half_self {ρ : Matrix n n ℂ} (hρ1 : ρ.trace = 1)
    (P : Matrix n n ℂ) :
    hypothesisTestError (1 / 2) ρ ρ P =
      (1 - (CFC.abs ((1 / 2 : ℝ) • ρ - (1 - 1 / 2 : ℝ) • ρ)).trace.re) / 2 := by
  have h : (1 / 2 : ℝ) • ρ - (1 - 1 / 2 : ℝ) • ρ = 0 := by norm_num
  rw [h, CFC.abs_zero, hypothesisTestError, Matrix.mul_sub, Matrix.mul_one,
    trace_sub, Complex.sub_re, hρ1]
  simp only [trace_zero, Complex.zero_re, Complex.one_re]
  ring

/-- Equation (8.41) with the trace norm `Matrix.traceNorm` on `Fin D`.

Wolf, Theorem "Quantum Neyman–Pearson", Equation (8.41),
`ch08_distance_measures.tex`, lines 548–555. -/
theorem hypothesisTestError_ge_traceNorm {D : ℕ} {ρ σ P : Matrix (Fin D) (Fin D) ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) (p : ℝ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    (1 - traceNorm (p • ρ - (1 - p) • σ)) / 2 ≤ hypothesisTestError p ρ σ P := by
  rw [traceNorm_eq_re_trace_abs]
  exact hypothesisTestError_ge hρ hσ hρ1 hσ1 p hP0 hP1

end Matrix
