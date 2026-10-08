/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceDistance
import QICLean.Entropy.ConditionalEntropy
import QICLean.Entropy.MutualInformationBasic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Continuity of conditional entropy with a controlled system

For states `ρ, σ` on `D ⊗ E` with trace distance `δ = ½‖ρ - σ‖₁`, the
Alicki–Fannes–Winter bound is
\[
  |S(D|E)_\rho - S(D|E)_\sigma|
    \le 2\delta\log d_D + (1+\delta)\,h\!\left(\frac{\delta}{1+\delta}\right)
    \le 4\sqrt\delta\,\log(e\,d_D),
\]
with `d_D = dim D` and `h` the binary entropy. Neither bound depends on the
dimension of `E`. The same bounds hold for `S(D)`, and their sum bounds the
change of the mutual information `I(D:E)`.

The proof writes `ρ - σ = δ(τ₊ - τ₋)` with `τ±` the normalized Jordan parts and
uses the common matrix `ρ + δτ₋ = σ + δτ₊` of trace `1 + δ`. The mixture
bounds of `QICLean/Entropy/ConditionalEntropy.lean` are applied to both
decompositions in unnormalized form, so `δ = 0` needs no separate case and
no division by `δ` occurs.

## Main results

* `Entropy.abs_conditionalEntropy_sub_le`: the sharp bound, Lemma 2.1, first
  inequality.
* `Entropy.abs_conditionalEntropy_sub_le_sqrt`: the bound `4√δ log(e d_D)`,
  Lemma 2.1, second inequality, with the explicit constant `C = 4`.
* `Entropy.abs_vonNeumannEntropy_sub_le`,
  `Entropy.abs_vonNeumannEntropy_sub_le_sqrt`: the same bounds for `S(D)`.
* `Entropy.abs_mutualInformation_sub_le`,
  `Entropy.abs_mutualInformation_sub_le_sqrt`: the mutual-information
  corollary, in terms of `d_D` only.

## Source attribution

Adapted from `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
under the Apache License 2.0, file
`lean/OAI/MathematicalPhysics/PEPSMove/EntropyContinuity.lean`, declarations
`conditional_abs_le_homogeneous`, `conditional_continuity`,
`log_one_add_le_two_sqrt` and `mixing_modulus_le`. Modifications: the
statements use QICLean's `vonNeumannEntropy`, `Entropy.conditionalEntropy` and
`Matrix.traceDistance`; the modulus is stated in the source form
`(1 + δ) h(δ/(1 + δ))` with Mathlib's `Real.binEntropy` and identified with the
upstream form `η(δ) - η(1 + δ)`; the square-root consequence, the bound for
`S(D)` and the mutual-information corollary are new.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Lemma 2.1 (`lem:continuity`) and its proof,
  `build/sections/01-preliminaries.tex`, lines 33–74.
* R. Alicki, M. Fannes, *Continuity of quantum conditional information*,
  J. Phys. A 37 (2004), L55–L57.
* A. Winter, *Tight uniform continuity bounds for quantum entropies*,
  Commun. Math. Phys. 347 (2016), Lemma 2.
-/

/-
Adapted from OpenAI's openai/math repository (Apache-2.0).
Upstream commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Upstream file: lean/OAI/MathematicalPhysics/PEPSMove/EntropyContinuity.lean
Upstream declaration: OAI.PolynomialPEPS.PhysicalMove.QuantumSSA.conditional_abs_le_homogeneous
Upstream URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSMove/EntropyContinuity.lean#L32-L51
Downstream declaration: Entropy.abs_conditionalEntropy_le_re_trace_mul_log_card
Changes for TNLean/QICLean: Stated for Entropy.conditionalEntropy; no Nonempty hypotheses.

Adapted from OpenAI's openai/math repository (Apache-2.0).
Upstream commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Upstream file: lean/OAI/MathematicalPhysics/PEPSMove/EntropyContinuity.lean
Upstream declaration: OAI.PolynomialPEPS.PhysicalMove.QuantumSSA.conditional_continuity
Upstream URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSMove/EntropyContinuity.lean#L70-L106
Downstream declaration: Entropy.abs_conditionalEntropy_sub_le
Changes for TNLean/QICLean: Modulus stated as (1 + δ) * Real.binEntropy (δ / (1 + δ)) and identified
with the upstream negMulLog form; trace hypotheses on the complex trace; no Nonempty hypotheses.

Adapted from OpenAI's openai/math repository (Apache-2.0).
Upstream commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Upstream file: lean/OAI/MathematicalPhysics/PEPSMove/EntropyContinuity.lean
Upstream declaration: OAI.PolynomialPEPS.PhysicalMove.QuantumSSA.log_one_add_le_two_sqrt
Upstream URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSMove/EntropyContinuity.lean#L235-L244
Downstream declaration: Entropy.log_one_add_le_two_mul_sqrt
Changes for TNLean/QICLean: Renamed; implicit nonnegativity argument.

Adapted from OpenAI's openai/math repository (Apache-2.0).
Upstream commit: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Upstream file: lean/OAI/MathematicalPhysics/PEPSMove/EntropyContinuity.lean
Upstream declaration: OAI.PolynomialPEPS.PhysicalMove.QuantumSSA.mixing_modulus_le
Upstream URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/PEPSMove/EntropyContinuity.lean#L246-L266
Downstream declaration: Entropy.negMulLog_sub_negMulLog_one_add_le
Changes for TNLean/QICLean: Renamed; implicit nonnegativity argument.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Real

noncomputable section

namespace Entropy

/-! ### The scalar modulus -/

/-- The Winter modulus in the source form equals `η(δ) - η(1 + δ)`:
`(1 + δ) h(δ/(1 + δ)) = -δ log δ + (1 + δ) log (1 + δ)`. -/
theorem one_add_mul_binEntropy_div_one_add {δ : ℝ} (hδ : 0 ≤ δ) :
    (1 + δ) * binEntropy (δ / (1 + δ)) = negMulLog δ - negMulLog (1 + δ) := by
  have hp : 0 < 1 + δ := by linarith
  have h1 : 1 - δ / (1 + δ) = (1 + δ)⁻¹ := by field_simp; ring
  rw [binEntropy, h1, inv_inv, div_eq_mul_inv, mul_inv, inv_inv]
  rcases hδ.eq_or_lt with rfl | hδ
  · simp
  rw [Real.log_mul (inv_ne_zero hδ.ne') hp.ne', Real.log_inv]
  simp only [negMulLog]
  field_simp
  ring

/-- `log (1 + x) ≤ 2 √x` for `x ≥ 0`. -/
theorem log_one_add_le_two_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : log (1 + x) ≤ 2 * √x := by
  have hp : 0 < 1 + x := by linarith
  have hl := log_le_sub_one_of_pos (sqrt_pos.mpr hp)
  rw [log_sqrt hp.le] at hl
  have hs : √(1 + x) ≤ 1 + √x := by
    have h1 := sq_sqrt hp.le
    have h2 := sq_sqrt hx
    nlinarith [sqrt_nonneg (1 + x), sqrt_nonneg x]
  linarith

/-- The mixing modulus is at most `4√δ`: `η(δ) - η(1 + δ) ≤ 4√δ`. -/
theorem negMulLog_sub_negMulLog_one_add_le {x : ℝ} (hx : 0 ≤ x) :
    negMulLog x - negMulLog (1 + x) ≤ 4 * √x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have hp : 0 < 1 + x := by linarith
  have hid : negMulLog x - negMulLog (1 + x) = log (1 + x) + x * log (1 + 1 / x) := by
    rw [show 1 + 1 / x = (1 + x) / x by field_simp; ring, log_div hp.ne' hx.ne']
    simp only [negMulLog]
    ring
  rw [hid]
  have hb := log_one_add_le_two_mul_sqrt hx.le
  have hc := mul_le_mul_of_nonneg_left
    (log_one_add_le_two_mul_sqrt (show 0 ≤ 1 / x by positivity)) hx.le
  have hroot : x * (2 * √(1 / x)) = 2 * √x := by
    rw [one_div, sqrt_inv]
    have hs := sq_sqrt hx.le
    have hn := (sqrt_pos.mpr hx).ne'
    field_simp
    nlinarith
  rw [hroot] at hc
  linarith

/-- **The square-root modulus.** For `0 ≤ δ ≤ 1` and `d ≥ 1`,
`2δ log d + (1 + δ) h(δ/(1 + δ)) ≤ 4√δ log(e d)`. -/
theorem winterModulus_le_sqrt {δ d : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hd : 1 ≤ d) :
    2 * δ * log d + (1 + δ) * binEntropy (δ / (1 + δ)) ≤ 4 * √δ * log (exp 1 * d) := by
  rw [one_add_mul_binEntropy_div_one_add hδ0, log_mul (exp_pos 1).ne' (by linarith), log_exp]
  have hm := negMulLog_sub_negMulLog_one_add_le hδ0
  have hlog : 0 ≤ log d := log_nonneg hd
  have hsq : δ ≤ √δ := by
    have h1 : √δ ≤ 1 := by simpa using sqrt_le_sqrt hδ1
    calc δ = √δ * √δ := (mul_self_sqrt hδ0).symm
      _ ≤ √δ * 1 := mul_le_mul_of_nonneg_left h1 (sqrt_nonneg _)
      _ = √δ := mul_one _
  nlinarith [sqrt_nonneg δ]

/-! ### Unnormalized two-summand bounds -/

section TwoSummands

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem conditionalEntropy_add_ge {A B : Matrix (m × n) (m × n) ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    conditionalEntropy A hA.isHermitian + conditionalEntropy B hB.isHermitian ≤
      conditionalEntropy (A + B) (hA.add hB).isHermitian := by
  have h := sum_conditionalEntropy_le ![A, B] (fun j ↦ by fin_cases j <;> simp [hA, hB])
  simpa [Fin.sum_univ_two] using h

theorem conditionalEntropy_add_le {A B : Matrix (m × n) (m × n) ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    conditionalEntropy (A + B) (hA.add hB).isHermitian ≤
      conditionalEntropy A hA.isHermitian + conditionalEntropy B hB.isHermitian +
        (negMulLog A.trace.re + negMulLog B.trace.re - negMulLog (A + B).trace.re) := by
  have h := conditionalEntropy_sum_le ![A, B] (fun j ↦ by fin_cases j <;> simp [hA, hB])
  simpa [Fin.sum_univ_two] using h

/-- For positive semidefinite `A`, `|S(D|E)_A| ≤ tr A · log d_D`. -/
theorem abs_conditionalEntropy_le_re_trace_mul_log_card {A : Matrix (m × n) (m × n) ℂ}
    (hA : A.PosSemidef) :
    |conditionalEntropy A hA.isHermitian| ≤ A.trace.re * Real.log (Fintype.card m) := by
  by_cases h0 : A.trace.re = 0
  · have hA0 := hA.eq_zero_of_re_trace_eq_zero h0
    subst hA0
    have := conditionalEntropy_real_smul 0 hA.isHermitian (by simp)
    simp only [zero_smul, zero_mul] at this
    simp [this]
  have htpos : 0 < A.trace.re := lt_of_le_of_ne hA.re_trace_nonneg (Ne.symm h0)
  set t := A.trace.re
  have hB : (t⁻¹ • A).PosSemidef := hA.smul (inv_nonneg.mpr htpos.le)
  have hB1 : (t⁻¹ • A).trace = 1 := by
    rw [trace_smul, hA.trace_eq_ofReal_re]
    simp [Complex.ext_iff, t, inv_mul_cancel₀ htpos.ne']
  have hd := abs_conditionalEntropy_le_log_card hB hB1
  have hAeq : A = t • (t⁻¹ • A) := by rw [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
  rw [conditionalEntropy_congr hAeq hA.isHermitian (hB.isHermitian.smul (IsSelfAdjoint.all t)),
    conditionalEntropy_real_smul t hB.isHermitian, abs_mul, abs_of_pos htpos]
  exact mul_le_mul_of_nonneg_left hd htpos.le

end TwoSummands

/-! ### Lemma 2.1 -/

section Continuity

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- **Continuity with a fixed controlled system, sharp form** (area-law
preprint, Lemma 2.1, first inequality of `eq:conditional-continuity`). For
states `ρ, σ` on `D ⊗ E` with `δ = ½‖ρ - σ‖₁`,
`|S(D|E)_ρ - S(D|E)_σ| ≤ 2δ log d_D + (1 + δ) h(δ/(1 + δ))`.

The bound does not involve the dimension of `E`. Source:
`01-preliminaries.tex`, lines 33–46 (statement) and 61–70 (proof). -/
theorem abs_conditionalEntropy_sub_le {ρ σ : Matrix (m × n) (m × n) ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    |conditionalEntropy ρ hρ.isHermitian - conditionalEntropy σ hσ.isHermitian| ≤
      2 * traceDistance ρ σ * Real.log (Fintype.card m) +
        (1 + traceDistance ρ σ) * binEntropy (traceDistance ρ σ / (1 + traceDistance ρ σ)) := by
  set δ := traceDistance ρ σ with hδ
  rw [one_add_mul_binEntropy_div_one_add (traceDistance_nonneg ρ σ)]
  let P : Matrix (m × n) (m × n) ℂ := (ρ - σ)⁺
  let N : Matrix (m × n) (m × n) ℂ := (ρ - σ)⁻
  have hP : P.PosSemidef := nonneg_iff_posSemidef.mp (CFC.posPart_nonneg _)
  have hN : N.PosSemidef := nonneg_iff_posSemidef.mp (CFC.negPart_nonneg _)
  have heq : ρ + N = σ + P := by
    have hh := CFC.posPart_sub_negPart (ρ - σ) (hρ.isHermitian.sub hσ.isHermitian)
    change P - N = ρ - σ at hh
    rw [add_comm σ P]
    exact (sub_eq_sub_iff_add_eq_add.mp hh).symm
  have ht := re_trace_posPart_eq_traceDistance hρ.isHermitian hσ.isHermitian (hρ1.trans hσ1.symm)
  change P.trace.re = δ ∧ N.trace.re = δ at ht
  have hρr : ρ.trace.re = 1 := by rw [hρ1, Complex.one_re]
  have hσr : σ.trace.re = 1 := by rw [hσ1, Complex.one_re]
  have hsum : (ρ + N).trace.re = 1 + δ := by rw [trace_add, Complex.add_re, hρr, ht.2]
  have hsum' : (σ + P).trace.re = 1 + δ := by rw [← heq, hsum]
  have hpa := abs_conditionalEntropy_le_re_trace_mul_log_card hP
  have hna := abs_conditionalEntropy_le_re_trace_mul_log_card hN
  rw [ht.1] at hpa
  rw [ht.2] at hna
  have h₁ := conditionalEntropy_add_ge hρ hN
  have h₂ := conditionalEntropy_add_le hσ hP
  have h₃ := conditionalEntropy_add_ge hσ hP
  have h₄ := conditionalEntropy_add_le hρ hN
  rw [hσr, ht.1, hsum', negMulLog_one, zero_add] at h₂
  rw [hρr, ht.2, hsum, negMulLog_one, zero_add] at h₄
  have hc : conditionalEntropy (ρ + N) (hρ.add hN).isHermitian =
      conditionalEntropy (σ + P) (hσ.add hP).isHermitian := conditionalEntropy_congr heq _ _
  rw [hc] at h₁ h₄
  rw [abs_le] at hpa hna ⊢
  constructor <;> linarith [hpa.1, hpa.2, hna.1, hna.2]

/-- **Continuity with a fixed controlled system, square-root form** (area-law
preprint, Lemma 2.1, second inequality of `eq:conditional-continuity`, with
`C = 4`). For states `ρ, σ` on `D ⊗ E` with `δ = ½‖ρ - σ‖₁`,
`|S(D|E)_ρ - S(D|E)_σ| ≤ 4√δ log(e d_D)`. -/
theorem abs_conditionalEntropy_sub_le_sqrt {ρ σ : Matrix (m × n) (m × n) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    |conditionalEntropy ρ hρ.isHermitian - conditionalEntropy σ hσ.isHermitian| ≤
      4 * √(traceDistance ρ σ) * Real.log (exp 1 * Fintype.card m) := by
  have : Nonempty (m × n) := Matrix.PosSemidef.nonempty_of_trace_eq_one hρ1
  have : Nonempty m := ⟨(Classical.arbitrary (m × n)).1⟩
  refine (abs_conditionalEntropy_sub_le hρ hσ hρ1 hσ1).trans
    (winterModulus_le_sqrt (traceDistance_nonneg ρ σ) (traceDistance_le_one hρ hσ hρ1 hσ1) ?_)
  exact_mod_cast Fintype.card_pos

/-- The entropy of `ρ` equals the conditional entropy of `ρ ⊗ 1` on `D ⊗ 1`. -/
theorem conditionalEntropy_submatrix_prodUnique (ρ : Matrix m m ℂ) (hρ : ρ.IsHermitian) :
    conditionalEntropy (ρ.submatrix (Equiv.prodUnique m Unit) (Equiv.prodUnique m Unit))
        ((isHermitian_submatrix_equiv _).mpr hρ) =
      vonNeumannEntropy ρ hρ - negMulLog ρ.trace.re := by
  rw [conditionalEntropy, vonNeumannEntropy_submatrix_equiv _ ρ hρ,
    vonNeumannEntropy_of_unique (α := Unit), trace_partialTraceLeft, trace_submatrix_equiv]

/-- **Continuity of the entropy, sharp form** (area-law preprint, Lemma 2.1,
"the same estimates hold for `S(D)` by making `E` trivial"). For states
`ρ, σ` on `D` with `δ = ½‖ρ - σ‖₁`,
`|S(ρ) - S(σ)| ≤ 2δ log d_D + (1 + δ) h(δ/(1 + δ))`. -/
theorem abs_vonNeumannEntropy_sub_le {ρ σ : Matrix m m ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    |vonNeumannEntropy ρ hρ.isHermitian - vonNeumannEntropy σ hσ.isHermitian| ≤
      2 * traceDistance ρ σ * Real.log (Fintype.card m) +
        (1 + traceDistance ρ σ) * binEntropy (traceDistance ρ σ / (1 + traceDistance ρ σ)) := by
  let e := Equiv.prodUnique m Unit
  have h := abs_conditionalEntropy_sub_le (hρ.submatrix e) (hσ.submatrix e)
    (by rw [trace_submatrix_equiv, hρ1]) (by rw [trace_submatrix_equiv, hσ1])
  have hd : traceDistance (ρ.submatrix e e) (σ.submatrix e e) = traceDistance ρ σ :=
    traceDistance_submatrix_equiv e hρ.isHermitian hσ.isHermitian
  rw [conditionalEntropy_submatrix_prodUnique, conditionalEntropy_submatrix_prodUnique, hd,
    hρ1, hσ1, Complex.one_re, negMulLog_one, sub_zero, sub_zero] at h
  exact h

/-- **Continuity of the entropy, square-root form.** For states `ρ, σ` on `D`
with `δ = ½‖ρ - σ‖₁`, `|S(ρ) - S(σ)| ≤ 4√δ log(e d_D)`. -/
theorem abs_vonNeumannEntropy_sub_le_sqrt {ρ σ : Matrix m m ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    |vonNeumannEntropy ρ hρ.isHermitian - vonNeumannEntropy σ hσ.isHermitian| ≤
      4 * √(traceDistance ρ σ) * Real.log (exp 1 * Fintype.card m) := by
  have : Nonempty m := Matrix.PosSemidef.nonempty_of_trace_eq_one hρ1
  refine (abs_vonNeumannEntropy_sub_le hρ hσ hρ1 hσ1).trans
    (winterModulus_le_sqrt (traceDistance_nonneg ρ σ) (traceDistance_le_one hρ hσ hρ1 hσ1) ?_)
  exact_mod_cast Fintype.card_pos

/-- The mutual information `I(D:E)_ρ = S(D)_ρ + S(E)_ρ - S(DE)_ρ` of a Hermitian
matrix on `D ⊗ E` is `S(D)_ρ - S(D|E)_ρ`. -/
theorem vonNeumannEntropy_add_sub_eq_sub_conditionalEntropy (ρ : Matrix (m × n) (m × n) ℂ)
    (hρ : ρ.IsHermitian) :
    vonNeumannEntropy (partialTraceRight ρ) (partialTraceRight_isHermitian hρ) +
        vonNeumannEntropy (partialTraceLeft ρ) (partialTraceLeft_isHermitian hρ) -
        vonNeumannEntropy ρ hρ =
      vonNeumannEntropy (partialTraceRight ρ) (partialTraceRight_isHermitian hρ) -
        conditionalEntropy ρ hρ := by
  rw [conditionalEntropy]; ring

/-- **Continuity of the mutual information** (area-law preprint, Lemma 2.1,
last sentence). For states `ρ, σ` on `D ⊗ E`, with `δ = ½‖ρ - σ‖₁` and
`δ_D = ½‖ρ_D - σ_D‖₁`, the change of `I(D:E) = S(D) + S(E) - S(DE)` is at most
the sum of the moduli for `S(D)` and `S(D|E)`. It depends on `d_D` and not on
the dimension of `E`. -/
theorem abs_mutualInformation_sub_le {ρ σ : Matrix (m × n) (m × n) ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    |(vonNeumannEntropy (partialTraceRight ρ) (partialTraceRight_isHermitian hρ.isHermitian) +
          vonNeumannEntropy (partialTraceLeft ρ) (partialTraceLeft_isHermitian hρ.isHermitian) -
          vonNeumannEntropy ρ hρ.isHermitian) -
        (vonNeumannEntropy (partialTraceRight σ) (partialTraceRight_isHermitian hσ.isHermitian) +
          vonNeumannEntropy (partialTraceLeft σ) (partialTraceLeft_isHermitian hσ.isHermitian) -
          vonNeumannEntropy σ hσ.isHermitian)| ≤
      (2 * traceDistance (partialTraceRight ρ) (partialTraceRight σ) *
          Real.log (Fintype.card m) +
        (1 + traceDistance (partialTraceRight ρ) (partialTraceRight σ)) *
          binEntropy (traceDistance (partialTraceRight ρ) (partialTraceRight σ) /
            (1 + traceDistance (partialTraceRight ρ) (partialTraceRight σ)))) +
      (2 * traceDistance ρ σ * Real.log (Fintype.card m) +
        (1 + traceDistance ρ σ) * binEntropy (traceDistance ρ σ / (1 + traceDistance ρ σ))) := by
  have hD := abs_vonNeumannEntropy_sub_le hρ.partialTraceRight hσ.partialTraceRight
    (by rw [trace_partialTraceRight, hρ1]) (by rw [trace_partialTraceRight, hσ1])
  have hC := abs_conditionalEntropy_sub_le hρ hσ hρ1 hσ1
  rw [vonNeumannEntropy_add_sub_eq_sub_conditionalEntropy,
    vonNeumannEntropy_add_sub_eq_sub_conditionalEntropy]
  rw [abs_le] at hD hC ⊢
  constructor <;> linarith [hD.1, hD.2, hC.1, hC.2]

/-- **Continuity of the mutual information, square-root form.** For states
`ρ, σ` on `D ⊗ E` with `δ = ½‖ρ - σ‖₁`,
`|I(D:E)_ρ - I(D:E)_σ| ≤ 8√δ log(e d_D)`, independently of the dimension of
`E`. -/
theorem abs_mutualInformation_sub_le_sqrt {ρ σ : Matrix (m × n) (m × n) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    |(vonNeumannEntropy (partialTraceRight ρ) (partialTraceRight_isHermitian hρ.isHermitian) +
          vonNeumannEntropy (partialTraceLeft ρ) (partialTraceLeft_isHermitian hρ.isHermitian) -
          vonNeumannEntropy ρ hρ.isHermitian) -
        (vonNeumannEntropy (partialTraceRight σ) (partialTraceRight_isHermitian hσ.isHermitian) +
          vonNeumannEntropy (partialTraceLeft σ) (partialTraceLeft_isHermitian hσ.isHermitian) -
          vonNeumannEntropy σ hσ.isHermitian)| ≤
      8 * √(traceDistance ρ σ) * Real.log (exp 1 * Fintype.card m) := by
  have : Nonempty (m × n) := Matrix.PosSemidef.nonempty_of_trace_eq_one hρ1
  have : Nonempty m := ⟨(Classical.arbitrary (m × n)).1⟩
  have hD := abs_vonNeumannEntropy_sub_le_sqrt hρ.partialTraceRight hσ.partialTraceRight
    (by rw [trace_partialTraceRight, hρ1]) (by rw [trace_partialTraceRight, hσ1])
  have hC := abs_conditionalEntropy_sub_le_sqrt hρ hσ hρ1 hσ1
  have hcontr := traceDistance_partialTraceRight_le hρ.isHermitian hσ.isHermitian
    (hρ1.trans hσ1.symm)
  have hlog : 0 ≤ Real.log (exp 1 * Fintype.card m) := by
    rw [log_mul (exp_pos 1).ne' (by exact_mod_cast Fintype.card_ne_zero), log_exp]
    have : (1 : ℝ) ≤ Fintype.card m := by exact_mod_cast Fintype.card_pos
    linarith [log_nonneg this]
  have hsq : √(traceDistance (partialTraceRight ρ) (partialTraceRight σ)) ≤
      √(traceDistance ρ σ) := sqrt_le_sqrt hcontr
  rw [vonNeumannEntropy_add_sub_eq_sub_conditionalEntropy,
    vonNeumannEntropy_add_sub_eq_sub_conditionalEntropy]
  have h4 : 4 * √(traceDistance (partialTraceRight ρ) (partialTraceRight σ)) *
      Real.log (exp 1 * Fintype.card m) ≤
      4 * √(traceDistance ρ σ) * Real.log (exp 1 * Fintype.card m) := by gcongr
  rw [abs_le] at hD hC ⊢
  constructor <;> linarith [hD.1, hD.2, hC.1, hC.2]

/-- **Continuity of `Entropy.mutualInformation`** on `Fin dA ⊗ Fin dB`, the
square-root form of `abs_mutualInformation_sub_le_sqrt`: the bound
`8√δ log(e dA)` does not involve `dB`. -/
theorem abs_mutualInformation_sub_le_sqrt_fin {dA dB : ℕ}
    {ρ σ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    |mutualInformation ρ hρ.isHermitian - mutualInformation σ hσ.isHermitian| ≤
      8 * √(traceDistance ρ σ) * Real.log (exp 1 * dA) := by
  have h := abs_mutualInformation_sub_le_sqrt hρ hσ hρ1 hσ1
  rw [Fintype.card_fin] at h
  exact h

end Continuity

end Entropy

end
