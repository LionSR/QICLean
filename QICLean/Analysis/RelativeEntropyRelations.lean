/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.KleinInequality

/-!
# Relations among relative entropies

Wolf, *Quantum Channels & Operations*, Section 8.4, Theorem "Relation among
relative entropies", Equations (8.36)–(8.39),
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 490–521.

For positive-semidefinite `ρ, σ` Wolf sets
`S⁽ᵅ⁾(ρ|σ) = tr[ρ - ρᵅ σ¹⁻ᵅ] / (1 - α)` and proves, for `α ≤ 1 ≤ β`,
`S⁽ᵅ⁾(ρ|σ) ≤ S(ρ|σ) ≤ S⁽ᵝ⁾(ρ|σ)` (Equation (8.38)), where
`S(ρ|σ) = tr[ρ(log ρ - log σ)]`.

## Proof

Following Wolf, write `ρ = ∑ᵢ λᵢ |xᵢ⟩⟨xᵢ|`, `σ = ∑ⱼ μⱼ |yⱼ⟩⟨yⱼ|` and
`Pᵢⱼ = |⟨xᵢ|yⱼ⟩|²`. Every trace `Re tr[f(ρ) g(σ)]` equals
`∑ᵢⱼ f(λᵢ) g(μⱼ) Pᵢⱼ` (`Matrix.re_trace_cfc_mul_cfc_eq_double_sum`), which is
Equations (8.36)–(8.37). For every real `a` the scalar bound
`λ - λᵃ μ¹⁻ᵃ ≤ (1 - a) λ (log λ - log μ)` for `λ, μ > 0` comes from
`log x ≤ x - 1` at `x = (μ/λ)¹⁻ᵃ`; this is Equation (8.39) with
`s = 1 - α` or `s = β - 1`. Summing gives
`tr ρ - tr[ρᵃ σ¹⁻ᵃ] ≤ (1 - a) S(ρ|σ)`
(`Matrix.re_trace_sub_le_mul_quantumRelativeEntropy`), and dividing by `1 - a`
gives both halves of Equation (8.38).

## Conventions and scope

Powers are the continuous functional calculus: negative powers invert on the
support and vanish on the kernel, and `X ^ (0 : ℝ) = 1`. The relative entropy is
`quantumRelativeEntropy`, which uses the totalized logarithm `log 0 = 0`.

**Scope restriction (finite relative entropy):** the theorems assume
`ker σ ⊆ ker ρ`. Wolf's footnote (line 474) sets the entropies to `+∞`
otherwise; then the right-hand inequality reads `∞ ≤ ∞` and the left one
`S⁽ᵅ⁾ ≤ ∞`, and the totalized trace-log expression no longer represents `S`.
The endpoints `α = 1` and `β = 1` are excluded: there `S⁽¹⁾` is defined only
as a limit. For `α < 0` the statement uses the support-inverse convention without
Wolf's assignment `S⁽ᵅ⁾ = ∞` when `ker ρ ⊄ ker σ`; under that assignment the left
inequality is false. See `docs/paper-gaps/wolf_ch8_relative_entropy_relations.tex`.

## Main results

* `Matrix.tsallisRelativeEntropy`: Wolf's `S⁽ᵅ⁾` in Equation (8.38).
* `Matrix.re_trace_cfc_mul_cfc_eq_double_sum`: Equations (8.36)–(8.37).
* `Matrix.tsallisRelativeEntropy_le_quantumRelativeEntropy`: left half of
  Equation (8.38).
* `Matrix.quantumRelativeEntropy_le_tsallisRelativeEntropy`: right half of
  Equation (8.38).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Finset

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Wolf's Tsallis-type relative entropy for positive-semidefinite matrices,
`S⁽ᵅ⁾(ρ|σ) = tr[ρ - ρᵅ σ¹⁻ᵅ] / (1 - α)`, with powers by the continuous
functional calculus.

Wolf, Theorem "Relation among relative entropies",
`ch08_distance_measures.tex`, lines 501–504. -/
def tsallisRelativeEntropy (α : ℝ) (ρ σ : Matrix n n ℂ) : ℝ :=
  (ρ - ρ ^ α * σ ^ (1 - α)).trace.re / (1 - α)

/-- **Equations (8.36)–(8.37).** For Hermitian `ρ, σ` and real functions
`f, g`, `Re tr[f(ρ) g(σ)] = ∑ᵢⱼ f(λᵢ) g(μⱼ) |⟨xᵢ|yⱼ⟩|²`, where `λ, x` and
`μ, y` are the eigenvalues and eigenvectors of `ρ` and `σ`.

Wolf, `ch08_distance_measures.tex`, lines 487–496. -/
theorem re_trace_cfc_mul_cfc_eq_double_sum {ρ σ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f g : ℝ → ℝ) :
    (hρ.cfc f * hσ.cfc g).trace.re =
      ∑ i, ∑ j, f (hρ.eigenvalues i) * g (hσ.eigenvalues j) *
        Complex.normSq (((star (hρ.eigenvectorUnitary : Matrix n n ℂ)) *
          (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j) := by
  set Vρ : Matrix n n ℂ := (hρ.eigenvectorUnitary : Matrix n n ℂ)
  set Vσ : Matrix n n ℂ := (hσ.eigenvectorUnitary : Matrix n n ℂ)
  set dp : n → ℂ := fun i => ((f (hρ.eigenvalues i) : ℝ) : ℂ)
  set dm : n → ℂ := fun j => ((g (hσ.eigenvalues j) : ℝ) : ℂ)
  set W : Matrix n n ℂ := star Vρ * Vσ with hW
  have hstarW : star W = star Vσ * Vρ := by rw [hW, star_mul, star_star]
  have htr : (hρ.cfc f * hσ.cfc g).trace = trace (diagonal dp * W * diagonal dm * star W) := by
    rw [hρ.cfc_form f, hσ.cfc_form g, hstarW,
      show Vρ * diagonal dp * star Vρ * (Vσ * diagonal dm * star Vσ)
          = Vρ * (diagonal dp * (star Vρ * Vσ) * diagonal dm * star Vσ) by
        simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm Vρ _, ← hW]
    simp only [Matrix.mul_assoc]
  rw [htr, TNLean.Klein.trace_diag_conj, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hnsq : W i j * star (W i j) = ((Complex.normSq (W i j) : ℝ) : ℂ) := by
    rw [Complex.star_def, mul_comm]
    exact Complex.normSq_eq_conj_mul_self.symm
  rw [hnsq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Under `ker σ ⊆ ker ρ`, every eigenvector of `σ` with eigenvalue zero is
orthogonal to every eigenvector of `ρ` with nonzero eigenvalue. -/
theorem eigenvalues_mul_normSq_eq_zero_of_ker_le {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.IsHermitian)
    (hsupp : ∀ v : n → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0) (i j : n)
    (hj : hσ.eigenvalues j = 0) :
    hρ.isHermitian.eigenvalues i *
        Complex.normSq (((star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) *
          (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j) = 0 := by
  set g : ℝ → ℝ := fun x => if x = 0 then 1 else 0
  have hzero : (ρ * hσ.cfc g).trace.re = 0 := by
    rw [TNLean.Klein.re_trace_mul_cfc_eq_diag_sum hσ g]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : hσ.eigenvalues k = 0
    · have hker : ρ *ᵥ ⇑(hσ.eigenvectorBasis k) = 0 := by
        apply hsupp
        rw [hσ.mulVec_eigenvectorBasis k, hk, zero_smul]
      rw [TNLean.Klein.diag_weight_eq_zero_of_kernel hσ k hker, Complex.zero_re, zero_mul]
    · simp [g, hk]
  rw [TNLean.Klein.re_trace_mul_cfc_eq_double_sum hρ.isHermitian hσ g] at hzero
  have hnonneg : ∀ i' j', 0 ≤ hρ.isHermitian.eigenvalues i' * g (hσ.eigenvalues j') *
      Complex.normSq (((star (hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ)) *
        (hσ.eigenvectorUnitary : Matrix n n ℂ)) i' j') := fun i' j' => by
    have hl' := hρ.eigenvalues_nonneg i'
    have hg' : 0 ≤ g (hσ.eigenvalues j') := by simp only [g]; split_ifs <;> norm_num
    exact mul_nonneg (mul_nonneg hl' hg') (Complex.normSq_nonneg _)
  have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i' _ =>
    Finset.sum_nonneg fun j' _ => hnonneg i' j').mp hzero i (Finset.mem_univ _)
  have hij := (Finset.sum_eq_zero_iff_of_nonneg fun j' _ => hnonneg i j').mp hi j
    (Finset.mem_univ _)
  simpa [g, hj] using hij

/-- The scalar form of Equation (8.39): for `λ, μ ≥ 0` with `λ = 0` or `μ > 0`
and every real `a`, `λ - λᵃ μ¹⁻ᵃ ≤ (1 - a)(λ log λ - λ log μ)`.

Wolf, proof of Theorem "Relation among relative entropies",
`ch08_distance_measures.tex`, lines 509–520. -/
theorem sub_rpow_mul_rpow_le_mul_log {l m : ℝ} (hl : 0 ≤ l) (hm : 0 ≤ m)
    (hlm : m = 0 → l = 0) (a : ℝ) :
    l - l ^ a * m ^ (1 - a) ≤ (1 - a) * (l * Real.log l - l * Real.log m) := by
  rcases hl.eq_or_lt with rfl | hl
  · simp only [zero_sub, zero_mul, sub_zero, mul_zero, neg_nonpos]
    exact mul_nonneg (Real.rpow_nonneg le_rfl a) (Real.rpow_nonneg hm _)
  rcases hm.eq_or_lt with rfl | hm
  · exact absurd (hlm rfl) hl.ne'
  set x := (m / l) ^ (1 - a) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos (div_pos hm hl) _
  have hlog : Real.log x = (1 - a) * (Real.log m - Real.log l) := by
    rw [hx, Real.log_rpow (div_pos hm hl), Real.log_div hm.ne' hl.ne']
  have hlx : l * x = l ^ a * m ^ (1 - a) := by
    calc l * x = l * (m ^ (1 - a) / l ^ (1 - a)) := by rw [hx, Real.div_rpow hm.le hl.le]
      _ = (l ^ (1 : ℝ) / l ^ (1 - a)) * m ^ (1 - a) := by rw [Real.rpow_one]; ring
      _ = l ^ a * m ^ (1 - a) := by rw [← Real.rpow_sub hl, sub_sub_cancel]
  have h := Real.log_le_sub_one_of_pos hxpos
  rw [hlog] at h
  have h' := mul_le_mul_of_nonneg_left h hl.le
  nlinarith [h', hlx]

/-- **The common bound behind Equation (8.38).** For positive-semidefinite
`ρ, σ` with `ker σ ⊆ ker ρ` and every real `a`,
`tr ρ - tr[ρᵃ σ¹⁻ᵃ] ≤ (1 - a) S(ρ|σ)`.

Wolf, proof of Theorem "Relation among relative entropies",
`ch08_distance_measures.tex`, lines 509–520. -/
theorem re_trace_sub_le_mul_quantumRelativeEntropy {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : n → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0) (a : ℝ) :
    (ρ - ρ ^ a * σ ^ (1 - a)).trace.re ≤ (1 - a) * quantumRelativeEntropy ρ σ := by
  have hρh := hρ.isHermitian
  have hσh := hσ.isHermitian
  set P : n → n → ℝ := fun i j => Complex.normSq
    (((star (hρh.eigenvectorUnitary : Matrix n n ℂ)) *
      (hσh.eigenvectorUnitary : Matrix n n ℂ)) i j) with hP
  have hone : (1 : Matrix n n ℂ) = hσh.cfc (fun _ => 1) := by
    rw [← hσh.cfc_eq, cfc_const_one ℝ σ]
  have htrρ : ρ.trace.re = ∑ i, ∑ j, id (hρh.eigenvalues i) * 1 * P i j := by
    rw [← re_trace_cfc_mul_cfc_eq_double_sum hρh hσh id (fun _ => 1), hρh.cfc_id, ← hone,
      Matrix.mul_one]
  have hpow : (ρ ^ a * σ ^ (1 - a)).trace.re =
      ∑ i, ∑ j, hρh.eigenvalues i ^ a * hσh.eigenvalues j ^ (1 - a) * P i j := by
    rw [← re_trace_cfc_mul_cfc_eq_double_sum hρh hσh (· ^ a) (· ^ (1 - a)),
      CFC.rpow_eq_cfc_real hρ.nonneg, CFC.rpow_eq_cfc_real hσ.nonneg, hρh.cfc_eq, hσh.cfc_eq]
  have hlogρ : (ρ * CFC.log ρ).trace.re =
      ∑ i, ∑ j, (hρh.eigenvalues i * Real.log (hρh.eigenvalues i)) * 1 * P i j := by
    rw [← re_trace_cfc_mul_cfc_eq_double_sum hρh hσh (fun x => x * Real.log x) (fun _ => 1),
      ← hone, Matrix.mul_one]
    congr 2
    calc ρ * CFC.log ρ = hρh.cfc id * hρh.cfc Real.log := by
          rw [hρh.cfc_id, CFC.log, hρh.cfc_eq]
      _ = hρh.cfc (fun x => id x * Real.log x) := (hρh.cfc_mul id Real.log).symm
  have hlogσ : (ρ * CFC.log σ).trace.re =
      ∑ i, ∑ j, id (hρh.eigenvalues i) * Real.log (hσh.eigenvalues j) * P i j := by
    rw [← re_trace_cfc_mul_cfc_eq_double_sum hρh hσh id Real.log, hρh.cfc_id, CFC.log,
      hσh.cfc_eq]
  rw [quantumRelativeEntropy_eq_trace_mul_log_sub, trace_sub, Complex.sub_re, htrρ, hpow,
    hlogρ, hlogσ, ← sub_nonneg]
  simp only [id, mul_one, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have hPnn : 0 ≤ P i j := Complex.normSq_nonneg _
  have hl := hρ.eigenvalues_nonneg i
  have hm := hσ.eigenvalues_nonneg j
  by_cases hPz : P i j = 0
  · simp [hPz]
  have hlm : hσh.eigenvalues j = 0 → hρh.eigenvalues i = 0 := fun hj => by
    have h := eigenvalues_mul_normSq_eq_zero_of_ker_le hρ hσh hsupp i j hj
    exact (mul_eq_zero.mp h).resolve_right hPz
  have hs := sub_rpow_mul_rpow_le_mul_log hl hm hlm a
  have hPpos : 0 < P i j := lt_of_le_of_ne hPnn (Ne.symm hPz)
  nlinarith [mul_le_mul_of_nonneg_right hs hPnn]

/-- **Left half of Equation (8.38).** For positive-semidefinite `ρ, σ` with
`ker σ ⊆ ker ρ` and `α < 1`, `S⁽ᵅ⁾(ρ|σ) ≤ S(ρ|σ)`.

Wolf, Theorem "Relation among relative entropies", Equation (8.38),
`ch08_distance_measures.tex`, lines 500–506. **Scope restriction (finite
relative entropy, `α ≠ 1`):** see
`docs/paper-gaps/wolf_ch8_relative_entropy_relations.tex`. -/
theorem tsallisRelativeEntropy_le_quantumRelativeEntropy {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : n → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0) {α : ℝ} (hα : α < 1) :
    tsallisRelativeEntropy α ρ σ ≤ quantumRelativeEntropy ρ σ := by
  rw [tsallisRelativeEntropy, div_le_iff₀ (sub_pos.mpr hα), mul_comm]
  exact re_trace_sub_le_mul_quantumRelativeEntropy hρ hσ hsupp α

/-- **Right half of Equation (8.38).** For positive-semidefinite `ρ, σ` with
`ker σ ⊆ ker ρ` and `β > 1`, `S(ρ|σ) ≤ S⁽ᵝ⁾(ρ|σ)`.

Wolf, Theorem "Relation among relative entropies", Equation (8.38),
`ch08_distance_measures.tex`, lines 500–506. **Scope restriction (finite
relative entropy, `β ≠ 1`):** see
`docs/paper-gaps/wolf_ch8_relative_entropy_relations.tex`. -/
theorem quantumRelativeEntropy_le_tsallisRelativeEntropy {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hsupp : ∀ v : n → ℂ, σ *ᵥ v = 0 → ρ *ᵥ v = 0) {β : ℝ} (hβ : 1 < β) :
    quantumRelativeEntropy ρ σ ≤ tsallisRelativeEntropy β ρ σ := by
  rw [tsallisRelativeEntropy, le_div_iff_of_neg (sub_neg.mpr hβ), mul_comm]
  exact re_trace_sub_le_mul_quantumRelativeEntropy hρ hσ hsupp β

end Matrix
