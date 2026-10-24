/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Entropy

/-!
# Mass of the leading weights of a distribution with bounded entropy

Let `p` be a finite probability distribution with entropy `S`, and let `T` be a set of `k`
weights with no weight outside `T` exceeding a weight inside it. If `exp (2 S) / 2 ≤ k`, then
the weights in `T` carry mass at least `1 / 2`.

Applied to the Schmidt coefficients of a pure state across a cut, this says that the
`exp (2 S) / 2` largest squared Schmidt coefficients carry at least half of the norm, where `S`
is the entanglement entropy of the cut.

Source: Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4,
section "Matrix Product States", lines 526–535, eq. `k0Ent`. At line 528 the source prints
`|A₀(k'+1)|² < 1/2k`, where it means `1 / (2 k')`; the proof below uses the latter.

## Main statements

* `Entropy.one_half_le_sum_of_exp_two_mul_probabilityEntropy_le`: the classical statement.
* `Matrix.one_half_le_sum_eigenvalues_of_exp_two_mul_vonNeumannEntropy_le`: the same statement
  for the eigenvalues of a density matrix.
-/

open Real
open scoped ComplexOrder

namespace Entropy

variable {Z : Type*} [Fintype Z]

/-- **Leading weights of a distribution with bounded entropy.** If the `k` weights in `T`
dominate every weight outside `T` and `exp (2 S) / 2 ≤ k`, where `S` is the entropy of `p`,
then the weights in `T` carry mass at least `1 / 2`.
Hastings, arXiv:0705.2024v4, lines 526–535, eq. `k0Ent`. -/
theorem one_half_le_sum_of_exp_two_mul_probabilityEntropy_le
    (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) (T : Finset Z)
    (hT : ∀ a ∈ T, ∀ b ∉ T, p b ≤ p a)
    (hk : exp (2 * probabilityEntropy p) / 2 ≤ T.card) :
    1 / 2 ≤ ∑ z ∈ T, p z := by
  classical
  by_contra hhead
  replace hhead := lt_of_not_ge hhead
  have hp1 : ∀ z, p z ≤ 1 := fun z => hsum ▸
    Finset.single_le_sum (fun y _ => hp y) (Finset.mem_univ z)
  have hS : 0 ≤ probabilityEntropy p :=
    Finset.sum_nonneg fun z _ => negMulLog_nonneg (hp z) (hp1 z)
  set k : ℝ := (T.card : ℝ) with hkdef
  have hk1 : 1 ≤ k := by
    have h1 : (1 : ℝ) ≤ exp (2 * probabilityEntropy p) := one_le_exp (by positivity)
    have hpos : (0 : ℝ) < T.card := by linarith
    have hpos' : 1 ≤ T.card := by exact_mod_cast hpos
    rw [hkdef]
    exact_mod_cast hpos'
  -- Every weight outside `T` is below `1 / (2 k)`.
  have hsmall : ∀ b ∉ T, p b ≤ 1 / (2 * k) := by
    intro b hb
    have hle : k * p b ≤ ∑ z ∈ T, p z := by
      rw [hkdef, ← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun a ha => hT a ha b hb
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- Each such weight contributes at least `p b * log (2 k)` to the entropy.
  have hterm : ∀ b ∉ T, p b * log (2 * k) ≤ negMulLog (p b) := by
    intro b hb
    rcases (hp b).eq_or_lt with h0 | hpos
    · rw [← h0, negMulLog_zero, zero_mul]
    · rw [negMulLog, neg_mul, ← mul_neg, ← log_inv]
      gcongr
      rw [le_inv_comm₀ (by positivity) hpos]
      simpa [one_div] using hsmall b hb
  have htail : 1 / 2 < ∑ z ∈ Tᶜ, p z := by
    have := Finset.sum_add_sum_compl T p
    rw [hsum] at this
    linarith
  have hlog : 0 < log (2 * k) := log_pos (by linarith)
  have hlower : (1 / 2) * log (2 * k) < probabilityEntropy p := by
    calc (1 / 2) * log (2 * k) < (∑ z ∈ Tᶜ, p z) * log (2 * k) := by gcongr
      _ = ∑ z ∈ Tᶜ, p z * log (2 * k) := Finset.sum_mul _ _ _
      _ ≤ ∑ z ∈ Tᶜ, negMulLog (p z) :=
          Finset.sum_le_sum fun b hb => hterm b (Finset.mem_compl.mp hb)
      _ ≤ probabilityEntropy p :=
          Finset.sum_le_univ_sum_of_nonneg fun z => negMulLog_nonneg (hp z) (hp1 z)
  have hexp : 2 * k < exp (2 * probabilityEntropy p) := by
    rw [← exp_log (by positivity : (0 : ℝ) < 2 * k)]
    exact exp_lt_exp.mpr (by linarith)
  linarith

end Entropy

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Leading eigenvalues of a density matrix with bounded entropy.** If the `k` eigenvalues
indexed by `T` dominate every other eigenvalue of the density matrix `ρ` and
`exp (2 S(ρ)) / 2 ≤ k`, then the eigenvalues in `T` sum to at least `1 / 2`.
Hastings, arXiv:0705.2024v4, lines 526–535, eq. `k0Ent`. -/
theorem one_half_le_sum_eigenvalues_of_exp_two_mul_vonNeumannEntropy_le
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (T : Finset n)
    (hT : ∀ a ∈ T, ∀ b ∉ T, hρ.isHermitian.eigenvalues b ≤ hρ.isHermitian.eigenvalues a)
    (hk : Real.exp (2 * vonNeumannEntropy ρ hρ.isHermitian) / 2 ≤ T.card) :
    1 / 2 ≤ ∑ z ∈ T, hρ.isHermitian.eigenvalues z := by
  refine Entropy.one_half_le_sum_of_exp_two_mul_probabilityEntropy_le _ hρ.eigenvalues_nonneg
    ?_ T hT hk
  have h := hρ.isHermitian.trace_eq_sum_eigenvalues
  rw [htr] at h
  simpa using (congrArg Complex.re h).symm

end Matrix
