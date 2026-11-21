/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FunctionalCalculus.TraceCFC
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# Measurements and convex functions

Measuring a density matrix with a symmetric POVM produces a probability distribution at least
as mixed as the state: for a POVM `{P_i}_{i=1}^m` on `M_d(ℂ)` with `m ≥ d` and `tr P_i = d/m`,
and every convex `f` with `f(0) ≤ 0`,

`tr f(ρ) ≥ ∑ᵢ f(pᵢ)`,  `pᵢ = tr(Pᵢ ρ)`.

For `m = d` the condition `f(0) ≤ 0` is not needed.

In the eigenbasis `(vₖ)` of `ρ`, `pᵢ = ∑ₖ aᵢₖ λₖ` with `aᵢₖ = ⟨vₖ, Pᵢ vₖ⟩ ≥ 0`,
`∑ᵢ aᵢₖ = 1` and `∑ₖ aᵢₖ = d/m ≤ 1`. Jensen's inequality with the remaining weight on `0`
gives `∑ᵢ f(pᵢ) ≤ ∑ₖ f(λₖ) + (m - d) f(0)`. Wolf proves the theorem through an embedding into
`M_m(ℂ)` and his Theorem 8.8; this direct argument uses the same doubly substochastic structure.

## Main results

* `Matrix.sum_convex_measurement_le`: Wolf, Theorem 8.9.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8, Theorem "Measurements and
  convex functions", Equation (8.23); local source
  `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 365--394.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace Matrix

/-- **Wolf, Theorem 8.9 (measurements and convex functions).** Let `{Pᵢ}_{i < m}` be a POVM on
`M_d(ℂ)` with `m ≥ d` and `tr Pᵢ = d/m`, let `ρ` be positive semidefinite, and let `f` be convex
with `f(0) ≤ 0`, or `m = d`. Then `∑ᵢ f(tr(Pᵢ ρ)) ≤ tr f(ρ)`. Wolf, Chapter 8, Equation (8.23);
local source `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 365--394. -/
theorem sum_convex_measurement_le {d m : ℕ} (P : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ i, (P i).PosSemidef) (hsum : ∑ i, P i = 1)
    (htr : ∀ i, (P i).trace = ((d : ℂ) / m)) (hdm : d ≤ m)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (hf0 : f 0 ≤ 0 ∨ m = d) :
    ∑ i, f ((P i * ρ).trace.re) ≤ (cfc f ρ).trace.re := by
  classical
  have hH := hρ.isHermitian
  let U : Matrix (Fin d) (Fin d) ℂ := hH.eigenvectorUnitary
  let lam := hH.eigenvalues
  have hUU : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hH.eigenvectorUnitary.2
    simpa [U, Matrix.star_eq_conjTranspose] using this
  have hρU : ρ = U * diagonal (fun k ↦ (lam k : ℂ)) * Uᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [U, lam, Function.comp_def, Matrix.star_eq_conjTranspose] using this
  let a : Fin m → Fin d → ℝ := fun i k ↦ ((Uᴴ * P i * U) k k).re
  have ha0 : ∀ i k, 0 ≤ a i k := fun i k ↦ by
    have hpsd := (hP i).conjTranspose_mul_mul_same U
    exact (Complex.nonneg_iff.mp hpsd.diag_nonneg).1
  have hp : ∀ i, (P i * ρ).trace.re = ∑ k, a i k * lam k := by
    intro i
    have h1 : (P i * ρ).trace = (Uᴴ * P i * U * diagonal (fun k ↦ (lam k : ℂ))).trace := by
      rw [hρU, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.mul_assoc]
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace]
    simp only [diag_apply, mul_diagonal, Complex.re_sum, a]
    exact Finset.sum_congr rfl fun k _ ↦ by simp [Complex.mul_re]
  have hcol : ∀ k, ∑ i, a i k = 1 := by
    intro k
    have h : ∑ i, Uᴴ * P i * U = 1 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, Matrix.mul_one, hUU]
    have := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ ↦ (M k k).re) h
    simpa [a, Matrix.sum_apply] using this
  have hrow : ∀ i, ∑ k, a i k = (d : ℝ) / m := by
    intro i
    have h : (Uᴴ * P i * U).trace = (P i).trace := by
      have hUU' : U * Uᴴ = 1 := by
        have := (Matrix.mem_unitaryGroup_iff).mp hH.eigenvectorUnitary.2
        simpa [U, Matrix.star_eq_conjTranspose] using this
      rw [Matrix.trace_mul_cycle, hUU', Matrix.one_mul]
    have hre : ((d : ℂ) / m).re = (d : ℝ) / m := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
        Complex.ofReal_re]
    have := congrArg Complex.re (h.trans (htr i))
    rw [hre] at this
    simpa [a, Matrix.trace] using this
  have hw1 : (0 : ℝ) ≤ 1 - (d : ℝ) / m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · rw [sub_nonneg, div_le_one (by exact_mod_cast hm)]
      exact_mod_cast hdm
  -- Jensen's inequality in each row, with the remaining weight on `0`.
  have hJ : ∀ i, f ((P i * ρ).trace.re) ≤ ∑ k, a i k * f (lam k) + (1 - (d : ℝ) / m) * f 0 := by
    intro i
    have hw : ∀ j ∈ (Finset.univ : Finset (Option (Fin d))),
        0 ≤ Option.elim j (1 - (d : ℝ) / m) (fun k ↦ a i k) := by
      intro j _; cases j with
      | none => exact hw1
      | some k => exact ha0 i k
    have hsum1 : ∑ j : Option (Fin d), Option.elim j (1 - (d : ℝ) / m) (fun k ↦ a i k) = 1 := by
      simp [Fintype.sum_option, hrow i]
    have hJ := hf.map_sum_le (t := Finset.univ)
      (w := fun j : Option (Fin d) ↦ Option.elim j (1 - (d : ℝ) / m) (fun k ↦ a i k))
      (p := fun j : Option (Fin d) ↦ Option.elim j 0 lam) hw hsum1 (fun _ _ ↦ Set.mem_univ _)
    rw [hp i]
    simpa [Fintype.sum_option, smul_eq_mul, add_comm] using hJ
  have htrf : (cfc f ρ).trace.re = ∑ k, f (lam k) := by
    rw [hH.cfc_eq]
    simpa using hH.trace_cfc_eq_sum_re f
  rw [htrf]
  calc ∑ i, f ((P i * ρ).trace.re)
      ≤ ∑ i, (∑ k, a i k * f (lam k) + (1 - (d : ℝ) / m) * f 0) :=
        Finset.sum_le_sum fun i _ ↦ hJ i
    _ = ∑ k, f (lam k) + (m - d) * f 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        simp only [← Finset.sum_mul, hcol, one_mul, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        congr 1
        rcases Nat.eq_zero_or_pos m with hm | hm
        · have : d = 0 := by omega
          simp [hm, this]
        · field_simp
    _ ≤ ∑ k, f (lam k) := by
        have hmd : (0 : ℝ) ≤ (m : ℝ) - d := by
          have : (d : ℝ) ≤ m := by exact_mod_cast hdm
          linarith
        rcases hf0 with h | h
        · nlinarith
        · simp [h]

end Matrix
