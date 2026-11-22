/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Entropy
import QICLean.Analysis.TraceCFC
import QICLean.Entropy.Renyi.Defs

/-!
# Entropies of a density operator with flat spectrum

A positive semidefinite matrix `ρ` of trace one satisfying `ρ² = r⁻¹ ρ` has eigenvalues
`0` and `r⁻¹`. Consequently its von Neumann entropy is `log r`, and so is its Rényi entropy
of every positive finite order; with `r` the rank of `ρ`, also the Rényi entropy of order zero.
For positive order different from one, the Rényi entropy is defined by the spectral trace of the
real power of the density; order one is the von Neumann entropy, and order zero is the
logarithm of the rank.

This elementary spectral calculation is the last step of Schuch, Cirac, and
Pérez-García, arXiv:1001.3807, Theorem 6.9 (`Papers/1001.3807/paper_v3.tex`,
lines 2027–2037 and 2062–2072), for the boundary density operator of a cut.

## Main results

* `vonNeumannEntropy_of_mul_self_eq_inv_smul`: the von Neumann entropy is `log r`.
* `renyiEntropy_of_mul_self_eq_inv_smul`: every positive finite Rényi order gives `log r`.
* `renyiEntropy_of_mul_self_eq_inv_smul_of_rank`: every nonnegative finite order gives the
  logarithm of the rank.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*

Moved from TNLean, `TNLean/Algebra/FlatDensityEntropy.lean` and
`TNLean/Algebra/FlatDensityRenyiEntropy.lean` at commit `49b78ed821` (Apache-2.0).
-/

open scoped BigOperators Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Hermitian quadratic flatness identity forces every eigenvalue to be zero
or the reciprocal flatness parameter. Source: SCP10, lines 2062–2072. -/
theorem Matrix.IsHermitian.eigenvalues_eq_zero_or_inv_of_mul_self_eq_inv_smul
    {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian)
    {r : ℝ} (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) (i : ι) :
    hρ.eigenvalues i = 0 ∨ hρ.eigenvalues i = r⁻¹ := by
  let v : ι → ℂ := hρ.eigenvectorBasis i
  have hv : v ≠ 0 :=
    (WithLp.ofLp_eq_zero 2).ne.2 (hρ.eigenvectorBasis.orthonormal.ne_zero i)
  have heig : ρ *ᵥ v = (hρ.eigenvalues i : ℂ) • v := by
    simpa only [v, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hρ.mulVec_eigenvectorBasis i
  have h := congrArg (fun A => A *ᵥ v) hflat
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, heig, Matrix.mulVec_smul, heig,
    smul_smul, smul_smul] at h
  have hscalar := (smul_left_injective ℂ hv) h
  have hreal : hρ.eigenvalues i * hρ.eigenvalues i = r⁻¹ * hρ.eigenvalues i := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv] using hscalar
  have hz : hρ.eigenvalues i * (hρ.eigenvalues i - r⁻¹) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hz with hz | hz
  · exact Or.inl hz
  · exact Or.inr (sub_eq_zero.mp hz)

/-- A trace-one positive semidefinite matrix satisfying `ρ² = r⁻¹ ρ` has entropy `log r`.
Source: arXiv:1001.3807, the flat-spectrum entropy calculation in the proof of Theorem 6.9,
lines 2062–2072. -/
theorem vonNeumannEntropy_of_mul_self_eq_inv_smul {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {r : ℝ}
    (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) : vonNeumannEntropy ρ hρ.isHermitian = Real.log r := by
  have hsum := posSemidef_trace_one_eigenvalues_sum_one hρ htr
  have hterm (i : ι) :
      Real.negMulLog (hρ.isHermitian.eigenvalues i) =
        hρ.isHermitian.eigenvalues i * Real.log r := by
    rcases hρ.isHermitian.eigenvalues_eq_zero_or_inv_of_mul_self_eq_inv_smul hflat i with hi | hi
    · simp only [hi, Real.negMulLog_zero, zero_mul]
    · rw [hi, Real.negMulLog, Real.log_inv]
      ring
  change (∑ i, Real.negMulLog (hρ.isHermitian.eigenvalues i)) = Real.log r
  simp_rw [hterm]
  rw [← Finset.sum_mul, hsum, one_mul]

open Matrix

/-- The trace of a positive spectral power of a flat density is `r^(1-α)`.
Source: SCP10, lines 2027–2037 and 2062–2072. -/
theorem trace_cfc_rpow_of_mul_self_eq_inv_smul {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {r α : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) :
    (hρ.isHermitian.cfc (fun x => x ^ α)).trace.re = r ^ (1 - α) := by
  have hsum := posSemidef_trace_one_eigenvalues_sum_one hρ htr
  have hterm i : hρ.isHermitian.eigenvalues i ^ α =
      hρ.isHermitian.eigenvalues i * r ^ (1 - α) := by
    rcases hρ.isHermitian.eigenvalues_eq_zero_or_inv_of_mul_self_eq_inv_smul hflat i with hi | hi
    · simp only [hi, Real.zero_rpow hα.ne', zero_mul]
    · rw [hi, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_neg_one,
        ← Real.rpow_add hr]
      congr 1
      ring
  change RCLike.re ((hρ.isHermitian.cfc (fun x => x ^ α)).trace) = _
  rw [hρ.isHermitian.trace_cfc_eq_sum_re]
  simp_rw [hterm]
  rw [← Finset.sum_mul, hsum, one_mul]

/-- Every positive finite Rényi order of a flat trace-one density equals `log r`.
Source: SCP10, lines 2027–2037 and 2062–2072. -/
theorem renyiEntropy_of_mul_self_eq_inv_smul {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {r α : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) :
    renyiEntropy ρ hρ.isHermitian α = Real.log r := by
  by_cases hα1 : α = 1
  · simp only [renyiEntropy, hα1, one_ne_zero, ↓reduceIte]
    exact vonNeumannEntropy_of_mul_self_eq_inv_smul hρ htr hflat
  · simp only [renyiEntropy, hα.ne', hα1, ↓reduceIte]
    rw [trace_cfc_rpow_of_mul_self_eq_inv_smul hρ htr hr hα hflat, Real.log_rpow hr]
    rw [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hα1)), one_mul]

/-- Including order zero, every nonnegative finite Rényi order of a flat density
is the logarithm of its rank. The rank identifies the zero-order convention.
Source: SCP10, lines 2027–2037 and 2062–2072. -/
theorem renyiEntropy_of_mul_self_eq_inv_smul_of_rank {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) {r α : ℝ} (hr : 0 < r) (hα : 0 ≤ α)
    (hflat : ρ * ρ = (r : ℂ)⁻¹ • ρ) (hrank : (ρ.rank : ℝ) = r) :
    renyiEntropy ρ hρ.isHermitian α = Real.log r := by
  rcases hα.eq_or_lt with hα0 | hαpos
  · simp only [← hα0, renyiEntropy, ↓reduceIte, hrank]
  · exact renyiEntropy_of_mul_self_eq_inv_smul hρ htr hr hαpos hflat
