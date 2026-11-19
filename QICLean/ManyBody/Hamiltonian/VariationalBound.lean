/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.VariationalBound
import QICLean.ManyBody.Hamiltonian.GaussianFilter

/-!
# A variational lower bound from Gaussian-filtered terms

Let `H = ∑ᵢ Uᵢ H₀ Uᵢ†`, where the `Uᵢ` are unitaries commuting with `H`.
The Gaussian-filtered term `K = gaussianFilteredTerm q ΔE H H₀` satisfies
`H = ∑ᵢ Uᵢ K Uᵢ†`. Consequently `E₀ ≥ N λ_min(K)`, with `N` the number of terms.
For translations of a periodic lattice this is Hastings' filtered instance of the
variational lower bound, arXiv:cond-mat/0508554v3, eq. `varnum` (lines 856–877)
and the discussion of filtered terms at lines 1005–1009.

The proof uses the actual Gaussian integral, its covariance and preservation of the
Hamiltonian sum. It does not require a gap or an approximation by finite polynomials.
QICLean identifies that integral with the norm-convergent even-commutator series;
the correction to the printed coefficients is documented at
https://sirui-lu.com/QICLean/paper-gaps/hastings05_gaussian_series_coefficients.pdf.
-/

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator

namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugating `H` and `W` by the same unitary conjugates the Gaussian-filtered operator.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1603–1618. -/
theorem gaussianFilteredTerm_conj {n : Type*} [Fintype n] [DecidableEq n] (r ΔE : ℝ)
    {U H : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (hH : H.IsHermitian) (W : Matrix n n ℂ) :
    gaussianFilteredTerm r ΔE (U * H * Uᴴ) (U * W * Uᴴ) =
      U * gaussianFilteredTerm r ΔE H W * Uᴴ := by
  have hUU : U * Uᴴ = 1 := by simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff).mp hU
  have hUU' : Uᴴ * U = 1 := by simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff').mp hU
  have hpath (t : ℝ) : hermitianUnitaryPath (U * H * Uᴴ) t = U * hermitianUnitaryPath H t * Uᴴ := by
    have hinv : Uᴴ = U⁻¹ := (inv_eq_right_inv hUU).symm
    rw [hinv, hermitianUnitaryPath, hermitianUnitaryPath,
      ← exp_conj U _ ((isUnit_iff_isUnit_det U).mpr (isUnit_det_of_right_inverse hUU))]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hint (t : ℝ) : hermitianUnitaryPath (U * H * Uᴴ) t * (U * W * Uᴴ) *
      hermitianUnitaryPath (U * H * Uᴴ) (-t) =
        U * (hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t)) * Uᴴ := by
    rw [hpath, hpath]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hUU', Matrix.one_mul]
  simp only [gaussianFilteredTerm, gaussianIntertwiner, hint]
  exact (ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) U Uᴴ).integral_comp_comm
    (integrable_intertwinerIntegrand _ hH hH W)

/-- The conjugates of an actual Gaussian-filtered term sum to the original Hamiltonian.
Hastings, arXiv:cond-mat/0508554v3, eq. `hsum` (lines 247–249) and lines 1005–1009. -/
theorem sum_conj_gaussianFilteredTerm {ι : Type*} [Fintype ι] (q ΔE : ℝ)
    (U : ι → Matrix n n ℂ) (hU : ∀ i, U i ∈ unitaryGroup n ℂ)
    (H₀ : Matrix n n ℂ) (hH₀ : H₀.IsHermitian)
    (hcomm : ∀ i, Commute (U i) (∑ j, U j * H₀ * (U j)ᴴ)) :
    ∑ i, U i * gaussianFilteredTerm q ΔE (∑ j, U j * H₀ * (U j)ᴴ) H₀ * (U i)ᴴ =
      ∑ j, U j * H₀ * (U j)ᴴ := by
  let H := ∑ j, U j * H₀ * (U j)ᴴ
  have hH : H.IsHermitian :=
    isSelfAdjoint_sum _ fun j _ ↦ isHermitian_mul_mul_conjTranspose (U j) hH₀
  have hconj (i : ι) : U i * H * (U i)ᴴ = H := by
    rw [(hcomm i).eq, Matrix.mul_assoc]
    have hUU : U i * (U i)ᴴ = 1 := by
      simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff).mp (hU i)
    rw [hUU, Matrix.mul_one]
  calc
    _ = ∑ i, gaussianFilteredTerm q ΔE H (U i * H₀ * (U i)ᴴ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← gaussianFilteredTerm_conj q ΔE (hU i) hH H₀, hconj]
    _ = H := sum_gaussianFilteredTerm Finset.univ q ΔE hH rfl

/-- The lowest eigenvalue of an actual Gaussian-filtered term gives a lower bound
on every eigenvalue of the Hamiltonian. Hastings, arXiv:cond-mat/0508554v3,
eq. `varnum` (lines 856–877), with the filtered choice at lines 1005–1009. -/
theorem card_mul_sInf_spectrum_gaussianFilteredTerm_le_of_conj {ι : Type*} [Fintype ι]
    (q ΔE : ℝ) (U : ι → Matrix n n ℂ) (hU : ∀ i, U i ∈ unitaryGroup n ℂ)
    (H₀ : Matrix n n ℂ) (hH₀ : H₀.IsHermitian)
    (hcomm : ∀ i, Commute (U i) (∑ j, U j * H₀ * (U j)ᴴ))
    {E : ℝ} {Ω : n → ℂ} (hΩ : Ω ≠ 0)
    (hE : (∑ j, U j * H₀ * (U j)ᴴ) *ᵥ Ω = (E : ℂ) • Ω) :
    Fintype.card ι * sInf (spectrum ℝ
      (gaussianFilteredTerm q ΔE (∑ j, U j * H₀ * (U j)ᴴ) H₀)) ≤ E := by
  let H := ∑ j, U j * H₀ * (U j)ᴴ
  let K := gaussianFilteredTerm q ΔE H H₀
  have hH : H.IsHermitian :=
    isSelfAdjoint_sum _ fun j _ ↦ isHermitian_mul_mul_conjTranspose (U j) hH₀
  have hsum : ∑ j, U j * K * (U j)ᴴ = H :=
    sum_conj_gaussianFilteredTerm q ΔE U hU H₀ hH₀ hcomm
  have hcommK : ∀ i, Commute (U i) (∑ j, U j * K * (U j)ᴴ) := by
    intro i
    rw [hsum]
    exact hcomm i
  have hEK : (∑ j, U j * K * (U j)ᴴ) *ᵥ Ω = (E : ℂ) • Ω := by
    rw [hsum]
    exact hE
  simpa using Matrix.card_mul_sInf_spectrum_le_of_conj U hU K
    (isHermitian_gaussianFilteredTerm q ΔE hH hH₀) hcommK (fun _ ↦ 0) 0 hΩ hEK


end ManyBody
