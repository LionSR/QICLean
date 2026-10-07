/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.MarginalPhaseQuantities

/-!
# The marginal-phase comparison for a faithful state

Let `ρ` be a positive definite density matrix on `x (U F)` with `d = dim x` and
`η = I(x:F|U)_ρ`.  Then for every real `u`,
$$\bigl\lVert\bigl((\rho_U^{-iu}\rho_{xU}^{iu})\otimes I_F
   -\rho_{UF}^{-iu}\rho_{xUF}^{iu}\bigr)\sqrt\rho\bigr\rVert_2
 \le2\,|\sinh\pi u|\,\mathcal R_\eta,$$
with the Hilbert--Schmidt norm on the left.  This is the faithful case of Lemma 5.2 of
the two-dimensional area-law manuscript; for a purification `θ` of `ρ`, the left side
is `‖(ρ̂_U^{-iu} ρ̂_{xU}^{iu} - ρ̂_{UF}^{-iu} ρ̂_{xUF}^{iu}) θ‖`.

## Main results

* `Entropy.MarginalPhase.norm_phaseDifference_le_of_posDef`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Lemma 5.2
  (`lem:conditional-phases`), `04-conditional.tex`, lines 321–339; faithful case of the
  proof, lines 341–454.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

theorem spectralFun_kronecker_one_cpow {T : Type*} [Fintype T] [DecidableEq T]
    {M : Matrix T T ℂ} (hM : M.PosDef) {c : ℝ} (hc : 0 < c) (z : ℂ) :
    spectralFun (kroneckerUnitary (1 : unitary (Matrix X X ℂ)) hM.1.eigenvectorUnitary)
        (fun p => (((c * hM.1.eigenvalues p.2 : ℝ)) : ℂ) ^ z) =
      ((c : ℂ) ^ z) • ((1 : Matrix X X ℂ) ⊗ₖ cpowSpec hM z) := by
  have h := spectralFun_kronecker (1 : unitary (Matrix X X ℂ)) hM.1.eigenvectorUnitary
    (fun _ => (c : ℂ) ^ z) (fun k => ((hM.1.eigenvalues k : ℝ) : ℂ) ^ z)
  rw [spectralFun_one_unitary] at h
  rw [cpowSpec, ← smul_kronecker, h]
  congr 1
  funext p
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le (hM.eigenvalues_pos p.2).le]

theorem norm_ofReal_cpow_imag {c : ℝ} (hc : 0 < c) (u : ℝ) :
    ‖(c : ℂ) ^ (-(u * Complex.I))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hc]
  simp

/-- **Marginal-phase comparison, faithful case.**  For a positive definite density
matrix `ρ` on `x (U F)` and every real `u`,
`‖((ρ_U^{-iu} ρ_{xU}^{iu}) ⊗ I_F - ρ_{UF}^{-iu} ρ^{iu}) √ρ‖₂ ≤ 2 |sinh π u| 𝓡_η` with
`η = I(x:F|U)_ρ` and `d = dim x` in `𝓡_η`.  Area-law manuscript, Lemma 5.2,
`04-conditional.tex`, lines 321–339 and 341–454. -/
theorem norm_phaseDifference_le_of_posDef [Nonempty X] [Nonempty F]
    {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ} (hρ : ρ.PosDef) (htr : ρ.trace = 1) (u : ℝ) :
    ‖(WithLp.toLp 2 (vec
        ((embedF (((1 : Matrix X X ℂ) ⊗ₖ cpowSpec (posDef_marginalU (F := F) hρ) (-(u * Complex.I))) *
            cpowSpec (posDef_marginalXU (F := F) hρ) (u * Complex.I)) -
          ((1 : Matrix X X ℂ) ⊗ₖ cpowSpec (posDef_marginalUF hρ) (-(u * Complex.I))) *
            cpowSpec hρ (u * Complex.I)) * rpowSpec hρ (1 / 2))) :
        EuclideanSpace ℂ ((X × (U × F)) × (X × (U × F))))‖ ≤
      2 * |Real.sinh (Real.pi * u)| *
        Matrix.phaseRate (Fintype.card X) (condMutualInfo ρ hρ.posSemidef) := by
  set R := compression hρ
  have hd : (0 : ℝ) < (Fintype.card X : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hD : (1 : ℝ) ≤ Fintype.card X := Nat.one_le_cast.2 Fintype.card_pos
  have hK : R.invQuadA ≤ (Fintype.card X : ℝ) ^ 2 := by
    have := compression_invQuadA_le hρ
    rwa [htr, Complex.one_re, mul_one] at this
  have hM : R.quadB ≤ 1 := by rw [compression_quadB, htr, Complex.one_re]
  have hbound := R.norm_phaseGap_le_phaseRate hD hK hM u
  rw [compression_logGap] at hbound
  refine le_trans (le_of_eq ?_) hbound
  rw [compression_phaseGap, neg_neg]
  set c : ℂ := (((Fintype.card X : ℝ)⁻¹ : ℝ) : ℂ) ^ (-(u * Complex.I))
  have hSF : spectralFun (sigmaFUnitary (posDef_marginalUF hρ))
      (fun p => ((sigmaFEig (posDef_marginalUF hρ) p : ℝ) : ℂ) ^ (-(u * Complex.I))) =
      c • ((1 : Matrix X X ℂ) ⊗ₖ cpowSpec (posDef_marginalUF hρ) (-(u * Complex.I))) :=
    spectralFun_kronecker_one_cpow (posDef_marginalUF hρ) hd _
  have hSS : spectralFun (sigmaSUnitary (posDef_marginalU (F := F) hρ))
      (fun p => ((sigmaSEig (posDef_marginalU (F := F) hρ) p : ℝ) : ℂ) ^ (-(u * Complex.I))) =
      c • ((1 : Matrix X X ℂ) ⊗ₖ cpowSpec (posDef_marginalU (F := F) hρ) (-(u * Complex.I))) :=
    spectralFun_kronecker_one_cpow (posDef_marginalU (F := F) hρ) hd _
  rw [hSF, hSS, Matrix.smul_mul, Matrix.smul_mul, embedF_smul, ← smul_sub, Matrix.smul_mul,
    vec_smul, WithLp.toLp_smul, norm_smul, norm_ofReal_cpow_imag hd, one_mul, ← neg_sub,
    Matrix.neg_mul, vec_neg, WithLp.toLp_neg, norm_neg]

end Entropy.MarginalPhase

end
