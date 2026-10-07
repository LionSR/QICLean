/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.MarginalPhaseFaithful
import QICLean.Algebra.PartialTraceDomination
import QICLean.Analysis.SuperoperatorResolvent
import QICLean.Analysis.Entropy

/-!
# The three scalar inputs of the marginal-phase comparison

For the resolvent compression of a faithful state `ρ` on `x (U F)` with `tr ρ = 1`:

* `⟨a₀, A⁻¹ a₀⟩ = tr (σ_f⁻¹ ρ²) ≤ d²`, from the domination `ρ ≤ d² σ_f`;
* `⟨b₀, B b₀⟩ = tr σ_s = 1`;
* `⟨b₀, log B b₀⟩ - ⟨a₀, log A a₀⟩ = S(xU) + S(UF) - S(U) - S(xUF) = I(x:F|U)`.

## Main results

* `Entropy.MarginalPhase.compression_invQuadA_le`.
* `Entropy.MarginalPhase.compression_quadB`.
* `Entropy.MarginalPhase.compression_logGap`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 380–400.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

/-- The conditional mutual information `I(x:F|U) = S(xU) + S(UF) - S(U) - S(xUF)` of a
positive semidefinite matrix on `x (U F)`.  Area-law manuscript, `04-conditional.tex`,
line 324. -/
def condMutualInfo (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) (hρ : ρ.PosSemidef) : ℝ :=
  vonNeumannEntropy (marginalXU ρ) ((hρ.submatrix assocE).partialTraceRight.isHermitian) +
    vonNeumannEntropy (marginalUF ρ) hρ.partialTraceLeft.isHermitian -
    vonNeumannEntropy (marginalU ρ)
      ((hρ.submatrix assocE).partialTraceRight.partialTraceLeft.isHermitian) -
    vonNeumannEntropy ρ hρ.isHermitian

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem trace_marginalXU (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    (marginalXU ρ).trace = ρ.trace := by
  rw [marginalXU, trace_partialTraceRight, trace_submatrix_equiv]

theorem trace_marginalU (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    (marginalU ρ).trace = ρ.trace := by
  rw [marginalU, trace_partialTraceLeft, trace_marginalXU]

theorem trace_sigmaS [Nonempty X] (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    (sigmaS ρ).trace = ρ.trace := by
  rw [sigmaS, trace_kronecker, trace_smul, trace_one, trace_marginalU, smul_eq_mul]
  have : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

section Faithful

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ} [Nonempty X] [Nonempty F] (hρ : ρ.PosDef)

theorem rpowSpec_mul_mul_rpowSpec_half {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (M : Matrix n n ℂ) :
    (rpowSpec hA (1 / 2) * M * rpowSpec hA (1 / 2)).trace = (M * rpowSpec hA 1).trace := by
  rw [trace_mul_cycle, rpowSpec_mul, trace_mul_comm]
  norm_num

/-- `⟨b₀, B b₀⟩ = tr σ_s = tr ρ`.  Area-law manuscript, `04-conditional.tex`, line 399. -/
theorem compression_quadB : (compression hρ).quadB = ρ.trace.re := by
  set hs := posDef_marginalXU (F := F) hρ
  rw [ResolventCompression.quadB]
  simp only [ResolventCompression.weightB]
  rw [← re_dotProduct_spectralFun_ofReal]
  change (star (vec (rpowSpec hs (1 / 2))) ⬝ᵥ
    (spectralFun (unitaryB hρ) (fun p => (eigB hρ p : ℂ)) *ᵥ vec (rpowSpec hs (1 / 2)))).re = _
  rw [spectralFun_eigB, kronecker_mulVec_vec, transpose_transpose, star_vec_dotProduct_vec,
    rpowSpec_isHermitian, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, rpowSpec_mul,
    rpowSpec_mul]
  norm_num [rpowSpec_zero, trace_sigmaS]

omit [Nonempty X] [Nonempty F] in
theorem re_trace_mul_mul_mono {n : Type*} [Fintype n] [DecidableEq n] {R A B : Matrix n n ℂ}
    (hR : R.IsHermitian) (hAB : A ≤ B) : (R * A * R).trace.re ≤ (R * B * R).trace.re := by
  have h := (le_iff.1 hAB).conjTranspose_mul_mul_same R
  rw [hR.eq, Matrix.mul_sub, Matrix.sub_mul] at h
  have := h.trace_nonneg
  rw [trace_sub] at this
  rw [Complex.nonneg_iff] at this
  simp only [Complex.sub_re, Complex.zero_re] at this
  linarith [this.1]

omit [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F] [Nonempty F] in
theorem sigmaF_eq_smul : (Fintype.card X : ℂ) • ((1 : Matrix X X ℂ) ⊗ₖ marginalUF ρ) =
    ((Fintype.card X : ℝ) ^ 2) • sigmaF ρ := by
  have hd : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [sigmaF, smul_kronecker, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  field_simp

omit [DecidableEq U] [DecidableEq F] [Nonempty F] in
theorem posDef_sigmaF (hρ : ρ.PosDef) : (sigmaF ρ).PosDef := by
  have hd : (0 : ℝ) < (Fintype.card X : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have h1 : ((Fintype.card X : ℝ)⁻¹ • (1 : Matrix X X ℂ)).PosDef := PosDef.one.smul hd
  rw [sigmaF, show ((Fintype.card X : ℂ)⁻¹ • (1 : Matrix X X ℂ)) =
    (Fintype.card X : ℝ)⁻¹ • (1 : Matrix X X ℂ) by rw [← Complex.coe_smul]; push_cast; rfl]
  exact h1.kronecker (posDef_marginalUF hρ)

/-- `⟨a₀, A⁻¹ a₀⟩ = tr (ρ σ_f⁻¹ ρ) ≤ d² tr ρ`, from `ρ ≤ d² σ_f`.  Area-law manuscript,
`04-conditional.tex`, lines 392–398. -/
theorem compression_invQuadA_le :
    (compression hρ).invQuadA ≤ (Fintype.card X : ℝ) ^ 2 * ρ.trace.re := by
  set hUF := posDef_marginalUF (F := F) (U := U) hρ
  set Sinv := spectralFun (sigmaFUnitary hUF) (fun p => ((sigmaFEig hUF p)⁻¹ : ℝ))
  have hsf : ∀ p, 0 < sigmaFEig hUF p := fun p => by
    have := hUF.eigenvalues_pos p.2
    unfold sigmaFEig
    have : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
    positivity
  -- the inverse quadratic form as a trace
  have hA : spectralFun (compression hρ).UA (fun k => (((compression hρ).lam k)⁻¹ : ℝ)) =
      (rpowSpec hρ 1)ᵀ ⊗ₖ Sinv := by
    refine spectralFun_leftRight_mul _ _ hρ.1.eigenvalues (sigmaFEig hUF)
      (fun t => ((t⁻¹ : ℝ) : ℂ)) (fun a => ((a ^ (1 : ℝ) : ℝ) : ℂ)) (fun b => ((b⁻¹ : ℝ) : ℂ))
      fun k j => ?_
    have hk := hρ.eigenvalues_pos k
    rw [Real.rpow_one, Real.rpow_neg_one, mul_inv, inv_inv, Complex.ofReal_mul]
  have hform : (compression hρ).invQuadA = (Sinv * rpowSpec hρ 2).trace.re := by
    rw [ResolventCompression.invQuadA]
    simp only [ResolventCompression.weightA]
    rw [← re_dotProduct_spectralFun_ofReal, hA, compression_a0, kronecker_mulVec_vec,
      transpose_transpose, star_vec_dotProduct_vec, rpowSpec_isHermitian, trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc, rpowSpec_mul, rpowSpec_mul]
    norm_num
  -- `Sinv` is the inverse of `σ_f`
  have hSinv : (sigmaF ρ)⁻¹ = Sinv := by
    refine inv_eq_left_inv ?_
    rw [← spectralFun_sigmaF hUF, spectralFun_mul, ← spectralFun_one (sigmaFUnitary hUF)]
    congr 1
    funext p
    simp only [Pi.mul_apply]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hsf p).ne', Complex.ofReal_one]
  -- domination and inversion
  set c : ℝ := (Fintype.card X : ℝ) ^ 2
  have hc : 0 < c := by
    have : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
    positivity
  have hσ := posDef_sigmaF hρ
  have hB : (c • sigmaF ρ).PosDef := hσ.smul hc
  have hle : ρ ≤ c • sigmaF ρ := by
    rw [← sigmaF_eq_smul]
    exact hρ.posSemidef.le_card_smul_one_kronecker_partialTraceLeft
  have hinv := PosDef.inv_le_inv_of_le hρ hB hle
  have hBinv : (c • sigmaF ρ)⁻¹ = c⁻¹ • (sigmaF ρ)⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc.ne', one_smul,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hσ.isUnit)]
  have hmono := re_trace_mul_mul_mono hρ.1 hinv
  rw [hBinv, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hρ.isUnit), Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul, trace_smul, Complex.real_smul, Complex.mul_re] at hmono
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hmono
  rw [hform, ← hSinv, show rpowSpec hρ 2 = ρ * ρ by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, ← rpowSpec_mul, rpowSpec_one],
    ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
  have hc' : c⁻¹ * (ρ * (sigmaF ρ)⁻¹ * ρ).trace.re ≤ ρ.trace.re := hmono
  rw [inv_mul_le_iff₀ hc] at hc'
  exact hc'

end Faithful

section LogForm

variable {T : Type*} [Fintype T] [DecidableEq T] [Nonempty X]

/-- The relative logarithmic form of `M` against `I_x / d ⊗ tr_x M`:
`⟨√M, log(L_σ R_{M^{-1}}) √M⟩ = S(M) - (log d) tr M - S(tr_x M)`.  Area-law
manuscript, `04-conditional.tex`, lines 386–390. -/
theorem re_logForm {M : Matrix (X × T) (X × T) ℂ} (hM : M.PosDef)
    (hT : (partialTraceLeft M).PosDef) :
    (star (vec (rpowSpec hM (1 / 2))) ⬝ᵥ
      (spectralFun (kroneckerUnitary (conjUnitary hM.1.eigenvectorUnitary)
          (kroneckerUnitary 1 hT.1.eigenvectorUnitary))
        (fun p => ((Real.log (hM.1.eigenvalues p.1 ^ (-1 : ℝ) *
          ((Fintype.card X : ℝ)⁻¹ * hT.1.eigenvalues p.2.2)) : ℝ) : ℂ)) *ᵥ
        vec (rpowSpec hM (1 / 2)))).re =
      vonNeumannEntropy M hM.1 - Real.log (Fintype.card X) * M.trace.re -
        vonNeumannEntropy (partialTraceLeft M) hT.1 := by
  set d : ℝ := (Fintype.card X : ℝ)
  have hd : 0 < d := Nat.cast_pos.2 Fintype.card_pos
  set W := hT.1.eigenvectorUnitary
  set μ := hT.1.eigenvalues
  set LT := spectralFun W (fun k => ((Real.log (μ k) : ℝ) : ℂ))
  have hsplit := spectralFun_leftRight_add hM.1.eigenvectorUnitary (kroneckerUnitary (1 : unitary (Matrix X X ℂ)) W)
    hM.1.eigenvalues (fun p => d⁻¹ * μ p.2) (fun t => ((Real.log t : ℝ) : ℂ))
    (fun a => ((-Real.log a : ℝ) : ℂ)) (fun b => ((Real.log b : ℝ) : ℂ)) (fun k j => by
      have hk := hM.eigenvalues_pos k
      have hj := hT.eigenvalues_pos j.2
      rw [Real.log_mul (Real.rpow_pos_of_pos hk _).ne' (mul_pos (inv_pos.2 hd) hj).ne',
        Real.log_rpow hk]
      push_cast; ring)
  have hLS : spectralFun (kroneckerUnitary (1 : unitary (Matrix X X ℂ)) W) (fun p => ((Real.log (d⁻¹ * μ p.2) : ℝ) : ℂ)) =
      ((-Real.log d : ℝ) : ℂ) • 1 + (1 : Matrix X X ℂ) ⊗ₖ LT := by
    rw [← spectralFun_const (kroneckerUnitary (1 : unitary (Matrix X X ℂ)) W), show (1 : Matrix X X ℂ) = spectralFun 1
      (fun _ => 1) from (spectralFun_one _).symm, spectralFun_kronecker, ← spectralFun_add]
    congr 1
    funext p
    have hj := hT.eigenvalues_pos p.2
    simp only [Pi.add_apply, one_mul]
    rw [Real.log_mul (inv_pos.2 hd).ne' hj.ne', Real.log_inv]
    push_cast; ring
  set NL := spectralFun hM.1.eigenvectorUnitary
    (fun k => ((-Real.log (hM.1.eigenvalues k) : ℝ) : ℂ))
  rw [hsplit, add_mulVec, kronecker_mulVec_vec, kronecker_mulVec_vec, transpose_transpose,
    transpose_one, Matrix.one_mul, Matrix.mul_one, dotProduct_add, star_vec_dotProduct_vec,
    star_vec_dotProduct_vec, rpowSpec_isHermitian, hLS, ← Matrix.mul_assoc, rpowSpec_mul,
    ← Matrix.mul_assoc, rpowSpec_mul_mul_rpowSpec_half]
  norm_num only
  rw [rpowSpec_one, Matrix.add_mul, trace_add, Matrix.smul_mul, Matrix.one_mul, trace_smul,
    trace_mul_comm ((1 : Matrix X X ℂ) ⊗ₖ LT), ← trace_partialTraceLeft_mul]
  -- evaluate the traces in eigencoordinates
  have h1 : (M * NL).trace = ((vonNeumannEntropy M hM.1 : ℝ) : ℂ) := by
    calc (M * NL).trace = (spectralFun hM.1.eigenvectorUnitary
          (fun k => ((hM.1.eigenvalues k : ℝ) : ℂ)) * NL).trace := by
          rw [hM.1.spectralFun_eigenvectorUnitary]
      _ = _ := by
          rw [spectralFun_mul, trace_spectralFun, vonNeumannEntropy, Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [Pi.mul_apply, Real.negMulLog]
          push_cast; ring
  have h2 : (partialTraceLeft M * LT).trace =
      ((-vonNeumannEntropy (partialTraceLeft M) hT.1 : ℝ) : ℂ) := by
    calc (partialTraceLeft M * LT).trace = (spectralFun W (fun k => ((μ k : ℝ) : ℂ)) * LT).trace := by
          rw [hT.1.spectralFun_eigenvectorUnitary]
      _ = _ := by
          rw [spectralFun_mul, trace_spectralFun, vonNeumannEntropy, ← Finset.sum_neg_distrib,
            Complex.ofReal_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [Pi.mul_apply, Real.negMulLog]
          push_cast; ring
  rw [h1, h2, smul_eq_mul, Complex.add_re, Complex.add_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

end LogForm

section FaithfulLog

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ} [Nonempty X] [Nonempty F] (hρ : ρ.PosDef)

/-- `⟨b₀, log B b₀⟩ - ⟨a₀, log A a₀⟩ = I(x:F|U)`.  Area-law manuscript,
`04-conditional.tex`, lines 383–390. -/
theorem compression_logGap :
    (compression hρ).logGap = condMutualInfo ρ hρ.posSemidef := by
  set hs := posDef_marginalXU (F := F) hρ
  have hA : ∑ k, Real.log ((compression hρ).lam k) * (compression hρ).weightA k =
      vonNeumannEntropy ρ hρ.1 - Real.log (Fintype.card X) * ρ.trace.re -
        vonNeumannEntropy (partialTraceLeft ρ) (posDef_marginalUF hρ).1 := by
    rw [← re_logForm hρ (posDef_marginalUF hρ), ← compression_a0 hρ]
    simp only [ResolventCompression.weightA]
    rw [← re_dotProduct_spectralFun_ofReal]
    rfl
  have hB : ∑ j, Real.log ((compression hρ).mu j) * (compression hρ).weightB j =
      vonNeumannEntropy (marginalXU ρ) hs.1 - Real.log (Fintype.card X) * ρ.trace.re -
        vonNeumannEntropy (marginalU ρ) (posDef_marginalU (F := F) hρ).1 := by
    have h := re_logForm hs (posDef_marginalU (F := F) hρ)
    rw [trace_marginalXU] at h
    simp only [ResolventCompression.weightB]
    rw [← re_dotProduct_spectralFun_ofReal]
    exact h
  rw [ResolventCompression.logGap, hA, hB]
  unfold condMutualInfo marginalUF
  ring

end FaithfulLog

end Entropy.MarginalPhase

end
