/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.MarginalPhaseComparison
import QICLean.Analysis.SpectralFunUnique

/-!
# Kernel-completed phases and support inclusions

For a Hermitian matrix `M` with eigenbasis `U` and eigenvalues `λ`, the kernel-completed
phase is `M̂^{iu} = ∑_{λ>0} λ^{iu} Π_λ + Π_{ker M}`, written here as
`spectralFun U (λ ↦ if λ = 0 then 1 else λ^{iu})`; the kernel and support projections
are `spectralFun U 1_{λ = 0}` and `spectralFun U 1_{λ ≠ 0}`.

For a positive semidefinite `ρ` on `x (U F)` this file proves the support inclusions
used in the singular case of the marginal-phase comparison:
`(I_x ⊗ Π_{ker ρ_{UF}}) √ρ = 0`, `(Π_{ker ρ_{xU}} ⊗ I_F) √ρ = 0`, and
`((I_x ⊗ Π_{ker ρ_U}) ρ̂_{xU}^{iu} ⊗ I_F) √ρ = 0`.

## Main definitions

* `Matrix.hatPhase`, `Matrix.kerProj`, `Matrix.suppProj`, `Matrix.sqrtSpec`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 456–478; the notation `ρ̂`, lines 14–25.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}

/-- The kernel-completed phase `M̂^{iu}`.  Area-law manuscript, `04-conditional.tex`,
lines 14–25. -/
def hatPhase (hM : M.IsHermitian) (u : ℝ) : Matrix n n ℂ :=
  spectralFun hM.eigenvectorUnitary
    (fun k => if hM.eigenvalues k = 0 then 1 else
      ((hM.eigenvalues k : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I))

/-- The kernel projection `Π_{ker M}` in the eigenbasis of `M`. -/
def kerProj (hM : M.IsHermitian) : Matrix n n ℂ :=
  spectralFun hM.eigenvectorUnitary (fun k => if hM.eigenvalues k = 0 then 1 else 0)

/-- The support projection `Π_{supp M}` in the eigenbasis of `M`. -/
def suppProj (hM : M.IsHermitian) : Matrix n n ℂ :=
  spectralFun hM.eigenvectorUnitary (fun k => if hM.eigenvalues k = 0 then 0 else 1)

/-- The square root `√M` in the eigenbasis of `M`. -/
def sqrtSpec (hM : M.IsHermitian) : Matrix n n ℂ :=
  spectralFun hM.eigenvectorUnitary (fun k => ((Real.sqrt (hM.eigenvalues k) : ℝ) : ℂ))

theorem sqrtSpec_eq_cfc (hM : M.IsHermitian) : sqrtSpec hM = cfc Real.sqrt M :=
  (hM.cfc_eq_spectralFun Real.sqrt).symm

theorem kerProj_isHermitian (hM : M.IsHermitian) : (kerProj hM)ᴴ = kerProj hM := by
  rw [kerProj, conjTranspose_spectralFun]
  congr 1; funext k; by_cases h : hM.eigenvalues k = 0 <;> simp [h]

theorem kerProj_mul_self (hM : M.IsHermitian) : kerProj hM * kerProj hM = kerProj hM := by
  rw [kerProj, spectralFun_mul]
  congr 1; funext k; by_cases h : hM.eigenvalues k = 0 <;> simp [h]

theorem kerProj_mul_eq_zero (hM : M.IsHermitian) : kerProj hM * M = 0 := by
  calc kerProj hM * M = kerProj hM *
      spectralFun hM.eigenvectorUnitary (fun k => ((hM.eigenvalues k : ℝ) : ℂ)) := by
        rw [hM.spectralFun_eigenvectorUnitary]
    _ = 0 := by
        rw [kerProj, spectralFun_mul, ← zero_smul ℂ (1 : Matrix n n ℂ),
          ← spectralFun_const hM.eigenvectorUnitary 0]
        congr 1
        funext k
        by_cases h : hM.eigenvalues k = 0 <;> simp [h]

theorem sqrtSpec_conjTranspose (hM : M.IsHermitian) : (sqrtSpec hM)ᴴ = sqrtSpec hM := by
  rw [sqrtSpec, conjTranspose_spectralFun]
  congr 1; funext k; simp

theorem sqrtSpec_mul_self (hM : M.PosSemidef) : sqrtSpec hM.1 * sqrtSpec hM.1 = M := by
  conv_rhs => rw [← hM.1.spectralFun_eigenvectorUnitary]
  rw [sqrtSpec, spectralFun_mul]
  congr 1; funext k
  simp only [Pi.mul_apply, ← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt (hM.eigenvalues_nonneg k)]

/-- A Hermitian projection with `tr (ρ K) = 0` annihilates `√ρ`. -/
theorem mul_sqrtSpec_eq_zero_of_trace (hM : M.PosSemidef) {K : Matrix n n ℂ}
    (hK : Kᴴ = K) (hKK : K * K = K) (htr : (M * K).trace = 0) : K * sqrtSpec hM.1 = 0 := by
  rw [← trace_mul_conjTranspose_self_eq_zero_iff, conjTranspose_mul, sqrtSpec_conjTranspose, hK,
    Matrix.mul_assoc, ← Matrix.mul_assoc (sqrtSpec hM.1), sqrtSpec_mul_self hM, trace_mul_comm,
    Matrix.mul_assoc, hKK, htr]

theorem hatPhase_eq (hM : M.IsHermitian) (u : ℝ) :
    hatPhase hM u = suppProj hM * hatPhase hM u + kerProj hM := by
  rw [hatPhase, suppProj, kerProj, spectralFun_mul, ← spectralFun_add]
  congr 1; funext k; by_cases h : hM.eigenvalues k = 0 <;> simp [h]

theorem suppProj_eq_sqrtSpec_mul (hM : M.PosSemidef) :
    suppProj hM.1 = sqrtSpec hM.1 *
      spectralFun hM.1.eigenvectorUnitary (fun k => if hM.1.eigenvalues k = 0 then 0 else
        (((Real.sqrt (hM.1.eigenvalues k))⁻¹ : ℝ) : ℂ)) := by
  rw [suppProj, sqrtSpec, spectralFun_mul]
  congr 1; funext k
  by_cases h : hM.1.eigenvalues k = 0
  · simp [h]
  · simp only [Pi.mul_apply, h, ite_false, ← Complex.ofReal_mul]
    rw [mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (hM.eigenvalues_nonneg k)
      (Ne.symm h))), Complex.ofReal_one]

end Matrix

namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

theorem one_kronecker_kerProj_mul_sqrtSpec {T : Type*} [Fintype T] [DecidableEq T]
    {ρ : Matrix (X × T) (X × T) ℂ} (hρ : ρ.PosSemidef) (hT : (partialTraceLeft ρ).IsHermitian) :
    ((1 : Matrix X X ℂ) ⊗ₖ kerProj hT) * sqrtSpec hρ.1 = 0 := by
  refine mul_sqrtSpec_eq_zero_of_trace hρ ?_ ?_ ?_
  · rw [conjTranspose_kronecker, conjTranspose_one, kerProj_isHermitian]
  · rw [← mul_kronecker_mul, Matrix.one_mul, kerProj_mul_self]
  · rw [← trace_partialTraceLeft_mul, trace_mul_comm, kerProj_mul_eq_zero, trace_zero]

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem posSemidef_marginalXU {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ} (hρ : ρ.PosSemidef) :
    (marginalXU ρ).PosSemidef :=
  (hρ.submatrix assocE).partialTraceRight

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem posSemidef_marginalU {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ} (hρ : ρ.PosSemidef) :
    (marginalU ρ).PosSemidef :=
  (posSemidef_marginalXU hρ).partialTraceLeft

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem posSemidef_marginalUF {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ} (hρ : ρ.PosSemidef) :
    (marginalUF ρ).PosSemidef :=
  hρ.partialTraceLeft

/-- `(Π_{ker ρ_{xU}} ⊗ I_F) √ρ = 0`.  Area-law manuscript, `04-conditional.tex`,
lines 463–464. -/
theorem embedF_kerProj_mul_sqrtSpec {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
    (hρ : ρ.PosSemidef) :
    embedF (kerProj (posSemidef_marginalXU hρ).1) * sqrtSpec hρ.1 = 0 := by
  refine mul_sqrtSpec_eq_zero_of_trace hρ ?_ ?_ ?_
  · rw [conjTranspose_embedF, kerProj_isHermitian]
  · rw [embedF_mul, kerProj_mul_self]
  · rw [trace_mul_embedF, trace_mul_comm]
    change (kerProj (posSemidef_marginalXU hρ).1 * marginalXU ρ).trace = 0
    rw [kerProj_mul_eq_zero, trace_zero]

/-- `((I_x ⊗ Π_{ker ρ_U}) ρ̂_{xU}^{iu} ⊗ I_F) √ρ = 0`.  Area-law manuscript,
`04-conditional.tex`, lines 466–469. -/
theorem embedF_kerProj_hatPhase_mul_sqrtSpec {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
    (hρ : ρ.PosSemidef) (u : ℝ) :
    embedF (((1 : Matrix X X ℂ) ⊗ₖ kerProj (posSemidef_marginalU hρ).1) *
      hatPhase (posSemidef_marginalXU hρ).1 u) * sqrtSpec hρ.1 = 0 := by
  set hs := posSemidef_marginalXU hρ
  have h1 : ((1 : Matrix X X ℂ) ⊗ₖ kerProj (posSemidef_marginalU hρ).1) * suppProj hs.1 = 0 := by
    have h0 := one_kronecker_kerProj_mul_sqrtSpec hs (posSemidef_marginalU hρ).1
    rw [suppProj_eq_sqrtSpec_mul hs, ← Matrix.mul_assoc]
    erw [h0]
    rw [Matrix.zero_mul]
  rw [hatPhase_eq hs.1 u, Matrix.mul_add, ← Matrix.mul_assoc, h1, Matrix.zero_mul, zero_add,
    ← embedF_mul, Matrix.mul_assoc, embedF_kerProj_mul_sqrtSpec hρ, Matrix.mul_zero]

end Entropy.MarginalPhase

end
