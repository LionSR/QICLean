/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralKronecker
import QICLean.Analysis.ResolventPhaseBound
import QICLean.Entropy.MarginalPhaseSetup

/-!
# The resolvent compression of a faithful state on three systems

Let `ρ` be a positive definite matrix on `x (U F)`.  On the Hilbert--Schmidt spaces of
`x (U F)` and `x U`, the operators `A = L_{σ_f} R_{ρ^{-1}}` and
`B = L_{σ_s} R_{ρ_{xU}^{-1}}` and the isometry
`V (Y √ρ_{xU}) = (Y ⊗ I_F) √ρ` satisfy `V* A V = B`, and `V √ρ_{xU} = √ρ`.  This file
builds the corresponding `Matrix.ResolventCompression`, using the eigenbases of `ρ`,
`ρ_{xU}`, `ρ_U` and `ρ_{UF}`.

## Main definitions

* `Entropy.MarginalPhase.compression` — the resolvent compression of `ρ`.

## Main results

* `Entropy.MarginalPhase.compression_opA_mulVec` — `A vec Y = vec (σ_f Y ρ⁻¹)`.
* `Entropy.MarginalPhase.compression_V_mulVec` — `V vec Y = vec ((Y ρ_{xU}^{-1/2} ⊗ I_F) √ρ)`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 352–370.
-/

open scoped Matrix Kronecker ComplexOrder

noncomputable section

namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

section Faithful

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}

theorem posDef_marginalUF [Nonempty X] (hρ : ρ.PosDef) : (marginalUF ρ).PosDef :=
  hρ.partialTraceLeft

theorem posDef_marginalXU [Nonempty F] (hρ : ρ.PosDef) : (marginalXU ρ).PosDef :=
  (hρ.submatrix assocE.injective).partialTraceRight

theorem posDef_marginalU [Nonempty X] [Nonempty F] (hρ : ρ.PosDef) : (marginalU ρ).PosDef :=
  (posDef_marginalXU hρ).partialTraceLeft

/-- Real power `t ↦ t ^ s` of a positive definite matrix through its eigenbasis. -/
def rpowSpec {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosDef)
    (s : ℝ) : Matrix n n ℂ :=
  spectralFun hA.1.eigenvectorUnitary (fun k => ((hA.1.eigenvalues k ^ s : ℝ) : ℂ))

theorem rpowSpec_mul {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) (s t : ℝ) : rpowSpec hA s * rpowSpec hA t = rpowSpec hA (s + t) := by
  rw [rpowSpec, rpowSpec, rpowSpec, spectralFun_mul]
  congr 1
  funext k
  simp only [Pi.mul_apply, ← Complex.ofReal_mul,
    ← Real.rpow_add (hA.eigenvalues_pos k)]

theorem rpowSpec_one {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) : rpowSpec hA 1 = A := by
  rw [rpowSpec]
  simp only [Real.rpow_one]
  exact hA.1.spectralFun_eigenvectorUnitary

theorem rpowSpec_zero {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) : rpowSpec hA 0 = 1 := by
  rw [rpowSpec]
  simp only [Real.rpow_zero, Complex.ofReal_one]
  exact spectralFun_one _

theorem rpowSpec_isHermitian {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosDef) (s : ℝ) : (rpowSpec hA s)ᴴ = rpowSpec hA s := by
  rw [rpowSpec, conjTranspose_spectralFun]
  congr 1
  funext k
  simp

/-- The eigenbasis of `σ_f = I_x / d ⊗ ρ_{UF}`. -/
def sigmaFUnitary (hUF : (marginalUF ρ).PosDef) : unitary (Matrix (X × (U × F)) (X × (U × F)) ℂ) :=
  kroneckerUnitary 1 hUF.1.eigenvectorUnitary

/-- The eigenvalues of `σ_f`. -/
def sigmaFEig (hUF : (marginalUF ρ).PosDef) (p : X × (U × F)) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * hUF.1.eigenvalues p.2

/-- The eigenbasis of `σ_s = I_x / d ⊗ ρ_U`. -/
def sigmaSUnitary (hU : (marginalU ρ).PosDef) : unitary (Matrix (X × U) (X × U) ℂ) :=
  kroneckerUnitary 1 hU.1.eigenvectorUnitary

/-- The eigenvalues of `σ_s`. -/
def sigmaSEig (hU : (marginalU ρ).PosDef) (p : X × U) : ℝ :=
  (Fintype.card X : ℝ)⁻¹ * hU.1.eigenvalues p.2

theorem spectralFun_one_unitary {n : Type*} [Fintype n] [DecidableEq n] (c : ℂ) :
    spectralFun (1 : unitary (Matrix n n ℂ)) (fun _ => c) = c • 1 := spectralFun_const _ _

theorem spectralFun_sigmaF (hUF : (marginalUF ρ).PosDef) :
    spectralFun (sigmaFUnitary hUF) (fun p => (sigmaFEig hUF p : ℂ)) = sigmaF ρ := by
  have h := spectralFun_kronecker (1 : unitary (Matrix X X ℂ)) hUF.1.eigenvectorUnitary
    (fun _ => ((Fintype.card X : ℂ)⁻¹)) (fun k => (hUF.1.eigenvalues k : ℂ))
  rw [spectralFun_one_unitary, hUF.1.spectralFun_eigenvectorUnitary] at h
  rw [sigmaF, h, sigmaFUnitary]
  congr 1
  funext p
  simp [sigmaFEig]

theorem spectralFun_sigmaS (hU : (marginalU ρ).PosDef) :
    spectralFun (sigmaSUnitary hU) (fun p => (sigmaSEig hU p : ℂ)) = sigmaS ρ := by
  have h := spectralFun_kronecker (1 : unitary (Matrix X X ℂ)) hU.1.eigenvectorUnitary
    (fun _ => ((Fintype.card X : ℂ)⁻¹)) (fun k => (hU.1.eigenvalues k : ℂ))
  rw [spectralFun_one_unitary, hU.1.spectralFun_eigenvectorUnitary] at h
  rw [sigmaS, h, sigmaSUnitary]
  congr 1
  funext p
  simp [sigmaSEig]

omit [DecidableEq X] [DecidableEq U] in
theorem embedF_add (A B : Matrix (X × U) (X × U) ℂ) :
    embedF (F := F) (A + B) = embedF A + embedF B := by
  ext i j; simp [embedF, add_mul]

omit [DecidableEq X] [DecidableEq U] in
theorem embedF_smul (c : ℂ) (A : Matrix (X × U) (X × U) ℂ) :
    embedF (F := F) (c • A) = c • embedF A := by
  ext i j; simp [embedF, mul_assoc]

variable [Nonempty X] [Nonempty F] (hρ : ρ.PosDef)

variable (ρ) in
/-- The linear map `Y ↦ (Y ρ_{xU}^{-1/2} ⊗ I_F) √ρ`. -/
def isoMap (hρ : ρ.PosDef) [Nonempty X] [Nonempty F] :
    Matrix (X × U) (X × U) ℂ →ₗ[ℂ] Matrix (X × (U × F)) (X × (U × F)) ℂ where
  toFun Y := embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) * rpowSpec hρ (1 / 2)
  map_add' A B := by rw [Matrix.add_mul, embedF_add, Matrix.add_mul]
  map_smul' c A := by rw [Matrix.smul_mul, embedF_smul, Matrix.smul_mul]; rfl

theorem isoMap_apply (Y : Matrix (X × U) (X × U) ℂ) :
    isoMap ρ hρ Y =
      embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) * rpowSpec hρ (1 / 2) := rfl

theorem trace_isoMap_conjTranspose_mul (Z Y : Matrix (X × U) (X × U) ℂ)
    (M : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    ((isoMap ρ hρ Z)ᴴ * M * isoMap ρ hρ Y).trace =
      (embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
        embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) *
        (rpowSpec hρ (1 / 2) * rpowSpec hρ (1 / 2))).trace := by
  rw [isoMap_apply, isoMap_apply, conjTranspose_mul, conjTranspose_embedF, conjTranspose_mul,
    rpowSpec_isHermitian, rpowSpec_isHermitian]
  rw [show rpowSpec hρ (1 / 2) * embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
      (embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) * rpowSpec hρ (1 / 2)) =
      rpowSpec hρ (1 / 2) * (embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
        embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) * rpowSpec hρ (1 / 2)) by
      simp only [Matrix.mul_assoc]]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- `V` is an isometry.  Area-law manuscript, `04-conditional.tex`, lines 359–363. -/
theorem linMatrix_isoMap_isometry :
    (linMatrix (isoMap ρ hρ))ᴴ * linMatrix (isoMap ρ hρ) = 1 := by
  set hs := posDef_marginalXU (F := F) hρ
  refine ext_star_vec_dotProduct_mulVec_vec fun Z Y => ?_
  rw [← mulVec_mulVec, ← star_mulVec_dotProduct, linMatrix_mulVec_vec, linMatrix_mulVec_vec,
    one_mulVec, star_vec_dotProduct_vec, star_vec_dotProduct_vec,
    ← Matrix.mul_one (isoMap ρ hρ Z)ᴴ, trace_isoMap_conjTranspose_mul, Matrix.mul_one,
    embedF_mul, rpowSpec_mul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, rpowSpec_one,
    trace_mul_comm, trace_mul_embedF]
  change (marginalXU ρ * (rpowSpec hs (-1 / 2) * Zᴴ * (Y * rpowSpec hs (-1 / 2)))).trace = _
  rw [show (marginalXU ρ * (rpowSpec hs (-1 / 2) * Zᴴ * (Y * rpowSpec hs (-1 / 2)))) =
      rpowSpec hs 1 * (rpowSpec hs (-1 / 2) * Zᴴ * (Y * rpowSpec hs (-1 / 2))) by
      rw [rpowSpec_one]]
  rw [show rpowSpec hs 1 * (rpowSpec hs (-1 / 2) * Zᴴ * (Y * rpowSpec hs (-1 / 2))) =
      (rpowSpec hs 1 * rpowSpec hs (-1 / 2)) * (Zᴴ * Y * rpowSpec hs (-1 / 2)) by
      simp only [Matrix.mul_assoc], trace_mul_comm, rpowSpec_mul, Matrix.mul_assoc,
    rpowSpec_mul]
  norm_num [rpowSpec_zero]

end Faithful


end Entropy.MarginalPhase

end
