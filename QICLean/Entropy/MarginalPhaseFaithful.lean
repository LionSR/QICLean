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

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem posDef_marginalUF [Nonempty X] (hρ : ρ.PosDef) : (marginalUF ρ).PosDef :=
  hρ.partialTraceLeft

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
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

omit [DecidableEq F] in
theorem spectralFun_sigmaS (hU : (marginalU ρ).PosDef) :
    spectralFun (sigmaSUnitary hU) (fun p => (sigmaSEig hU p : ℂ)) = sigmaS ρ := by
  have h := spectralFun_kronecker (1 : unitary (Matrix X X ℂ)) hU.1.eigenvectorUnitary
    (fun _ => ((Fintype.card X : ℂ)⁻¹)) (fun k => (hU.1.eigenvalues k : ℂ))
  rw [spectralFun_one_unitary, hU.1.spectralFun_eigenvectorUnitary] at h
  rw [sigmaS, h, sigmaSUnitary]
  congr 1
  funext p
  simp [sigmaSEig]

omit [DecidableEq X] [DecidableEq U] [Fintype X] [Fintype U] [Fintype F] in
theorem embedF_add (A B : Matrix (X × U) (X × U) ℂ) :
    embedF (F := F) (A + B) = embedF A + embedF B := by
  ext i j; simp [embedF, add_mul]

omit [DecidableEq X] [DecidableEq U] [Fintype X] [Fintype U] [Fintype F] in
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

theorem trace_isoMap_conjTranspose_mul_mul (Z Y : Matrix (X × U) (X × U) ℂ)
    (M N : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    ((isoMap ρ hρ Z)ᴴ * M * isoMap ρ hρ Y * N).trace =
      (embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
        embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) *
        (rpowSpec hρ (1 / 2) * N * rpowSpec hρ (1 / 2))).trace := by
  rw [isoMap_apply, isoMap_apply, conjTranspose_mul, conjTranspose_embedF, conjTranspose_mul,
    rpowSpec_isHermitian, rpowSpec_isHermitian]
  rw [show rpowSpec hρ (1 / 2) * embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
      (embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) * rpowSpec hρ (1 / 2)) * N =
      rpowSpec hρ (1 / 2) * (embedF (rpowSpec (posDef_marginalXU hρ) (-1 / 2) * Zᴴ) * M *
        embedF (Y * rpowSpec (posDef_marginalXU hρ) (-1 / 2)) * rpowSpec hρ (1 / 2) * N) by
      simp only [Matrix.mul_assoc]]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The eigenbasis of `A = L_{σ_f} R_{ρ^{-1}}` on the Hilbert--Schmidt space. -/
def unitaryA : unitary (Matrix ((X × (U × F)) × (X × (U × F))) ((X × (U × F)) × (X × (U × F))) ℂ) :=
  kroneckerUnitary (conjUnitary hρ.1.eigenvectorUnitary) (sigmaFUnitary (posDef_marginalUF hρ))

/-- The eigenvalues `σ_k / ρ_j` of `A`. -/
def eigA (p : (X × (U × F)) × (X × (U × F))) : ℝ :=
  hρ.1.eigenvalues p.1 ^ (-1 : ℝ) * sigmaFEig (posDef_marginalUF hρ) p.2

/-- The eigenbasis of `B = L_{σ_s} R_{ρ_{xU}^{-1}}`. -/
def unitaryB : unitary (Matrix ((X × U) × (X × U)) ((X × U) × (X × U)) ℂ) :=
  kroneckerUnitary (conjUnitary (posDef_marginalXU (F := F) hρ).1.eigenvectorUnitary)
    (sigmaSUnitary (posDef_marginalU hρ))

/-- The eigenvalues of `B`. -/
def eigB (p : (X × U) × (X × U)) : ℝ :=
  (posDef_marginalXU (F := F) hρ).1.eigenvalues p.1 ^ (-1 : ℝ) *
    sigmaSEig (posDef_marginalU (F := F) hρ) p.2

omit [Nonempty F] in
theorem spectralFun_eigA :
    spectralFun (unitaryA hρ) (fun p => (eigA hρ p : ℂ)) = (rpowSpec hρ (-1))ᵀ ⊗ₖ sigmaF ρ := by
  rw [rpowSpec, transpose_spectralFun, ← spectralFun_sigmaF (posDef_marginalUF hρ),
    spectralFun_kronecker, unitaryA]
  congr 1
  funext p
  simp [eigA]

theorem spectralFun_eigB :
    spectralFun (unitaryB hρ) (fun p => (eigB hρ p : ℂ)) =
      (rpowSpec (posDef_marginalXU (F := F) hρ) (-1))ᵀ ⊗ₖ sigmaS ρ := by
  rw [rpowSpec, transpose_spectralFun, ← spectralFun_sigmaS (posDef_marginalU hρ),
    spectralFun_kronecker, unitaryB]
  congr 1
  funext p
  simp [eigB]

omit [Nonempty F] in
theorem eigA_pos (p : (X × (U × F)) × (X × (U × F))) : 0 < eigA hρ p := by
  have h1 := hρ.eigenvalues_pos p.1
  have h2 := (posDef_marginalUF hρ).eigenvalues_pos p.2.2
  unfold eigA sigmaFEig
  have : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  positivity

theorem eigB_pos (p : (X × U) × (X × U)) : 0 < eigB (F := F) hρ p := by
  have h1 := (posDef_marginalXU (F := F) hρ).eigenvalues_pos p.1
  have h2 := (posDef_marginalU (F := F) hρ).eigenvalues_pos p.2.2
  unfold eigB sigmaSEig
  have : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  positivity

/-- `V* A V = B`.  Area-law manuscript, `04-conditional.tex`, lines 364–366. -/
theorem linMatrix_isoMap_compress :
    (linMatrix (isoMap ρ hρ))ᴴ * spectralFun (unitaryA hρ) (fun p => (eigA hρ p : ℂ)) *
        linMatrix (isoMap ρ hρ) =
      spectralFun (unitaryB hρ) (fun p => (eigB hρ p : ℂ)) := by
  set hs := posDef_marginalXU (F := F) hρ
  refine ext_star_vec_dotProduct_mulVec_vec fun Z Y => ?_
  rw [spectralFun_eigA, spectralFun_eigB, ← mulVec_mulVec, ← mulVec_mulVec,
    ← star_mulVec_dotProduct, linMatrix_mulVec_vec, linMatrix_mulVec_vec, kronecker_mulVec_vec,
    kronecker_mulVec_vec, transpose_transpose, transpose_transpose, star_vec_dotProduct_vec,
    star_vec_dotProduct_vec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    trace_isoMap_conjTranspose_mul_mul, rpowSpec_mul, rpowSpec_mul]
  norm_num [rpowSpec_zero]
  rw [trace_mul_comm, ← Matrix.mul_assoc, embedF_mul, trace_mul_comm, trace_mul_embedF,
    partialTraceRight_sigmaF, Matrix.mul_assoc Y, ← Matrix.mul_assoc _ _ Zᴴ, rpowSpec_mul]
  norm_num
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]

/-- The resolvent compression of a faithful state on `x (U F)`: `A = L_{σ_f} R_{ρ^{-1}}`,
`B = L_{σ_s} R_{ρ_{xU}^{-1}}`, `V (Y √ρ_{xU}) = (Y ⊗ I_F) √ρ` and `b₀ = √ρ_{xU}`.
Area-law manuscript, `04-conditional.tex`, lines 352–367. -/
def compression : ResolventCompression ((X × (U × F)) × (X × (U × F))) ((X × U) × (X × U)) where
  UA := unitaryA hρ
  lam := eigA hρ
  UB := unitaryB hρ
  mu := eigB hρ
  V := linMatrix (isoMap ρ hρ)
  b0 := vec (rpowSpec (posDef_marginalXU hρ) (1 / 2))
  lam_pos := eigA_pos hρ
  mu_pos := eigB_pos hρ
  isometry := linMatrix_isoMap_isometry hρ
  compress := linMatrix_isoMap_compress hρ

theorem compression_a0 : (compression hρ).a0 = vec (rpowSpec hρ (1 / 2)) := by
  change linMatrix (isoMap ρ hρ) *ᵥ vec _ = _
  rw [linMatrix_mulVec_vec, isoMap_apply, rpowSpec_mul]
  norm_num [rpowSpec_zero, embedF_one]

/-- Complex power `t ↦ t ^ z` of a positive definite matrix through its eigenbasis. -/
def cpowSpec {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.PosDef)
    (z : ℂ) : Matrix n n ℂ :=
  spectralFun hA.1.eigenvectorUnitary (fun k => ((hA.1.eigenvalues k : ℝ) : ℂ) ^ z)

theorem ofReal_rpow_neg_one_mul_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    (((a ^ (-1 : ℝ) * b : ℝ)) : ℂ) ^ z = (a : ℂ) ^ (-z) * (b : ℂ) ^ z := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hb.le,
    Real.rpow_neg_one, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_pos.ne), ← Complex.cpow_neg]

theorem rpowSpec_mul_cpowSpec_mul_rpowSpec {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (z : ℂ) :
    rpowSpec hA (1 / 2) * cpowSpec hA z * rpowSpec hA (-1 / 2) = cpowSpec hA z := by
  rw [rpowSpec, cpowSpec, rpowSpec, spectralFun_mul, spectralFun_mul]
  congr 1
  funext k
  have hk := hA.eigenvalues_pos k
  simp only [Pi.mul_apply]
  rw [mul_comm, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hk]
  norm_num

theorem rpowSpec_mul_cpowSpec_comm {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosDef) (s : ℝ) (z : ℂ) :
    rpowSpec hA s * cpowSpec hA z = cpowSpec hA z * rpowSpec hA s := by
  rw [rpowSpec, cpowSpec, spectralFun_mul, spectralFun_mul, mul_comm]

/-- The phase gap of the compression:
`A^z a₀ - V B^z b₀ = (σ_f^z ρ^{-z} - (σ_s^z ρ_{xU}^{-z} ⊗ I_F)) √ρ`.  Area-law manuscript,
`04-conditional.tex`, lines 434–444. -/
theorem compression_phaseGap (z : ℂ) :
    (compression hρ).phaseGap z =
      vec ((spectralFun (sigmaFUnitary (posDef_marginalUF hρ))
          (fun p => ((sigmaFEig (posDef_marginalUF hρ) p : ℝ) : ℂ) ^ z) * cpowSpec hρ (-z) -
        embedF (spectralFun (sigmaSUnitary (posDef_marginalU (F := F) hρ))
          (fun p => ((sigmaSEig (posDef_marginalU (F := F) hρ) p : ℝ) : ℂ) ^ z) *
            cpowSpec (posDef_marginalXU (F := F) hρ) (-z))) * rpowSpec hρ (1 / 2)) := by
  set hs := posDef_marginalXU (F := F) hρ
  have hA : spectralFun (compression hρ).UA (fun k => ((compression hρ).lam k : ℂ) ^ z) =
      (cpowSpec hρ (-z))ᵀ ⊗ₖ spectralFun (sigmaFUnitary (posDef_marginalUF hρ))
        (fun p => ((sigmaFEig (posDef_marginalUF hρ) p : ℝ) : ℂ) ^ z) := by
    refine spectralFun_leftRight_mul _ _ hρ.1.eigenvalues (sigmaFEig (posDef_marginalUF hρ))
      (fun t => (t : ℂ) ^ z) (fun a => (a : ℂ) ^ (-z)) (fun b => (b : ℂ) ^ z) fun k j => ?_
    refine ofReal_rpow_neg_one_mul_cpow (hρ.eigenvalues_pos k) ?_ z
    have := (posDef_marginalUF hρ).eigenvalues_pos j.2
    unfold sigmaFEig
    have : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
    positivity
  have hB : spectralFun (compression hρ).UB (fun k => ((compression hρ).mu k : ℂ) ^ z) =
      (cpowSpec hs (-z))ᵀ ⊗ₖ spectralFun (sigmaSUnitary (posDef_marginalU (F := F) hρ))
        (fun p => ((sigmaSEig (posDef_marginalU (F := F) hρ) p : ℝ) : ℂ) ^ z) := by
    refine spectralFun_leftRight_mul _ _ hs.1.eigenvalues
      (sigmaSEig (posDef_marginalU (F := F) hρ))
      (fun t => (t : ℂ) ^ z) (fun a => (a : ℂ) ^ (-z)) (fun b => (b : ℂ) ^ z) fun k j => ?_
    refine ofReal_rpow_neg_one_mul_cpow (hs.eigenvalues_pos k) ?_ z
    have := (posDef_marginalU (F := F) hρ).eigenvalues_pos j.2
    unfold sigmaSEig
    have : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
    positivity
  set SF := spectralFun (sigmaFUnitary (posDef_marginalUF hρ))
    (fun p => ((sigmaFEig (posDef_marginalUF hρ) p : ℝ) : ℂ) ^ z)
  set SS := spectralFun (sigmaSUnitary (posDef_marginalU (F := F) hρ))
    (fun p => ((sigmaSEig (posDef_marginalU (F := F) hρ) p : ℝ) : ℂ) ^ z)
  have h1 : SF * rpowSpec hρ (1 / 2) * cpowSpec hρ (-z) =
      SF * cpowSpec hρ (-z) * rpowSpec hρ (1 / 2) := by
    rw [Matrix.mul_assoc, rpowSpec_mul_cpowSpec_comm, Matrix.mul_assoc]
  have h2 : SS * rpowSpec hs (1 / 2) * cpowSpec hs (-z) * rpowSpec hs (-1 / 2) =
      SS * cpowSpec hs (-z) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (rpowSpec hs (1 / 2)),
      rpowSpec_mul_cpowSpec_mul_rpowSpec]
  rw [ResolventCompression.phaseGap, hA, hB, compression_a0, kronecker_mulVec_vec,
    transpose_transpose]
  change _ - linMatrix (isoMap ρ hρ) *ᵥ (_ *ᵥ vec (rpowSpec hs (1 / 2))) = _
  rw [kronecker_mulVec_vec, transpose_transpose, linMatrix_mulVec_vec, isoMap_apply, h1, h2,
    ← vec_sub, Matrix.sub_mul]

end Faithful


end Entropy.MarginalPhase

end
