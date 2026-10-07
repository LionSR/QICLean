/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.PartialTrace
import QICLean.Analysis.TraceDistance
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Marginals on three systems for the marginal-phase comparison

For a matrix `ρ` on `x (U F)`, indexed by `X × (U × F)`, this file fixes the
marginals `ρ_{UF} = tr_x ρ`, `ρ_{xU} = tr_F ρ` and `ρ_U = tr_x ρ_{xU}`, the reference
operators `σ_f = I_x / d ⊗ ρ_{UF}` and `σ_s = I_x / d ⊗ ρ_U` with `d = dim x`, and the
embedding `W ↦ W ⊗ I_F` of operators on `x U` into operators on `x (U F)`.

## Main definitions

* `Entropy.MarginalPhase.marginalXU`, `marginalU`, `marginalUF`.
* `Entropy.MarginalPhase.sigmaF`, `sigmaS`.
* `Entropy.MarginalPhase.embedF`.

## Main results

* `Entropy.MarginalPhase.trace_mul_embedF` — `tr (M (W ⊗ I_F)) = tr (tr_F M · W)`.
* `Entropy.MarginalPhase.partialTraceRight_sigmaF` — `tr_F σ_f = σ_s`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 345–351.
-/

open scoped Matrix Kronecker

noncomputable section


namespace Entropy.MarginalPhase

open Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

/-- The reassociation `(x U) F ≃ x (U F)`. -/
abbrev assocE : (X × U) × F ≃ X × (U × F) := Equiv.prodAssoc X U F

/-- The marginal `ρ_{xU} = tr_F ρ`. -/
def marginalXU (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) : Matrix (X × U) (X × U) ℂ :=
  partialTraceRight (ρ.submatrix assocE assocE)

/-- The marginal `ρ_U = tr_x ρ_{xU}`. -/
def marginalU (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) : Matrix U U ℂ :=
  partialTraceLeft (marginalXU ρ)

/-- The marginal `ρ_{UF} = tr_x ρ`. -/
def marginalUF (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) : Matrix (U × F) (U × F) ℂ :=
  partialTraceLeft ρ

/-- The reference operator `σ_f = I_x / d ⊗ ρ_{UF}`.  Area-law manuscript,
`04-conditional.tex`, line 348. -/
def sigmaF (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) : Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  ((Fintype.card X : ℂ)⁻¹ • (1 : Matrix X X ℂ)) ⊗ₖ marginalUF ρ

/-- The reference operator `σ_s = I_x / d ⊗ ρ_U`.  Area-law manuscript,
`04-conditional.tex`, line 350. -/
def sigmaS (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) : Matrix (X × U) (X × U) ℂ :=
  ((Fintype.card X : ℂ)⁻¹ • (1 : Matrix X X ℂ)) ⊗ₖ marginalU ρ

/-- The embedding `W ↦ W ⊗ I_F` of operators on `x U` into operators on `x (U F)`. -/
def embedF (W : Matrix (X × U) (X × U) ℂ) : Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  (W ⊗ₖ (1 : Matrix F F ℂ)).submatrix assocE.symm assocE.symm

omit [DecidableEq X] [DecidableEq U] in
theorem embedF_mul (A B : Matrix (X × U) (X × U) ℂ) :
    embedF (F := F) A * embedF B = embedF (A * B) := by
  rw [embedF, embedF, embedF, submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]

omit [Fintype X] [Fintype U] [Fintype F] in
theorem embedF_one : embedF (F := F) (1 : Matrix (X × U) (X × U) ℂ) = 1 := by
  rw [embedF, one_kronecker_one, submatrix_one_equiv]

omit [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] in
theorem conjTranspose_embedF (W : Matrix (X × U) (X × U) ℂ) :
    (embedF (F := F) W)ᴴ = embedF Wᴴ := by
  rw [embedF, embedF, conjTranspose_submatrix, conjTranspose_kronecker, conjTranspose_one]

omit [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] in
theorem embedF_sub (A B : Matrix (X × U) (X × U) ℂ) :
    embedF (F := F) (A - B) = embedF A - embedF B := by
  ext i j
  simp [embedF, sub_mul]

omit [DecidableEq X] [DecidableEq U] in
/-- `tr (M (W ⊗ I_F)) = tr (tr_F M · W)`. -/
theorem trace_mul_embedF (M : Matrix (X × (U × F)) (X × (U × F)) ℂ)
    (W : Matrix (X × U) (X × U) ℂ) :
    (M * embedF W).trace = (partialTraceRight (M.submatrix assocE assocE) * W).trace := by
  rw [trace_partialTraceRight_mul, embedF, ← trace_submatrix_equiv assocE,
    ← submatrix_mul_equiv (e₂ := assocE)]
  simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]

omit [DecidableEq X] [Fintype U] [DecidableEq U] [DecidableEq F] in
theorem marginalU_eq (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    marginalU ρ = partialTraceRight (marginalUF ρ) := by
  ext u u'
  simp only [marginalU, marginalXU, marginalUF, partialTraceLeft_apply, partialTraceRight_apply,
    submatrix_apply, Equiv.prodAssoc_apply]
  exact Finset.sum_comm

omit [Fintype U] [DecidableEq U] [DecidableEq F] in
theorem partialTraceRight_sigmaF (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    partialTraceRight ((sigmaF ρ).submatrix assocE assocE) = sigmaS ρ := by
  ext ⟨x, u⟩ ⟨x', u'⟩
  simp only [sigmaF, sigmaS, partialTraceRight_apply, submatrix_apply, Equiv.prodAssoc_apply,
    kroneckerMap_apply, marginalU_eq, Finset.mul_sum]

end Entropy.MarginalPhase

end
