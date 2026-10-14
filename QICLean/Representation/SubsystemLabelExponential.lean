/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SubsystemLabelCoordinates

/-!
# Regional label exponential moments of pure tensor powers

A regional exponential expectation of a literal product vector is the
trace of the same exponential against the tensor power of its actual
regional reduced density. The one-copy vector need not be normalized.
The identity includes zero copies, empty regions, and zero-dimensional
local spaces.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, proof of
`comparator:sharp-upper`, lines 405–412; the post-marginal identity used
there is `comparator:post-marginal`. Source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- A regional label exponential has the same expectation in the literal
pure tensor power and in the tensor power of the actual regional marginal.
No normalization or regional invariance is assumed.

Source: OpenAI area-law manuscript, `07-comparators.tex`,
`comparator:sharp-upper`, lines 405–412, using
`comparator:post-marginal`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem re_inner_exp_labelEntropy_subsystemPerm_prod
    (ψ : EuclideanSpace ℂ ((f : F) → ι f)) (k : ℕ) (Q : Finset F) (u : ℝ) :
    let Ψ := WithLp.toLp 2 (fun x : Config k ι ↦ ∏ j, ψ (x j))
    (⟪Ψ, Matrix.toEuclideanLin
      (NormedSpace.exp ((u : ℂ) • labelEntropy (subsystemPerm k ι Q))) Ψ⟫_ℂ).re =
      (Matrix.finKronecker (fun _ : Fin k ↦ FiniteProduct.reducedPure ι ψ Q) *
        NormedSpace.exp ((u : ℂ) •
          labelEntropy (copyPerm (FiniteProduct.Configuration ι Q) k))).trace.re := by
  classical
  have hexp {A : Type _} [Fintype A] [DecidableEq A]
      (φ : Equiv.Perm (Fin k) →* Equiv.Perm A) :
      NormedSpace.exp ((u : ℂ) • labelEntropy φ) =
        ∑ l, Complex.exp ((u : ℂ) * (Real.log l.dim : ℂ)) • labelProj φ l := by
    rw [labelEntropy, labelObservable_eq_hom, ← map_smul,
      Matrix.IsOrthogonalResolution.exp_hom, Matrix.IsOrthogonalResolution.hom_apply]
    rfl
  have hM :
      (NormedSpace.exp ((u : ℂ) • labelEntropy (subsystemPerm k ι Q))).submatrix
        (subsystemSplitEquiv ι k Q).symm (subsystemSplitEquiv ι k Q).symm =
      Matrix.kronecker
        (1 : Matrix (Fin k → FiniteProduct.Configuration ι Qᶜ)
          (Fin k → FiniteProduct.Configuration ι Qᶜ) ℂ)
        (NormedSpace.exp ((u : ℂ) •
          labelEntropy (copyPerm (FiniteProduct.Configuration ι Q) k))) := by
    rw [hexp, hexp]
    ext x y
    simpa only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.mul_sum, mul_left_comm] using
      (Finset.sum_congr rfl (fun (l : IrrepLabel (Equiv.Perm (Fin k)))
        (_ : l ∈ Finset.univ) ↦ congrArg
          (fun M ↦ Complex.exp ((u : ℂ) * (Real.log l.dim : ℂ)) * M x y)
          (labelProj_subsystemPerm_submatrix ι k Q l)))
  let τ : FiniteProduct.Configuration ι Qᶜ × FiniteProduct.Configuration ι Q → ℂ :=
    fun x ↦ ψ ((FiniteProduct.splitEquiv ι Q).symm (x.2, x.1))
  let v' : (Fin k → FiniteProduct.Configuration ι Qᶜ) ×
      (Fin k → FiniteProduct.Configuration ι Q) → ℂ :=
    fun x ↦ ∏ j, τ (x.1 j, x.2 j)
  have htrace (P : Matrix (Fin k → FiniteProduct.Configuration ι Q)
      (Fin k → FiniteProduct.Configuration ι Q) ℂ) :
      (Matrix.finKronecker (fun _ : Fin k ↦ FiniteProduct.reducedPure ι ψ Q) * P).trace =
        (Matrix.vecMulVec v' (star v') * Matrix.kronecker
          (1 : Matrix (Fin k → FiniteProduct.Configuration ι Qᶜ)
            (Fin k → FiniteProduct.Configuration ι Qᶜ) ℂ) P).trace := by
    simpa only [v', Matrix.partialTraceLeft_vecMulVec_prod,
      show Matrix.partialTraceLeft (Matrix.vecMulVec τ (star τ)) =
        FiniteProduct.reducedPure ι ψ Q from rfl, Matrix.kronecker] using
      Matrix.trace_partialTraceLeft_mul P (Matrix.vecMulVec v' (star v'))
  rw [htrace, ← hM, Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  have hv : v' = (fun x : Config k ι ↦ ∏ j, ψ (x j)) ∘
      (subsystemSplitEquiv ι k Q).symm := rfl
  simp only [hv, Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  simpa only [Equiv.symm_symm, Equiv.symm_comp_self, Function.comp_id,
    dotProduct, Function.comp_apply, Pi.star_apply] using
    congrArg Complex.re ((subsystemSplitEquiv ι k Q).symm.sum_comp
      (fun x : Config k ι ↦
        (NormedSpace.exp ((u : ℂ) • labelEntropy (subsystemPerm k ι Q)) *ᵥ
          (fun y : Config k ι ↦ ∏ j, ψ (y j))) x * star (∏ j, ψ (x j)))).symm

end TensorPower
