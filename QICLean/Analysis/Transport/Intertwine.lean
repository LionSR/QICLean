/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.LeafStateIntertwine
import QICLean.Analysis.Transport.Defs
import QICLean.Analysis.CoisometricCompression

/-!
# Rectangular transport of the mean-tree states

The imaginary powers of intertwined positive definite roots intertwine.
Together with the trace-adjoint leaf-map identity, this gives the embedding
identity for the transport matrices defined in the area-law manuscript.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, 06-transport.tex, transport:states, lines 393–401, revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.Transport

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Imaginary powers of positive definite matrices respect a rectangular
intertwiner. Auxiliary to OpenAI's area-law manuscript, 06-transport.tex,
transport:states, lines 393–401, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem imagPow_intertwine {M : Matrix n n ℂ} {N : Matrix m m ℂ}
    (hM : M.PosDef) (hN : N.PosDef) (J : Matrix n m ℂ)
    (hJ : M * J = J * N) (u : ℝ) : imagPow M u * J = J * imagPow N u := by
  have hlog : CFC.log M * J = J * CFC.log N := by
    simpa only [CFC.log] using
      ConditionalMovement.QuantumSSA.cfc_intertwine
        hM.isHermitian hN.isHermitian J hJ Real.log
  have hscaled : J * ((-u) • (Complex.I • CFC.log N)) =
      ((-u) • (Complex.I • CFC.log M)) * J := by
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using
      congrArg (fun X : Matrix n m ℂ ↦ (-u) • (Complex.I • X)) hlog.symm
  have hexp := mul_exp_eq_exp_mul_of_mul_eq J
    ((-u) • (Complex.I • CFC.log N)) ((-u) • (Complex.I • CFC.log M)) hscaled
  exact hexp.symm

/-- The manuscript's transport matrix respects the embedding of a root
vector along a common rectangular intertwiner. Auxiliary to OpenAI's
area-law manuscript, 06-transport.tex, transport:states, lines 393–401,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The identity retains the same tree, labels and weights. -/
theorem transportState_intertwine {ι : Type*} [DecidableEq ι]
    {A : ι → Matrix n n ℂ} {B : ι → Matrix m m ℂ}
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (J : Matrix n m ℂ) (hJ : ∀ i, A i * J = J * B i)
    (T : MeanTree ι) (j : ι) (v : m → ℂ) (u : ℝ) :
    transportState T A (J *ᵥ v) j u = J * transportState T B v j u * Jᴴ := by
  dsimp only [transportState]
  have hvec : imagPow (T.eval A) u *ᵥ (J *ᵥ v) =
      J *ᵥ (imagPow (T.eval B) u *ᵥ v) := by
    simpa only [mulVec_mulVec] using
      congrArg (fun K : Matrix n m ℂ ↦ K *ᵥ v)
        (imagPow_intertwine (MeanTree.posDef_eval hA T)
          (MeanTree.posDef_eval hB T) J (MeanTree.eval_intertwine hA hB J hJ T) u)
  rw [hvec]
  simpa only [mul_vecMulVec, vecMulVec_mul, star_mulVec] using
    MeanTree.traceAdjoint_leafMap_intertwine hA hB J hJ T j
      (vecMulVec (imagPow (T.eval B) u *ᵥ v) (star (imagPow (T.eval B) u *ᵥ v)))

end Matrix.Transport
