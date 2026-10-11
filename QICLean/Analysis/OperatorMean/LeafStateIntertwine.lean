/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.MeanTreeDerivativeIntertwine
import QICLean.Channel.SingleKraus

/-!
# Trace-adjoint leaf maps along a rectangular intertwiner

Compression of the normalized leaf maps gives the corresponding embedding
identity for their trace adjoints. The intertwiner may be rectangular, and
the matrix acted on may be arbitrary.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, the trace-adjoint convention and transport states,
  06-transport.tex, transport:states, lines 393–401, revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a.

The embedding identity is auxiliary to the manuscript's state construction.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.MeanTree

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {ι : Type*} [DecidableEq ι]

/-- The trace adjoint of a normalized leaf map transports an embedded matrix.
Auxiliary to OpenAI's area-law manuscript, 06-transport.tex,
transport:states and the trace-adjoint convention, lines 393–401, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Repeated labels and zero terminal weights are included. -/
theorem traceAdjoint_leafMap_intertwine
    {A : ι → Matrix n n ℂ} {B : ι → Matrix m m ℂ}
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (J : Matrix n m ℂ) (hJ : ∀ i, A i * J = J * B i)
    (T : MeanTree ι) (j : ι) (ρ : Matrix m m ℂ) :
    traceAdjointMap (T.leafMap A j).toLinearMap (J * ρ * Jᴴ) =
      J * traceAdjointMap (T.leafMap B j).toLinearMap ρ * Jᴴ := by
  have hcomp : (singleKrausMap Jᴴ).comp (T.leafMap A j).toLinearMap =
      (T.leafMap B j).toLinearMap.comp (singleKrausMap Jᴴ) := by
    apply LinearMap.ext
    intro X
    simpa only [LinearMap.comp_apply, singleKrausMap_apply,
      conjTranspose_conjTranspose, ContinuousLinearMap.coe_coe] using
      leafMap_compress hA hB J hJ T j X
  simpa only [traceAdjointMap_comp, traceAdjointMap_singleKrausMap,
    conjTranspose_conjTranspose, LinearMap.comp_apply, singleKrausMap_apply] using
    LinearMap.congr_fun (congrArg traceAdjointMap hcomp) ρ

end Matrix.MeanTree
