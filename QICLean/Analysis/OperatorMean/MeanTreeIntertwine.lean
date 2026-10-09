/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.FiniteTree
import QICLean.Analysis.OperatorMean.GeometricMeanIntertwine

/-!
# Rectangular transport of an actual weighted mean tree

The evaluation of a weighted mean tree transports along a common rectangular
intertwiner of its positive definite leaf inputs. The identity retains the
tree, including repeated leaf labels and zero edge weights.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `06-transport.tex`, the weighted-tree definition, lines 28–34, and
  Lemma 7.1, transport:means, lines 99–128, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The evaluation identity is auxiliary to the manuscript's transport estimate.
-/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

namespace MeanTree

variable {ι : Type*}

/-- The evaluation of a finite weighted mean tree transports along a common
rectangular intertwiner of positive definite leaf inputs. Auxiliary to
OpenAI's area-law manuscript, `06-transport.tex`, lines 28–34 and 99–128,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Repeated labels and zero edge weights are included. -/
theorem eval_intertwine
    {A : ι → Matrix n n ℂ} {B : ι → Matrix m m ℂ}
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (J : Matrix n m ℂ) (hJ : ∀ i, A i * J = J * B i)
    (T : MeanTree ι) :
    T.eval A * J = J * T.eval B := by
  induction T
  case node p l r ihl ihr =>
    simpa only [eval_node] using
      geomMean_intertwine (posDef_eval hA l) (posDef_eval hA r)
        (posDef_eval hB l) (posDef_eval hB r) J ihl ihr p
  case leaf i =>
    exact hJ i

end MeanTree

end Matrix
