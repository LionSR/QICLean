/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixSandwichIntertwine
import QICLean.Analysis.OperatorMean.TreeDerivative
import QICLean.Analysis.OperatorMean.MeanTreeIntertwine
import QICLean.Analysis.OperatorMean.GeometricMeanDerivativeIntertwine

/-!
# Rectangular transport of mean-tree derivative maps

The recursive derivative of an actual weighted mean tree transports every
matrix direction along a common rectangular intertwiner of its positive
definite leaf inputs. The normalized leaf maps obey the same identity,
including zero terminal weights. Taking adjoints of the intertwining equations
gives compression on arbitrary ambient directions. Repeated labels are
retained in the recursive sums.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, Lemma 7.2, 06-transport.tex, lines 144–172, revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix.MeanTree

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {ι : Type*} [DecidableEq ι]

/-- Rectangular transport of the recursive derivative in a leaf label.
Auxiliary to OpenAI's area-law manuscript, Lemma 7.2,
06-transport.tex, lines 144–172, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The direction is arbitrary, and repeated labels are included. -/
theorem derivLabel_intertwine
    {A : ι → Matrix n n ℂ} {B : ι → Matrix m m ℂ}
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (J : Matrix n m ℂ) (hJ : ∀ i, A i * J = J * B i)
    (T : MeanTree ι) (j : ι) (H : Matrix m m ℂ) :
    T.derivLabel A j (J * H * Jᴴ) = J * T.derivLabel B j H * Jᴴ := by
  induction T
  case node p l r ihl ihr =>
    simp only [derivLabel, _root_.add_apply, ContinuousLinearMap.comp_apply, ihl, ihr]
    rw [geomMeanDerivLeft_intertwine (posDef_eval hA l) (posDef_eval hA r)
      (posDef_eval hB l) (posDef_eval hB r) J (eval_intertwine hA hB J hJ l)
      (eval_intertwine hA hB J hJ r) p.2,
      geomMeanDerivRight_intertwine (posDef_eval hA l) (posDef_eval hA r)
        (posDef_eval hB l) (posDef_eval hB r) J (eval_intertwine hA hB J hJ l)
        (eval_intertwine hA hB J hJ r) p.2]
    simp only [Matrix.mul_add, Matrix.add_mul]
  case leaf i =>
    by_cases hij : i = j <;> simp [derivLabel, hij]

/-- Rectangular transport of the normalized leaf map, including labels of
zero terminal weight. Auxiliary to OpenAI's area-law manuscript, Lemma 7.2,
06-transport.tex, lines 144–172, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem leafMap_intertwine
    {A : ι → Matrix n n ℂ} {B : ι → Matrix m m ℂ}
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (J : Matrix n m ℂ) (hJ : ∀ i, A i * J = J * B i)
    (T : MeanTree ι) (j : ι) (H : Matrix m m ℂ) :
    T.leafMap A j (J * H * Jᴴ) = J * T.leafMap B j H * Jᴴ := by
  simp only [leafMap, normalizedDerivMap, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, sandwichL_apply]
  rw [((hA j).rpow_isHermitian _).sandwich_intertwine
    ((hB j).rpow_isHermitian _) J
    ((hA j).posSemidef.rpow_intertwine (hB j).posSemidef J (hJ j) _) H]
  rw [derivLabel_intertwine hA hB J hJ T j,
    ((posDef_eval hA T).rpow_isHermitian _).sandwich_intertwine
      ((posDef_eval hB T).rpow_isHermitian _) J
      ((posDef_eval hA T).posSemidef.rpow_intertwine (posDef_eval hB T).posSemidef
        J (eval_intertwine hA hB J hJ T) _)]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

/-- Compression of the recursive derivative on an arbitrary ambient direction.
Auxiliary to OpenAI's area-law manuscript, Lemma 7.2,
06-transport.tex, lines 144–172, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem derivLabel_compress
    {A : ι → Matrix n n ℂ} {B : ι → Matrix m m ℂ}
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (J : Matrix n m ℂ) (hJ : ∀ i, A i * J = J * B i)
    (T : MeanTree ι) (j : ι) (X : Matrix n n ℂ) :
    Jᴴ * T.derivLabel A j X * J = T.derivLabel B j (Jᴴ * X * J) := by
  have hstar (i : ι) : B i * Jᴴ = Jᴴ * A i :=
    (hA i).isHermitian.conjTranspose_intertwine (hB i).isHermitian J (hJ i)
  simpa only [conjTranspose_conjTranspose] using
    (derivLabel_intertwine hB hA Jᴴ hstar T j X).symm

/-- Compression of the normalized leaf map on an arbitrary ambient direction,
including labels of zero terminal weight. Auxiliary to OpenAI's area-law
manuscript, Lemma 7.2, 06-transport.tex, lines 144–172, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem leafMap_compress
    {A : ι → Matrix n n ℂ} {B : ι → Matrix m m ℂ}
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (J : Matrix n m ℂ) (hJ : ∀ i, A i * J = J * B i)
    (T : MeanTree ι) (j : ι) (X : Matrix n n ℂ) :
    Jᴴ * T.leafMap A j X * J = T.leafMap B j (Jᴴ * X * J) := by
  have hstar (i : ι) : B i * Jᴴ = Jᴴ * A i :=
    (hA i).isHermitian.conjTranspose_intertwine (hB i).isHermitian J (hJ i)
  simpa only [conjTranspose_conjTranspose] using
    (leafMap_intertwine hB hA Jᴴ hstar T j X).symm

end Matrix.MeanTree
