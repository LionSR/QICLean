/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Subspace.TrimmingInvariance
import QICLean.Probability.Measurable.SpectralProjectionMeasurable
import QICLean.Probability.Measurable.MatrixFamilySupportMeasurable

/-!
# Borel measurability of collective trimming projections

For fixed cuts, threshold and number of steps, the literal collective
trimming products and individual cut projections are Borel functions of
the input family. The family need not be orthonormal or independent.
Zero vectors and arbitrary real thresholds are included.

Source: ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655.
This proves measurability of the projections, not an adaptive sampling law.

It also contains the following results.

* `Entropy.measurable_projectionMatrix_trimSubspace`: the Borel ambient projection of the actual
  trimmed subspace.
-/

section TrimmingMeasurable

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

omit [Fintype V] [DecidableEq V] in
/-- The original Gram operator is continuous in all vectors of the
family. Used for ALVV collective trimming, arXiv:1602.08828v2,
Definition `def:trimming`, lines 648–655. -/
theorem continuous_leftMarginal_stackVector (s : ℕ) :
    Continuous (fun u : Fin s → EuclideanSpace ℂ (∀ v, Fin (n v)) ↦
      leftMarginal (stackVector u)) := by
  simp_rw [leftMarginal_stackVector]
  unfold vecMulVec
  fun_prop

private theorem continuous_regionalPartialTrace (D : Finset V) :
    Continuous (fun A : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ ↦
      partialTraceRight (ManyBody.cutOperator D A)) := by
  apply continuous_matrix
  intro x y
  change Continuous (fun A : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ ↦
    ∑ z, A ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) D).symm (x, z))
        ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) D).symm (y, z)))
  fun_prop

private theorem continuous_localLift (D : Finset V) :
    Continuous
        (ManyBody.place D : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ →
      Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ) := by
  unfold ManyBody.place Matrix.kroneckerMap
  fun_prop

private theorem measurable_trimStep_of_measurable_trimProj {s : ℕ}
    (D : ℕ → Finset V) (xi : ℝ) (j : ℕ)
    (hP : Measurable (fun u : Fin s → EuclideanSpace ℂ (∀ v, Fin (n v)) ↦
      trimProj D xi u j)) :
    Measurable (fun u : Fin s → EuclideanSpace ℂ (∀ v, Fin (n v)) ↦ trimStep D xi u j) := by
  have hconj : Measurable (fun u : Fin s → EuclideanSpace ℂ (∀ v, Fin (n v)) ↦
      (trimProj D xi u j)ᴴ) :=
    (show Continuous (fun A : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ ↦ Aᴴ) from
      by fun_prop).measurable.comp hP
  unfold trimStep
  simp_rw [leftMarginal_cutEnvVector_leftApply]
  exact (measurable_spectralProjectionGE (xi ^ 2)).comp
    ((continuous_regionalPartialTrace (D j)).measurable.comp
      ((hP.mul (continuous_leftMarginal_stackVector s).measurable).mul hconj))

/-- For every finite family, the literal successive collective-trimming
product is a Borel measurable function of its vectors. No orthonormality,
nonzero-vector or threshold-positivity premise is needed. Source: ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem measurable_trimProj {s : ℕ} (D : ℕ → Finset V) (xi : ℝ) (k : ℕ) :
    Measurable (fun u : Fin s → EuclideanSpace ℂ (∀ v, Fin (n v)) ↦ trimProj D xi u k) := by
  induction k with
  | zero => exact measurable_const
  | succ j ih =>
    simpa only [trimProj_succ, Function.comp_def] using ih.fun_mul
      ((continuous_localLift (D j)).measurable.comp
        (measurable_trimStep_of_measurable_trimProj D xi j ih))

/-- Each actual spectral cut in collective trimming is Borel measurable
in the entire input family. The number of vectors may be zero, and the
threshold and cuts are arbitrary. Source: ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem measurable_trimStep {s : ℕ} (D : ℕ → Finset V) (xi : ℝ) (k : ℕ) :
    Measurable (fun u : Fin s → EuclideanSpace ℂ (∀ v, Fin (n v)) ↦ trimStep D xi u k) := by
  exact measurable_trimStep_of_measurable_trimProj D xi k (measurable_trimProj D xi k)

end Entropy

end TrimmingMeasurable

section TrimmingProjectionMeasurable

/-!
## The Borel ambient projection of the actual trimmed subspace

The retained vectors come from the literal successive trimming product.
Their span is the existing trimmed subspace, and its actual ambient
orthogonal projection is Borel in the entire finite input family.
No orthonormality, rank or nonzero premise is assumed.

Source: ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655.
This is a measurable subspace construction, not an adaptive probability law.
-/

open scoped Matrix.Norms.L2Operator

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- The actual ambient orthogonal projection onto the existing trimmed
subspace is Borel measurable in every finite input family. The projection
is obtained from its actual retained span; no comparison subspace or
basis-choice measurability premise is introduced. Source: ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem measurable_projectionMatrix_trimSubspace {s : ℕ}
    (D : ℕ → Finset V) (xi : ℝ) (k : ℕ) :
    Measurable (fun u : Fin s → EuclideanSpace ℂ (∀ v, Fin (n v)) ↦
      (Matrix.toEuclideanCLM (n := (∀ v, Fin (n v))) (𝕜 := ℂ)).symm
        (trimSubspace D xi u k).starProjection) := by
  have hretained : Measurable (fun u : Fin s → EuclideanSpace ℂ (∀ v, Fin (n v)) ↦
      fun i ↦ Matrix.toEuclideanLin (trimProj D xi u k) (u i)) := by
    apply measurable_pi_iff.mpr
    intro i
    simpa only [Function.comp_def, ← ContinuousLinearMap.coe_coe,
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
      (Matrix.continuous_uncurry_toEuclideanCLM (n := (∀ v, Fin (n v))) (𝕜 := ℂ)).measurable.comp
        ((measurable_trimProj D xi k).prodMk (measurable_pi_apply i))
  simpa only [trimSubspace, Function.comp_def] using
    (Matrix.measurable_projectionMatrix_span_range (ι := Fin s)
        (m := (∀ v, Fin (n v)))).comp hretained

end Entropy

end TrimmingProjectionMeasurable
