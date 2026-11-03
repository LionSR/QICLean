/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceTrimmingInvariance
import QICLean.Analysis.SpectralProjectionMeasurable

/-!
# Borel measurability of collective trimming projections

For fixed cuts, threshold and number of steps, the literal collective
trimming products and individual cut projections are Borel functions of
the input family. The family need not be orthonormal or independent.
Zero vectors and arbitrary real thresholds are included.

Source: ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655.
This proves measurability of the projections, not an adaptive sampling law.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

omit [Fintype V] [DecidableEq V] in
/-- The original Gram operator is continuous in all vectors of the
family. Used for ALVV collective trimming, arXiv:1602.08828v2,
Definition `def:trimming`, lines 648–655. -/
theorem continuous_leftMarginal_stackVector (s : ℕ) :
    Continuous (fun u : Fin s → EuclideanSpace ℂ (SiteConfig n) ↦
      leftMarginal (stackVector u)) := by
  simp_rw [leftMarginal_stackVector]
  unfold vecMulVec
  fun_prop

private theorem continuous_regionalPartialTrace (D : Finset V) :
    Continuous (fun A : Matrix (SiteConfig n) (SiteConfig n) ℂ ↦
      partialTraceRight (cutOperator D A)) := by
  apply continuous_matrix
  intro x y
  change Continuous (fun A : Matrix (SiteConfig n) (SiteConfig n) ℂ ↦
    ∑ z, A ((cutEquiv n D).symm (x, z)) ((cutEquiv n D).symm (y, z)))
  fun_prop

private theorem continuous_localLift (D : Finset V) :
    Continuous (localLift D : Matrix (RegionConfig n D) (RegionConfig n D) ℂ →
      Matrix (SiteConfig n) (SiteConfig n) ℂ) := by
  unfold localLift Matrix.kroneckerMap
  fun_prop

private theorem measurable_trimStep_of_measurable_trimProj {s : ℕ}
    (D : ℕ → Finset V) (xi : ℝ) (j : ℕ)
    (hP : Measurable (fun u : Fin s → EuclideanSpace ℂ (SiteConfig n) ↦
      trimProj D xi u j)) :
    Measurable (fun u : Fin s → EuclideanSpace ℂ (SiteConfig n) ↦ trimStep D xi u j) := by
  have hconj : Measurable (fun u : Fin s → EuclideanSpace ℂ (SiteConfig n) ↦
      (trimProj D xi u j)ᴴ) :=
    (show Continuous (fun A : Matrix (SiteConfig n) (SiteConfig n) ℂ ↦ Aᴴ) from
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
    Measurable (fun u : Fin s → EuclideanSpace ℂ (SiteConfig n) ↦ trimProj D xi u k) := by
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
    Measurable (fun u : Fin s → EuclideanSpace ℂ (SiteConfig n) ↦ trimStep D xi u k) := by
  exact measurable_trimStep_of_measurable_trimProj D xi k (measurable_trimProj D xi k)

end Entropy
