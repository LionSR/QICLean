/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceTrimmingMeasurable
import QICLean.Analysis.FiniteSpanProjectionMeasurable

/-!
# The Borel ambient projection of the actual trimmed subspace

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
    Measurable (fun u : Fin s → EuclideanSpace ℂ (SiteConfig n) ↦
      (Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).symm
        (trimSubspace D xi u k).starProjection) := by
  have hretained : Measurable (fun u : Fin s → EuclideanSpace ℂ (SiteConfig n) ↦
      fun i ↦ Matrix.toEuclideanLin (trimProj D xi u k) (u i)) := by
    apply measurable_pi_iff.mpr
    intro i
    simpa only [Function.comp_def, ← ContinuousLinearMap.coe_coe,
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using
      (Matrix.continuous_uncurry_toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).measurable.comp
        ((measurable_trimProj D xi k).prodMk (measurable_pi_apply i))
  simpa only [trimSubspace, Function.comp_def] using
    (Matrix.measurable_projectionMatrix_span_range (ι := Fin s) (m := SiteConfig n)).comp hretained

end Entropy
