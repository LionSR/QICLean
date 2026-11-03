/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.LocalLift
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# Positive native matrices for supported positive operators

A positive matrix supported on a region is the identity extension of
an actual positive matrix on that region, with the same upper norm cap.
The proof restricts to a fixed complementary configuration and uses
scalar order bounds. Empty configuration spaces are included.
This is a finite-dimensional auxiliary for regional energy estimates in
ALVV, arXiv:1602.08828v2, Figure `fig:algo1`, lines 1631–1632.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Entropy

/-- A supported positive matrix has an actual native positive matrix
whose norm obeys the given upper cap. No native matrix is supplied.
The claim includes empty configuration spaces. Auxiliary to regional
energy estimation in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1631–1632. -/
theorem IsSupportedOn.exists_posSemidef_localLift_norm_le
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {D : Finset V}
    {X : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hs : IsSupportedOn X D)
    (hX : X.PosSemidef) (M : ℝ) (hbound : ‖X‖ ≤ M) :
    ∃ K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ,
      K.PosSemidef ∧ ‖K‖ ≤ M ∧ X = localLift D K := by
  classical
  have hM : 0 ≤ M := (norm_nonneg X).trans hbound
  by_cases hc : Nonempty (SiteConfig n)
  · let σ0 := Classical.choice hc
    let y0 := ((cutEquiv n D) σ0).2
    let g : RegionConfig n D → SiteConfig n := fun x ↦ (cutEquiv n D).symm (x, y0)
    have hginj : Function.Injective g := by
      intro x y heq
      exact congrArg Prod.fst ((cutEquiv n D).symm.injective heq)
    let K := X.submatrix g g
    have hK : K.PosSemidef := hX.submatrix g
    have hcap : X ≤ M • 1 := by
      have hh := (CStarAlgebra.norm_le_iff_le_algebraMap X hM hX.nonneg).mp hbound
      simpa only [Algebra.algebraMap_eq_smul_one] using hh
    have hdiff := (le_iff.mp hcap).submatrix g
    change (M • (1 : Matrix (SiteConfig n) (SiteConfig n) ℂ).submatrix g g - K).PosSemidef
      at hdiff
    rw [submatrix_one g hginj] at hdiff
    have hKnorm : ‖K‖ ≤ M :=
      (CStarAlgebra.norm_le_iff_le_algebraMap K hM hK.nonneg).mpr
        (by simpa only [Algebra.algebraMap_eq_smul_one] using (le_iff.mpr hdiff))
    refine ⟨K, hK, hKnorm, ?_⟩
    obtain ⟨K', hXK'⟩ := hs.exists_localLift σ0
    have hKK' : K = K' := by
      ext x y
      change cutOperator D X (x, y0) (y, y0) = K' x y
      rw [hXK', cutOperator_localLift]
      simp
    rw [hKK']
    exact hXK'
  · have : IsEmpty (SiteConfig n) := not_nonempty_iff.mp hc
    refine ⟨0, PosSemidef.zero, ?_, ?_⟩
    · simpa only [norm_zero] using hM
    · exact Subsingleton.elim _ _

end Entropy
