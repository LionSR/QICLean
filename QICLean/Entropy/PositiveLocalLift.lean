/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.SupportedMarginalTails
import QICLean.Entropy.FilterMoment
import QICLean.ManyBody.Sites.RegionState
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
theorem _root_.ManyBody.IsSupportedOn.exists_posSemidef_localLift_norm_le
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {D : Finset V}
    {X : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ} (hs : ManyBody.IsSupportedOn X D)
    (hX : X.PosSemidef) (M : ℝ) (hbound : ‖X‖ ≤ M) :
    ∃ K : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ,
      K.PosSemidef ∧ ‖K‖ ≤ M ∧ X = ManyBody.place D K := by
  classical
  have hM : 0 ≤ M := (norm_nonneg X).trans hbound
  by_cases hc : Nonempty (∀ v, Fin (n v))
  · let σ0 := Classical.choice hc
    let y0 := ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) D) σ0).2
    let g : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) → (∀ v, Fin (n v)) := fun x ↦
        (ManyBody.cutEquiv (fun v ↦ Fin (n v)) D).symm (x, y0)
    have hginj : Function.Injective g := by
      intro x y heq
      exact congrArg Prod.fst ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) D).symm.injective heq)
    let K := X.submatrix g g
    have hK : K.PosSemidef := hX.submatrix g
    have hcap : X ≤ M • 1 := by
      have hh := (CStarAlgebra.norm_le_iff_le_algebraMap X hM hX.nonneg).mp hbound
      simpa only [Algebra.algebraMap_eq_smul_one] using hh
    have hdiff := (le_iff.mp hcap).submatrix g
    change (M • (1 : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ).submatrix g g - K).PosSemidef
      at hdiff
    rw [submatrix_one g hginj] at hdiff
    have hKnorm : ‖K‖ ≤ M :=
      (CStarAlgebra.norm_le_iff_le_algebraMap K hM hK.nonneg).mpr
        (by simpa only [Algebra.algebraMap_eq_smul_one] using (le_iff.mpr hdiff))
    refine ⟨K, hK, hKnorm, ?_⟩
    obtain ⟨K', hXK'⟩ := ManyBody.exists_eq_place_of_mem_supportedOperators hs
    have hKK' : K = K' := by
      ext x y
      change ManyBody.cutOperator D X (x, y0) (y, y0) = K' x y
      rw [hXK', ManyBody.cutOperator_place]
      simp
    rw [hKK']
    exact hXK'
  · have : IsEmpty (∀ v, Fin (n v)) := not_nonempty_iff.mp hc
    refine ⟨0, PosSemidef.zero, ?_, ?_⟩
    · simpa only [norm_zero] using hM
    · exact Subsingleton.elim _ _

end Entropy
