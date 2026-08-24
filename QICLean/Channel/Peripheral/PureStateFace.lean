/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Normed.Module.Connected
import QICLean.Analysis.TraceNormContractionCoefficient

/-!
# Connected rank-one pure-state faces

This file supplies the topology used literally in Wolf's proof of Theorem 6.16,
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1648--1654.  Inside one
full matrix block, pure states are rank-one projections.  Their unit-vector
parametrization is path connected over `ℂ`, and its image under the continuous
map `Matrix.pureStateProj` is therefore connected.

The results here do not choose a target block, assume a block permutation, or
compare block dimensions.  Those are conclusions for the later face-permutation
argument, not hypotheses of these reusable helpers.

## Main declarations

* `Matrix.isPathConnected_unitVectors`
* `Matrix.isConnected_pureStateProj_image`

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.16][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix

noncomputable section

namespace Matrix

variable {D : ℕ}

private theorem isUnitVector_euclideanEquiv_iff
    (φ : EuclideanSpace ℂ (Fin D)) :
    IsUnitVector (EuclideanSpace.equiv (Fin D) ℂ φ) ↔ ‖φ‖ = 1 := by
  rw [IsUnitVector, dotProduct_comm]
  change WithLp.ofLp φ ⬝ᵥ star (WithLp.ofLp φ) = 1 ↔ ‖φ‖ = 1
  rw [← EuclideanSpace.inner_eq_star_dotProduct]
  rw [inner_self_eq_norm_sq_to_K]
  constructor
  · intro h
    have hsq : ‖φ‖ ^ 2 = 1 := by
      rw [← Complex.ofReal_inj]
      rw [Complex.ofReal_pow, Complex.ofReal_one]
      exact h
    nlinarith [norm_nonneg φ]
  · intro h
    norm_num [h]

private theorem one_lt_rank_euclideanSpace (hD : 0 < D) :
    1 < Module.rank ℝ (EuclideanSpace ℂ (Fin D)) := by
  rw [rank_real_of_complex]
  rw [← Module.finrank_eq_rank]
  rw [finrank_euclideanSpace_fin]
  have hnat : 1 < 2 * D := by omega
  exact_mod_cast hnat

/-- The complex unit vectors in a nonzero full matrix block form a path-connected set.

The ambient function space carries the product topology used by the matrix API.  We
transport Mathlib's path-connectedness theorem for the Euclidean unit sphere along
`EuclideanSpace.equiv`; the defining dot-product equation for `IsUnitVector` is exactly
the Euclidean norm-one equation. -/
theorem isPathConnected_unitVectors (hD : 0 < D) :
    IsPathConnected {ψ : Fin D → ℂ | IsUnitVector ψ} := by
  let e := EuclideanSpace.equiv (Fin D) ℂ
  have hpath : IsPathConnected
      (Metric.sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :=
    isPathConnected_sphere (one_lt_rank_euclideanSpace hD) 0 (by positivity)
  have himage : IsPathConnected
      (e '' Metric.sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :=
    hpath.image e.continuous
  have hset : e '' Metric.sphere (0 : EuclideanSpace ℂ (Fin D)) 1 =
      {ψ : Fin D → ℂ | IsUnitVector ψ} := by
    ext ψ
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      change IsUnitVector (e φ)
      apply (isUnitVector_euclideanEquiv_iff φ).2
      simpa only [Metric.mem_sphere, dist_zero_right] using hφ
    · intro hψ
      change IsUnitVector ψ at hψ
      refine ⟨e.symm ψ, ?_, e.apply_symm_apply ψ⟩
      rw [Metric.mem_sphere, dist_zero_right]
      apply (isUnitVector_euclideanEquiv_iff (e.symm ψ)).1
      have heq : (EuclideanSpace.equiv (Fin D) ℂ) (e.symm ψ) = ψ :=
        e.apply_symm_apply ψ
      rw [heq]
      exact hψ
  rw [← hset]
  exact himage

/-- The rank-one pure-state projections in a nonzero full matrix block form a connected set.

This is the precise source-facing bridge used in Wolf's continuity step: it is the image
of the connected unit-vector set under the existing continuous map `pureStateProj`. -/
theorem isConnected_pureStateProj_image (hD : 0 < D) :
    IsConnected (pureStateProj (D := D) ''
      {ψ : Fin D → ℂ | IsUnitVector ψ}) :=
  ((isPathConnected_unitVectors hD).image continuous_pureStateProj).isConnected

end Matrix
