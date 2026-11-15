/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.FixedPoint.AbstractAlgebra
import QICLean.Channel.FixedPoint.MaximalSupportBasic
import QICLean.Channel.FixedPoint.MeanErgodicAdjoint
import QICLean.Channel.Schwarz.TwoPositive
import QICLean.Algebra.StarSubalgebraBlockForm

/-!
# The fixed-point algebra from a full-rank fixed point

Wolf Theorem 6.12 assumes that the trace-pairing adjoint of a unital Schwarz map has a
full-rank fixed point, and replaces it by a positive-definite one with the proposition on
positive fixed points. This file carries out that replacement for abstract positive unital
maps and packages the source theorem with its literal hypothesis.

The trace-pairing adjoint `T` of a positive unital map is positive and trace preserving. Its
fixed point of maximal support `ρ₀` is positive semidefinite and its support projection `Q`
satisfies `Q X Q = X` for every fixed point `X`. For a full-rank fixed point this forces `Q`
to be invertible, hence `Q = 1`, so `ρ₀` is positive definite.

## Main results

* `SchwarzMap.exists_posDef_traceAdjoint_fixedPoint_of_isUnit`: a full-rank fixed point of
  the trace adjoint yields a positive-definite one.
* `SchwarzMap.fixedPointsStarSubalgebraOfIsUnit`: Wolf Theorem 6.12, the fixed points of a
  positive unital Schwarz map whose trace adjoint has a full-rank fixed point form a
  star-subalgebra.
* `SchwarzMap.exists_unitary_conj_blockDiagonal_iff_fixedPoint_of_isUnit`: the block form
  of Wolf Equation (1.39) for that fixed-point set, without a zero block.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.12 and Proposition 6.9;
  local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1161--1235
  and 1395--1417.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace SchwarzMap

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **A positive-definite invariant weight from a full-rank one.** If `E` is a positive
unital map and its trace-pairing adjoint has an invertible fixed point, then the trace
adjoint also has a positive-definite fixed point. This is the reduction at the start of the
proof of Wolf Theorem 6.12, which invokes Proposition 6.9; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1161--1235 and 1404--1405. -/
theorem exists_posDef_traceAdjoint_fixedPoint_of_isUnit
    (E : Mat →ₗ[ℂ] Mat) (hEpos : IsPositiveMap E) (hE_one : E 1 = 1)
    {ρ : Mat} (hρ : IsUnit ρ) (hρ_fix : Matrix.traceAdjointMap E ρ = ρ) :
    ∃ σ : Mat, σ.PosDef ∧ Matrix.traceAdjointMap E σ = σ := by
  let T := Matrix.traceAdjointMap E
  have hT : IsPositiveMap T := hEpos.traceAdjointMap
  have hTP : IsTracePreservingMap T := by
    rw [isTracePreservingMap_iff_traceAdjointMap_one]
    simpa only [T, Matrix.traceAdjointMap_traceAdjointMap] using hE_one
  obtain ⟨hρ₀, hfix, hmax⟩ := IsPositiveMap.exists_maximalSupport_fixedPoint hT hTP
  set Q := Kraus.stationaryProj hρ₀ with hQ
  have hQρ : Q * ρ * Q = ρ := hmax ρ hρ_fix
  have hQQ : Q * Q = Q := (Kraus.isOrthogonalProjection_stationaryProj hρ₀).2
  have hQunit : IsUnit Q := by
    have hdet : IsUnit (Q * (ρ * Q)).det := by
      rw [← Matrix.mul_assoc, hQρ]
      exact (Matrix.isUnit_iff_isUnit_det ρ).mp hρ
    rw [Matrix.det_mul] at hdet
    exact (Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_of_mul_isUnit_left hdet)
  have hQone : Q = 1 := by
    obtain ⟨u, hu⟩ := hQunit
    have h := congrArg (fun M ↦ (↑u⁻¹ : Mat) * M) hQQ
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h
    rw [← hu, h]
  exact ⟨_, hρ₀.posDef_of_supportProj_eq_one hQone, hfix⟩

/-- **Wolf Theorem 6.12 (fixed-point algebra).** Let `E` be a positive unital map satisfying
the Schwarz inequality whose trace-pairing adjoint has a full-rank fixed point. Then the fixed
points of `E` form a star-subalgebra. Full rank is stated as invertibility of the matrix.

Wolf uses the term *Schwarz map* for a positive unital map satisfying Equation (5.2); the three
properties are separate hypotheses here. Source: Wolf Theorem 6.12, local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1395--1417. The explicit block
realization from Wolf Equation (1.39) is not asserted here. -/
noncomputable def fixedPointsStarSubalgebraOfIsUnit
    (E : Mat →ₗ[ℂ] Mat) (hEpos : IsPositiveMap E) (hE_one : E 1 = 1)
    (hE : IsSchwarzMap E) {ρ : Mat} (hρ : IsUnit ρ)
    (hρ_fix : Matrix.traceAdjointMap E ρ = ρ) :
    StarSubalgebra ℂ Mat :=
  let h := exists_posDef_traceAdjoint_fixedPoint_of_isUnit E hEpos hE_one hρ hρ_fix
  fixedPointsStarSubalgebra E hEpos hE_one hE h.choose_spec.1 h.choose_spec.2

@[simp] theorem mem_fixedPointsStarSubalgebraOfIsUnit
    (E : Mat →ₗ[ℂ] Mat) (hEpos : IsPositiveMap E) (hE_one : E 1 = 1)
    (hE : IsSchwarzMap E) {ρ : Mat} (hρ : IsUnit ρ)
    (hρ_fix : Matrix.traceAdjointMap E ρ = ρ) (X : Mat) :
    X ∈ fixedPointsStarSubalgebraOfIsUnit E hEpos hE_one hE hρ hρ_fix ↔ E X = X :=
  Iff.rfl

/-- **Wolf Theorem 6.12 (block form).** Under the hypotheses of Wolf Theorem 6.12 the fixed
points of `E` have the form of Wolf Equation (1.39) without the zero block: there is a unitary
`U` such that `E X = X` exactly when `U† X U = ⨁_k 1_{m_k} ⊗ B_k` for some matrices
`B_k ∈ M_{d_k}(ℂ)`. Source: Wolf Theorem 6.12 and Equation (1.39), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1395--1417. -/
theorem exists_unitary_conj_blockDiagonal_iff_fixedPoint_of_isUnit
    (E : Mat →ₗ[ℂ] Mat) (hEpos : IsPositiveMap E) (hE_one : E 1 = 1)
    (hE : IsSchwarzMap E) {ρ : Mat} (hρ : IsUnit ρ)
    (hρ_fix : Matrix.traceAdjointMap E ρ = ρ) :
    ∃ (K : ℕ) (d m : Fin K → ℕ) (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin D)
      (U : Mat), U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        ∀ X : Mat,
          E X = X ↔ ∃ B : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * X * U = Matrix.reindex e e
              (Matrix.blockDiagonal' fun k =>
                (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ B k) :=
  StarSubalgebra.exists_unitary_conj_blockDiagonal_iff
    (fixedPointsStarSubalgebraOfIsUnit E hEpos hE_one hE hρ hρ_fix)

end SchwarzMap
