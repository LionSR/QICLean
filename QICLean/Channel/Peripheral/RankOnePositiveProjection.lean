/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.SpectralRadius
import QICLean.Channel.Schwarz.TwoPositive
import QICLean.Algebra.HermitianHelpers
import QICLean.Algebra.MatrixTracePairing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Rank-one positive projections

A positive linear projection of one-dimensional range has a positive output
matrix and a positive trace functional. Their normalization follows from
idempotence. The proof chooses the output matrix as the image of the identity,
so positivity does not have to be recovered from an arbitrary generator of the
range.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace IsPositiveMap

/-- A rank-one positive idempotent map on a nonzero finite matrix algebra has
a positive trace factorization. The output matrix is `T 1`, while the positive
input matrix is its trace-adjoint counterpart divided by `tr(T 1)`.

This is the rank-one projection decomposition used in
finite-dimensional transfer-map arguments. -/
theorem exists_posSemidef_trace_factors_of_finrank_range_eq_one_of_idempotent
    {D : ℕ} [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsPositiveMap T)
    (hrank : Module.finrank ℂ (LinearMap.range T) = 1)
    (hidem : T.comp T = T) :
    ∃ L R : Matrix (Fin D) (Fin D) ℂ,
      L.PosSemidef ∧ R.PosSemidef ∧
      Matrix.trace (L * R) = 1 ∧
      ∀ X, T X = Matrix.trace (L * X) • R := by
  let R := T 1
  have hRne : R ≠ 0 := by
    intro hRzero
    have hTzero : T = 0 := by
      apply LinearMap.ext
      intro X
      have hb := hT.norm_apply_le_norm_map_one_mul_norm X
      change ‖T X‖ ≤ ‖R‖ * ‖X‖ at hb
      rw [hRzero, norm_zero, zero_mul] at hb
      exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
    rw [hTzero] at hrank
    rw [LinearMap.range_zero, finrank_bot] at hrank
    omega
  have hRpos : R.PosSemidef := hT 1 Matrix.PosSemidef.one
  have htrRpos : 0 < Matrix.trace R := hRpos.trace_pos_of_ne_zero hRne
  have htrRne : Matrix.trace R ≠ 0 := ne_of_gt htrRpos
  let L := (Matrix.trace R)⁻¹ • Matrix.traceAdjointMap T 1
  have hLpos : L.PosSemidef := by
    exact (hT.traceAdjointMap 1 Matrix.PosSemidef.one).smul (inv_nonneg.mpr htrRpos.le)
  have hRfix : T R = R := by
    have h := LinearMap.congr_fun hidem 1
    simpa only [LinearMap.comp_apply] using h
  have hpair (X : Matrix (Fin D) (Fin D) ℂ) :
      Matrix.trace (Matrix.traceAdjointMap T 1 * X) = Matrix.trace (T X) := by
    simpa using Matrix.trace_traceAdjointMap_mul T 1 X
  refine ⟨L, R, hLpos, hRpos, ?_, ?_⟩
  · simp only [L, Matrix.smul_mul, Matrix.trace_smul, hpair R, hRfix,
      smul_eq_mul, inv_mul_cancel₀ htrRne]
  · intro X
    let r : LinearMap.range T := ⟨R, ⟨1, rfl⟩⟩
    have hrne : r ≠ 0 := by
      intro h
      exact hRne (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hrank hrne
      (⟨T X, ⟨X, rfl⟩⟩ : LinearMap.range T)
    have hc' : c • R = T X := congrArg Subtype.val hc
    have hcval : Matrix.trace (L * X) = c := by
      simp only [L, Matrix.smul_mul, Matrix.trace_smul, hpair X, ← hc',
        Matrix.trace_smul, smul_eq_mul]
      rw [mul_comm c (Matrix.trace R), ← mul_assoc, inv_mul_cancel₀ htrRne, one_mul]
    rw [hcval, ← hc']

end IsPositiveMap

namespace IsCPMap

/-- The rank-one positive-projection decomposition for a completely positive
map. Complete positivity enters only through positivity of the map. -/
theorem exists_posSemidef_trace_factors_of_finrank_range_eq_one_of_idempotent
    {D : ℕ} [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsCPMap T)
    (hrank : Module.finrank ℂ (LinearMap.range T) = 1)
    (hidem : T.comp T = T) :
    ∃ L R : Matrix (Fin D) (Fin D) ℂ,
      L.PosSemidef ∧ R.PosSemidef ∧
      Matrix.trace (L * R) = 1 ∧
      ∀ X, T X = Matrix.trace (L * X) • R :=
  IsPositiveMap.exists_posSemidef_trace_factors_of_finrank_range_eq_one_of_idempotent
    T hT.isPositiveMap hrank hidem

end IsCPMap
