/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

/-!
# Two-outcome projective measurements and their transport

An orthogonal projector `D` and its complement `1 - D` form a complete positive projection
family. If `T` is a scaled partial isometry, `T† T = c P` with `c > 0` and `T P = T`, and `D` is a
Hermitian idempotent commuting with `P`, then `c⁻¹ T D T†` is an orthogonal projector on the
target space with `(c⁻¹ T D T†) T = T D`; together with its complement it gives a complete
two-outcome measurement on the whole target space whose outcomes act on `T` through `D` and
`1 - D`. These finite-dimensional identities are used for the interference measurements of
Schuch, Cirac, and Pérez-García, arXiv:1001.3807, lines 2464–2486 and 2582–2615.

Moved from TNLean, `TNLean/Algebra/BinaryProjectionFamily.lean` and
`TNLean/Algebra/ScaledProjectionTransport.lean` at commit `49b78ed821` (Apache-2.0).
Changes: the two modules are merged.

## Main results

* `Matrix.binaryProjectionFamily_complete`
* `Matrix.scaledProjectionTransport_properties`
* `Matrix.exists_binaryProjectionFamily_transport`
-/

open scoped BigOperators Matrix ComplexOrder
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An orthogonal projector and its complement are a complete positive binary
measurement. Source: SCP10, the interference measurement, lines 2605–2615;
auxiliary finite-dimensional identity. -/
theorem binaryProjectionFamily_complete (D : Matrix ι ι ℂ)
    (hDh : D.IsHermitian) (hDI : D * D = D) :
    let Q : Bool → Matrix ι ι ℂ := fun b => if b then D else 1 - D
    (∀ b, (Q b).IsHermitian ∧ (Q b).PosSemidef) ∧
    (∀ b c, Q b * Q c = if b = c then Q b else 0) ∧
    (∑ b, Q b) = 1 := by
  let Q : Bool → Matrix ι ι ℂ := fun b => if b then D else 1 - D
  have hCh : (1 - D).IsHermitian := Matrix.isHermitian_one.sub hDh
  have hCI : (1 - D) * (1 - D) = 1 - D := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      hDI, sub_self, sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro b
    cases b
    · change (1 - D).IsHermitian ∧ (1 - D).PosSemidef
      refine ⟨hCh, ?_⟩
      have hp := Matrix.posSemidef_self_mul_conjTranspose (1 - D)
      rw [hCh.eq, hCI] at hp
      exact hp
    · change D.IsHermitian ∧ D.PosSemidef
      refine ⟨hDh, ?_⟩
      have hp := Matrix.posSemidef_self_mul_conjTranspose D
      rw [hDh.eq, hDI] at hp
      exact hp
  · intro b c
    cases b <;> cases c <;>
      simp [Matrix.sub_mul, Matrix.mul_sub, hDI]
  · simp

end Matrix

noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace Matrix
variable {H K : Type*} [Fintype H] [Fintype K]

/-- Transport a projection through a scaled partial isometry: `c⁻¹ T D T†`.
Source: SCP10, lines 2582–2615. -/
def scaledProjectionTransport (T : Matrix H K ℂ) (D : Matrix K K ℂ) (c : ℝ) :
    Matrix H H ℂ :=
  (c : ℂ)⁻¹ • (T * D * T.conjTranspose)

/-- The transported projection is positive and intertwines the original map.
Source: SCP10, lines 2582–2615; auxiliary scaled-isometry identity. -/
theorem scaledProjectionTransport_properties
    (T : Matrix H K ℂ) (P D : Matrix K K ℂ) (c : ℝ) (hc : 0 < c)
    (hGram : T.conjTranspose * T = (c : ℂ) • P)
    (hTP : T * P = T) (hcomm : D * P = P * D)
    (hDh : D.IsHermitian) (hDI : D * D = D) :
    (scaledProjectionTransport T D c).IsHermitian ∧
      (scaledProjectionTransport T D c).PosSemidef ∧
      scaledProjectionTransport T D c * scaledProjectionTransport T D c =
        scaledProjectionTransport T D c ∧
      scaledProjectionTransport T D c * T = T * D := by
  let Q := scaledProjectionTransport T D c
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hQT : Q * T = T * D := by
    change (c : ℂ)⁻¹ • (T * D * T.conjTranspose) * T = _
    rw [Matrix.smul_mul, Matrix.mul_assoc, hGram, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ hc', one_smul, Matrix.mul_assoc, hcomm,
      ← Matrix.mul_assoc, hTP]
  have hQh : Q.IsHermitian :=
    (Matrix.isHermitian_mul_mul_conjTranspose T hDh).smul (by simp [IsSelfAdjoint])
  have hQI : Q * Q = Q := by
    change Q * ((c : ℂ)⁻¹ • (T * D * T.conjTranspose)) = Q
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQT,
      Matrix.mul_assoc T D D, hDI]
    rfl
  refine ⟨hQh, ?_, hQI, hQT⟩
  simpa only [hQh.eq, hQI] using Matrix.posSemidef_self_mul_conjTranspose Q

/-- The target space of a scaled partial isometry `T` carries a complete two-outcome projective
measurement whose outcomes act on `T` by the projections `D` and `1 - D`.
Source: SCP10, lines 2605–2615. -/
theorem exists_binaryProjectionFamily_transport [DecidableEq H] [DecidableEq K]
    (T : Matrix H K ℂ) (P D : Matrix K K ℂ) (c : ℝ) (hc : 0 < c)
    (hGram : T.conjTranspose * T = (c : ℂ) • P)
    (hTP : T * P = T) (hcomm : D * P = P * D)
    (hDh : D.IsHermitian) (hDI : D * D = D) :
    ∃ Q : Bool → Matrix H H ℂ,
      (∀ b, (Q b).IsHermitian ∧ (Q b).PosSemidef) ∧
      (∀ b r, Q b * Q r = if b = r then Q b else 0) ∧
      (∑ b, Q b) = 1 ∧
      Q true = scaledProjectionTransport T D c ∧
      Q true * T = T * D ∧ Q false * T = T * (1 - D) := by
  obtain ⟨hQh, _, hQI, hQT⟩ :=
    scaledProjectionTransport_properties T P D c hc hGram hTP hcomm hDh hDI
  let Q : Bool → Matrix H H ℂ :=
    fun b => if b then scaledProjectionTransport T D c else
      1 - scaledProjectionTransport T D c
  obtain ⟨hh, hi, hs⟩ := binaryProjectionFamily_complete
    (scaledProjectionTransport T D c) hQh hQI
  refine ⟨Q, hh, hi, hs, rfl, hQT, ?_⟩
  change (1 - scaledProjectionTransport T D c) * T = T * (1 - D)
  rw [Matrix.sub_mul, Matrix.one_mul, hQT, Matrix.mul_sub, Matrix.mul_one]

end Matrix
