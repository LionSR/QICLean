/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RestoringGroundComponent

/-! Actual ground projection, singular selection, and unrestricted ancillary rows. -/

open Matrix Entropy
open scoped BigOperators Kronecker

/-- The actual physical rank-one projection retains the remote ground coordinate. -/
example :
    restoringGroundOuterProduct
      (WithLp.toLp 2 (Pi.single ((false, false), true) 1))
        (((false, true), (false, false)), true)
        (((false, true), (false, false)), true) = (1 : ℂ) := by
  simp [restoringGroundOuterProduct, restoringPhysicalLift, restoringPhysicalGrouping,
    kroneckerMap_apply, vecMulVec_apply]

/-- The same projection kills a different remote coordinate. -/
example :
    restoringGroundOuterProduct
      (WithLp.toLp 2 (Pi.single ((false, false), true) 1))
        (((false, true), (false, false)), false)
        (((false, true), (false, false)), true) = (0 : ℂ) := by
  simp [restoringGroundOuterProduct, restoringPhysicalLift, restoringPhysicalGrouping,
    kroneckerMap_apply, vecMulVec_apply]

/-- The copied ancillary row is retained even when it is outside the selected
set and its assigned probability is zero. No marginal or projection assumptions
are needed for this exact coordinate identity. -/
example (Ω : EuclideanSpace ℂ ((Bool × Bool) × Bool))
    (Q : Matrix (Bool × Bool) (Bool × Bool) ℂ) (T : Matrix Bool Bool ℂ)
    (a : Bool × Bool) (z : Bool) :
    restoringGroundComponent {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single true Complex.I) (Pi.single false 1) Q T Ω
        (((false, true), a), z) =
      restoringMarginal (restoringReducedDensity Ω) Q T true false * Ω (a, z) := by
  simpa [restoringWeight] using
    restoringGroundComponent_apply {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single true Complex.I) (Pi.single false 1) (by simp) (by simp) Q T Ω
      false true a z

/-- The exact norm identity sums over both ancillary rows although only one
column is selected and the other probability vanishes. -/
example (Ω : EuclideanSpace ℂ ((Bool × Bool) × Bool)) (hΩ : ‖Ω‖ = 1)
    (Q : Matrix (Bool × Bool) (Bool × Bool) ℂ) (T : Matrix Bool Bool ℂ) :
    ‖restoringGroundComponent {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single true Complex.I) (Pi.single false 1) Q T Ω‖ ^ 2 =
      ∑ y : Bool, ‖restoringMarginal (restoringReducedDensity Ω) Q T y false‖ ^ 2 := by
  simpa using restoringGroundComponent_norm_sq {false}
    (fun x : Bool ↦ if x then 0 else 1) (by simp)
    (Pi.single true Complex.I) (Pi.single false 1) (by simp) (by simp) Q T Ω hΩ

/-- The actual norm bound accepts a singular physical marginal and requires
commutation only between its reduced density and `Q`. -/
example (Ω : EuclideanSpace ℂ ((Bool × Bool) × Bool)) (hΩ : ‖Ω‖ = 1)
    {Q : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hQ : IsStarProjection Q)
    (hρQ : Commute (restoringReducedDensity Ω) Q)
    {T : Matrix Bool Bool ℂ} (hT : IsStarProjection T)
    (hdiag : partialTraceRight (restoringReducedDensity Ω) =
      diagonal (fun x : Bool ↦ if x then 0 else 1)) :
    ‖restoringGroundComponent {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single true Complex.I) (Pi.single false 1) Q T Ω‖ ≤ 1 := by
  exact restoringGroundComponent_norm_le_one {false}
    (fun x : Bool ↦ if x then 0 else 1) (by simp)
    (Pi.single true Complex.I) (Pi.single false 1) (by simp) (by simp)
    Ω hΩ hQ hρQ hT (by
      rw [hdiag]
      congr 1
      funext x
      cases x <;> simp)

/-- The same physical ground component comes from the full column operator
and the initial state, with independent unit complex blank phases. -/
example (Ω : EuclideanSpace ℂ ((Bool × Bool) × Bool))
    (Q : Matrix (Bool × Bool) (Bool × Bool) ℂ) (T : Matrix Bool Bool ℂ) :
    restoringGroundComponent {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single true Complex.I) (Pi.single false 1) Q T Ω =
      WithLp.toLp 2 (restoringGroundOuterProduct Ω *ᵥ
        (restoringColumnGlobal {false} (fun x : Bool ↦ if x then 0 else 1)
          (Pi.single true Complex.I) (Pi.single true Complex.I) Q T *ᵥ
            (restoringInitial (Pi.single true Complex.I) (Pi.single true Complex.I) Ω).ofLp)) := by
  apply restoringGroundComponent_column_eq <;> simp

/-- A non-real off-diagonal ground coefficient distinguishes the source's
row/column order from either its transpose or complex conjugate. -/
example :
    restoringGroundComponent {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single false 1) (Pi.single false 1)
      (1 : Matrix (Bool × Fin 1) (Bool × Fin 1) ℂ)
      (1 : Matrix (Fin 1) (Fin 1) ℂ)
      (WithLp.toLp 2 (fun i : (Bool × Fin 1) × Fin 1 ↦
        if i.1.1 then Complex.I else 1))
      (((false, true), (false, 0)), 0) = Complex.I := by
  rw [restoringGroundComponent_apply _ _ _ _ (by simp) (by simp)]
  simp [restoringWeight, restoringMarginal, restoringReducedDensity,
    partialTraceRight_apply, vecMulVec_apply]
