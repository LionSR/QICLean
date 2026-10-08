/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RestoringVectors

/-! Consumers for the actual vector identities, singular selections, and spectator order. -/

open Matrix Entropy
open scoped BigOperators Kronecker

/-- The copied physical `X` index comes from `e`, including the remote `Z` index. -/
example (Ω : EuclideanSpace ℂ ((Bool × Bool) × Bool)) :
    restoringCopy (fun _ ↦ 1) (fun _ ↦ Complex.I) Ω
      (((false, true), (false, true)), false) =
        Complex.I * Ω ((true, true), false) := by
  simp [restoringCopy]

/-- Physical lifting separates the ancillas without losing the remote coordinate. -/
example : restoringPhysicalGrouping (X := Bool) (Y := Bool) (Z := Bool)
    (((true, false), (false, true)), true) =
      ((true, false), ((false, true), true)) := rfl

/-- An unselected zero eigenvalue does not obstruct the actual column identity,
and `Ω` can have arbitrary coefficients at that coordinate. -/
example (Ω : EuclideanSpace ℂ ((Bool × Bool) × Bool))
    (Q : Matrix (Bool × Bool) (Bool × Bool) ℂ) (T : Matrix Bool Bool ℂ) :
    restoringGlobal {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single true Complex.I) (Pi.single false 1) Q T *ᵥ
        (restoringCopy (Pi.single true Complex.I) (Pi.single false 1) Ω).ofLp =
      restoringColumnGlobal {false} (fun x : Bool ↦ if x then 0 else 1)
        (Pi.single true Complex.I) (Pi.single true Complex.I) Q T *ᵥ
          (restoringInitial (Pi.single true Complex.I) (Pi.single true Complex.I) Ω).ofLp := by
  apply restoringGlobal_mulVec_copy
  · simp
  · simp

/-- The adjoint theorem accepts a singular spectrum, arbitrary physical state,
arbitrary physical `L`, and Hermitian matrices without projection or commutation
hypotheses. -/
example (sBlank xBlank : Bool → ℂ)
    {Q : Matrix (Bool × Bool) (Bool × Bool) ℂ} {T : Matrix Bool Bool ℂ}
    (hQ : Q.IsHermitian) (hT : T.IsHermitian)
    (L : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ)
    (Ω : EuclideanSpace ℂ ((Bool × Bool) × Bool)) :
    (restoringGlobal {false} (fun x : Bool ↦ if x then 0 else 1)
      sBlank xBlank Q T)ᴴ *ᵥ
        ((restoringPhysicalLift L)ᴴ *ᵥ
          (restoringRestored (fun x : Bool ↦ if x then 0 else 1) Ω).ofLp) =
      (restoringCopy sBlank xBlank
        (WithLp.toLp 2 ((((restoringSelectedProjection {false} ⊗ₖ T) * Q) ⊗ₖ
          (1 : Matrix Bool Bool ℂ)) *ᵥ (Lᴴ *ᵥ Ω.ofLp)))).ofLp := by
  apply restoringGlobal_adjoint_identity _ _ _ _ _ hQ hT
  simp

/-- Selection is an actual diagonal projection, rather than an assumed action
on a specific vector. -/
example : restoringSelectedProjection {false} true true = (0 : ℂ) := by
  simp [restoringSelectedProjection]

/-- A complex blank phase is preserved by the copy isometry. -/
example : Isometry (restoringCopy (Y := Bool) (Z := Bool)
    (Pi.single true Complex.I) (Pi.single false 1)) := by
  apply restoringCopy_isometry
  · simp
  · simp

/-- A physical vector supported at an unselected zero-probability coordinate
still has a nonzero copied coefficient. This rules out truncating the copy. -/
example :
    restoringCopy (Pi.single false 1) (Pi.single false 1)
      (WithLp.toLp 2 (Pi.single ((true, false), true) 1))
        (((false, true), (false, false)), true) = (1 : ℂ) := by
  simp [restoringCopy]

/-- The column operator retains a full-basis input coordinate even when its
assigned probability is zero; the remote spectator is unchanged. -/
example :
    restoringColumnGlobal {false} (fun x : Bool ↦ if x then 0 else 1)
      (Pi.single false 1) (Pi.single false Complex.I)
      (1 : Matrix (Bool × Fin 1) (Bool × Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)
      (((false, true), (false, 0)), true) (((false, false), (true, 0)), true) =
        -Complex.I := by
  simp [restoringColumnGlobal, columnOperator, restoringWeight, basisColumn,
    vecMulVec_apply, kroneckerMap_apply]

/-- The source's square-root error estimate follows for a singular selection,
without any commutation assumption on the actual projections. -/
example {Q : Matrix (Bool × Bool) (Bool × Bool) ℂ} {T : Matrix Bool Bool ℂ}
    (hQ : IsStarProjection Q) (hT : IsStarProjection T)
    (L : Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ)
    (Ω : EuclideanSpace ℂ ((Bool × Bool) × Bool)) (δ : ℝ)
    (hX : ‖WithLp.toLp 2 (((restoringSelectedProjection {false} ⊗ₖ
      (1 : Matrix Bool Bool ℂ)) ⊗ₖ (1 : Matrix Bool Bool ℂ)) *ᵥ Ω.ofLp) - Ω‖ ≤ Real.sqrt δ)
    (hY : ‖WithLp.toLp 2 ((((1 : Matrix Bool Bool ℂ) ⊗ₖ T) ⊗ₖ
      (1 : Matrix Bool Bool ℂ)) *ᵥ Ω.ofLp) - Ω‖ ≤ Real.sqrt δ)
    (hQΩ : ‖WithLp.toLp 2 ((Q ⊗ₖ (1 : Matrix Bool Bool ℂ)) *ᵥ Ω.ofLp) - Ω‖ ≤ Real.sqrt δ) :
    ‖WithLp.toLp 2 ((restoringGlobal {false} (fun x : Bool ↦ if x then 0 else 1)
        (Pi.single true Complex.I) (Pi.single false 1) Q T)ᴴ *ᵥ
          ((restoringPhysicalLift L)ᴴ *ᵥ
            (restoringRestored (fun x : Bool ↦ if x then 0 else 1) Ω).ofLp)) -
      restoringCopy (Pi.single true Complex.I) (Pi.single false 1) Ω‖ ≤
        3 * Real.sqrt δ + ‖WithLp.toLp 2 (Lᴴ *ᵥ Ω.ofLp) - Ω‖ := by
  apply restoringGlobal_adjoint_error_le _ _ _ _ _ _ _ hQ hT L Ω _ hX hY hQΩ <;> simp
