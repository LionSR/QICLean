/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PolarUnitaryCorrectionKronecker

/-! One local unitary for every finite spectator and every pair of residual bounds. -/

open scoped Matrix Kronecker MatrixOrder ComplexOrder
open Matrix

-- The existential witness precedes the universal spectator space. Neither
-- the spectator dimension nor a decomposition of the vectors enters the bound.
example {n : Type*} [Fintype n] [DecidableEq n] (D : Matrix n n ℂ) :
    ∃ U : unitaryGroup n ℂ,
      D = (U : Matrix n n ℂ) * CFC.sqrt (Dᴴ * D) ∧
      ∀ (m : Type*) [Fintype m] [DecidableEq m],
        let L := toEuclideanCLM (n := n × m) (𝕜 := ℂ)
        let E := D ⊗ₖ (1 : Matrix m m ℂ)
        ∀ (x y : EuclideanSpace ℂ (n × m)) (ε δ : ℝ),
          ‖L E x - y‖ ≤ ε → ‖L Eᴴ y - x‖ ≤ δ →
          ‖L ((U : Matrix n n ℂ) ⊗ₖ (1 : Matrix m m ℂ)) x - y‖ ≤ ε + δ := by
  obtain ⟨U, hD, _, _⟩ := exists_unitary_polar_correction D
  refine ⟨U, hD, ?_⟩
  intro m _ _
  dsimp only
  intro x y ε δ hε hδ
  exact ((unitary_polar_correction_kronecker_one (m := m) D U hD).2.2.2 x y).trans
    (add_le_add hε hδ)

-- An empty spectator remains admissible for a singular local operator.
example : ∃ U : unitaryGroup (Fin 2) ℂ,
    let V := (U : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 : Matrix (Fin 0) (Fin 0) ℂ)
    V ∈ unitaryGroup (Fin 2 × Fin 0) ℂ := by
  obtain ⟨U, hD, _, _⟩ :=
    exists_unitary_polar_correction (0 : Matrix (Fin 2) (Fin 2) ℂ)
  exact ⟨U, (unitary_polar_correction_kronecker_one (m := Fin 0) 0 U hD).1⟩
