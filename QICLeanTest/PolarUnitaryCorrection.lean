/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PolarUnitaryCorrection

/-! Consumers of same-space polar correction, including singular and empty cases. -/

open scoped Matrix MatrixOrder ComplexOrder
open Matrix

-- The selected unitary works simultaneously for every pair of vectors and
-- every pair of residual bounds, as needed for amplification.
example {n : Type*} [Fintype n] [DecidableEq n] (D : Matrix n n ℂ) :
    ∃ U : unitaryGroup n ℂ, ∀ (x y : EuclideanSpace ℂ n) (ε δ : ℝ),
      ‖toEuclideanCLM (n := n) (𝕜 := ℂ) D x - y‖ ≤ ε →
      ‖toEuclideanCLM (n := n) (𝕜 := ℂ) Dᴴ y - x‖ ≤ δ →
      ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (U : Matrix n n ℂ) x - y‖ ≤ ε + δ := by
  obtain ⟨U, _, _, hU⟩ := exists_unitary_polar_correction D
  exact ⟨U, fun x y ε δ hε hδ ↦ (hU x y).trans (add_le_add hε hδ)⟩

-- The zero operator has a same-space unitary correction; no invertibility
-- or injectivity premise is introduced by a downstream use.
example : ∃ U : unitaryGroup (Fin 3) ℂ,
    ∀ x : EuclideanSpace ℂ (Fin 3),
      ‖toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) ((U : Matrix (Fin 3) (Fin 3) ℂ) - 0) x‖ ≤
        ‖toEuclideanCLM (n := Fin 3) (𝕜 := ℂ) (1 - (0 : Matrix (Fin 3) (Fin 3) ℂ)ᴴ * 0) x‖ := by
  obtain ⟨U, _, hU, _⟩ := exists_unitary_polar_correction (0 : Matrix (Fin 3) (Fin 3) ℂ)
  exact ⟨U, hU⟩

-- A genuinely singular, nonzero matrix uses the very same theorem.
example : ∃ U : unitaryGroup (Fin 2) ℂ,
    ∀ x y : EuclideanSpace ℂ (Fin 2),
      ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (U : Matrix (Fin 2) (Fin 2) ℂ) x - y‖ ≤
        ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) x - y‖ +
          ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
            ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) y - x‖ := by
  obtain ⟨U, _, _, hU⟩ :=
    exists_unitary_polar_correction (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
  exact ⟨U, hU⟩

-- Empty ambient spaces are included without a positive-dimension assumption.
example (D : Matrix (Fin 0) (Fin 0) ℂ) :
    ∃ U : unitaryGroup (Fin 0) ℂ,
      D = (U : Matrix (Fin 0) (Fin 0) ℂ) * CFC.sqrt (Dᴴ * D) := by
  obtain ⟨U, hU, _, _⟩ := exists_unitary_polar_correction D
  exact ⟨U, hU⟩
