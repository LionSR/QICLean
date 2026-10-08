/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionChain

/-! Boundary cases for contraction chains: empty spaces, changing dimensions,
marked occurrences with exact private stages, and zero approximation error. -/

open scoped Matrix Matrix.Norms.L2Operator

-- Identity operators on zero-dimensional memory do not require a nontrivial space.
example : ‖(1 : Matrix (Fin 0) (Fin 0) ℂ)‖ ≤ 1 := Matrix.l2_opNorm_one_le

-- The initial memory need not have the dimension of any later memory.
example : Matrix.contractionPrefix
    (D := fun t => Fin (t + 1)) (fun _ => 0) 0 = 1 := rfl

-- A single approximation is charged once, regardless of intervening exact stages.
example (G H : (t : ℕ) → Matrix (Fin (t + 2)) (Fin (t + 1)) ℂ)
    (hG : ∀ t, ‖G t‖ ≤ 1) (hH : ∀ t, ‖H t‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (he : ‖G 1 - H 1‖ ≤ δ)
    (hexact : ∀ t, t ≠ 1 → G t = H t) (n : ℕ) :
    ‖Matrix.contractionPrefix (D := fun t => Fin (t + 1)) G n -
      Matrix.contractionPrefix (D := fun t => Fin (t + 1)) H n‖ ≤ δ := by
  have h := Matrix.contractionPrefix_sub_norm_le_supported
    (D := fun t => Fin (t + 1)) G H hG hH {1} δ hδ
    (by
      intro t ht
      have ht' : t = 1 := Finset.mem_singleton.mp ht
      subst t
      exact he)
    (by intro t ht; exact hexact t (by simpa using ht)) n
  simpa using h

-- Exact zero-tolerance approximations remain contractions, including zero maps.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E) (hG : ‖G‖ ≤ 1) :
    ‖((1 + (0 : ℝ))⁻¹ : ℝ) • G‖ ≤ 1 ∧
      ‖((1 + (0 : ℝ))⁻¹ : ℝ) • G - G‖ ≤ 0 := by
  simpa using NormedSpace.rescale_approximation G G 0 (le_refl 0) hG (by simp)
