/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionWordDecaySpectator

/-! Regressions for entangled inputs, empty spectators, and the large-gap branch. -/

open scoped InnerProductSpace MatrixOrder ComplexOrder Kronecker
open Matrix

private noncomputable def ground : EuclideanSpace ℂ (Fin 3) := PiLp.single 2 0 1

private noncomputable def entangled : EuclideanSpace ℂ (Fin 3 × Fin 2) :=
  PiLp.single 2 (1, 0) 1 + PiLp.single 2 (2, 1) 1

private theorem entangled_norm_sq : ‖entangled‖ ^ 2 = 2 := by
  norm_num [EuclideanSpace.norm_sq_eq, entangled, Fintype.sum_prod_type, Fin.sum_univ_succ]

private theorem entangled_slices (r : Fin 2) :
    ⟪ground, WithLp.toLp 2 (fun i => entangled (i, r))⟫_ℂ = 0 := by
  fin_cases r <;> simp [ground, entangled, EuclideanSpace.inner_single_left]

-- The regression input has two independent spectator slices and cannot be a product.
example : ¬ ∃ (u : Fin 3 → ℂ) (v : Fin 2 → ℂ),
    ∀ p : Fin 3 × Fin 2, entangled p = u p.1 * v p.2 := by
  rintro ⟨u, v, h⟩
  have h10 : u 1 * v 0 = 1 := by simpa [entangled] using (h (1, 0)).symm
  have h21 : u 2 * v 1 = 1 := by simpa [entangled] using (h (2, 1)).symm
  have h11 : u 1 * v 1 = 0 := by simpa [entangled] using (h (1, 1)).symm
  have hu : u 1 ≠ 0 := by intro hz; simp [hz] at h10
  have hv : v 1 ≠ 0 := by intro hz; simp [hz] at h21
  exact (mul_ne_zero hu hv) h11

private noncomputable def deficit : Matrix (Fin 3) (Fin 3) ℂ :=
  1 - vecMulVec (WithLp.ofLp ground) (star (WithLp.ofLp ground))

private theorem deficit_le_one : deficit ≤ 1 := by
  exact sub_le_self _ (posSemidef_vecMulVec_self_star (WithLp.ofLp ground)).nonneg

private theorem deficit_ground : toEuclideanLin deficit ground = 0 := by
  simp only [deficit, map_sub, LinearMap.sub_apply, toLpLin_one, LinearMap.id_apply,
    toEuclideanLin_vecMulVec_star_self_apply, inner_self_eq_norm_sq_to_K]
  simp [ground]

-- A unit-gap, one-label system kills this genuinely entangled excited vector in one event.
example : contractionWordSpectatorSum (fun _ : Unit => deficit) 1 entangled = 0 := by
  have hgap : (1 : ℂ) • (1 - vecMulVec (WithLp.ofLp ground)
      (star (WithLp.ofLp ground))) ≤ ∑ _ : Unit, deficit := by simp [deficit]
  have h := contractionWordSpectatorSum_le_pow (fun _ : Unit => deficit)
    (fun _ => deficit_le_one) (fun _ => deficit_ground) hgap (by simp : (1 : ℝ) ≤
      Fintype.card Unit) entangled_slices 1
  have hn : 0 ≤ contractionWordSpectatorSum (fun _ : Unit => deficit) 1 entangled :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  simpa using le_antisymm (by simpa using h) hn

-- The empty word has its original nonzero energy even on an entangled input.
example : contractionWordSpectatorSum (fun _ : Unit => deficit) 0 entangled = 2 := by
  rw [contractionWordSpectatorSum_zero, entangled_norm_sq]

-- Empty spectators are allowed for every physical system and every word length.
example {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (k : ι → Matrix n n ℂ) (m : ℕ) (ξ : EuclideanSpace ℂ (n × Fin 0)) :
    contractionWordSpectatorSum k m ξ = 0 := by
  have hξ : ξ = 0 := Subsingleton.elim _ _
  rw [hξ, contractionWordSpectatorSum_zero_vector]

-- The large-gap result remains valid with an empty label type and an arbitrary spectator.
example {a : Type*} [Fintype a] [DecidableEq a]
    (Ω : EuclideanSpace ℂ Unit) (hnorm : ‖Ω‖ = 1)
    (hgap : (1 : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
      ∑ i : Fin 0, (Fin.elim0 i : Matrix Unit Unit ℂ))
    (ζ : EuclideanSpace ℂ (Unit × a)) :
    toEuclideanLin ((1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ⊗ₖ
      (1 : Matrix a a ℂ)) ζ = 0 := by
  exact spectator_excitedProjection_eq_zero_of_card_lt_gap (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i) hnorm hgap (by simp) ζ
