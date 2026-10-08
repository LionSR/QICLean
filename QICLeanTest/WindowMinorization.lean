/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.WindowMinorization

/-!
# Rectangular singular-reference window regression

Alternating two- and three-dimensional matrix spaces carry different rank-one reset
references. A three-site interval has a one-site remainder and different endpoint
dimensions; a four-site cycle derives its compatible references without a supplied family.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace RectangularWindowRegression

def dim (i : ℕ) : ℕ := if i % 2 = 0 then 2 else 3

def ρ (i : ℕ) : Matrix (Fin (dim i)) (Fin (dim i)) ℂ :=
  Matrix.diagonal (fun j => if j.val = (if i % 2 = 0 then 0 else 1) then 1 else 0)

theorem density_pos (i : ℕ) : (ρ i).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  dsimp
  split_ifs <;> positivity

theorem density_trace (i : ℕ) : (ρ i).trace = 1 := by
  rw [ρ, Matrix.trace_diagonal]
  let z : Fin (dim i) := ⟨if i % 2 = 0 then 0 else 1, by
    by_cases hi : i % 2 = 0 <;> simp [dim, hi]⟩
  rw [Finset.sum_eq_single z]
  · simp [z]
  · intro j _ hj
    have hjv : j.val ≠ (if i % 2 = 0 then 0 else 1) := fun h => hj (Fin.ext h)
    simp [hjv]
  · simp

noncomputable def site (i : ℕ) :
    Matrix (Fin (dim (i + 1))) (Fin (dim (i + 1))) ℂ →ₗ[ℂ]
      Matrix (Fin (dim i)) (Fin (dim i)) ℂ := Matrix.tracePrepareMap (ρ i)

theorem site_cptp (i : ℕ) : IsKrausCPTP (site i) :=
  Matrix.tracePrepareMap_isKrausCPTP _ (density_pos i) (density_trace i)

theorem window_reset (a : ℕ) :
    Matrix.channelInterval site a (a + 2) (Nat.le_add_right a 2) =
      Matrix.tracePrepareMap (α := Fin (dim (a + 2))) (ρ a) := by
  rw [Matrix.channelInterval_succ site (Nat.le_add_right a 1),
    Matrix.channelInterval_single]
  ext X : 1
  simp [site, Matrix.tracePrepareMap_apply, density_trace]

theorem window_minorization (a : ℕ) :
    ∃ τ : Matrix (Fin (dim a)) (Fin (dim a)) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix
        (Matrix.channelInterval site a (a + 2) (Nat.le_add_right a 2)) ≥
          ((1 : ℂ) / dim (a + 2)) •
            (τ ⊗ₖ (1 : Matrix (Fin (dim (a + 2))) (Fin (dim (a + 2))) ℂ)) := by
  refine ⟨ρ a, density_pos a, density_trace a, ?_⟩
  rw [window_reset, Matrix.choiMatrix_tracePrepareMap]

example : dim 0 = 2 ∧ dim 1 = 3 ∧ dim 2 = 2 ∧ dim 3 = 3 := by decide

example : ρ 0 = Matrix.diagonal ![1, 0] ∧ ρ 1 = Matrix.diagonal ![0, 1, 0] := by
  constructor <;> apply congrArg Matrix.diagonal <;> ext i <;> fin_cases i <;> rfl

example :
    ‖Matrix.linearMapMatrix (Matrix.channelInterval site 0 3 (by omega) -
      Matrix.tracePrepareMap (α := Fin (dim 3))
        (Matrix.channelInterval site 0 3 (by omega) (ρ 3)))‖ ≤ 0 := by
  have h := Matrix.norm_linearMapMatrix_channelInterval_sub_transport_le_of_window_domination
    site 3 2 (by decide) 1 le_rfl
    (fun i _ => by dsimp [dim]; split_ifs <;> decide)
    (fun i _ => site_cptp i)
    (fun a _ => by simpa only [Complex.ofReal_one] using window_minorization a)
    0 3 (by omega) le_rfl (ρ 3) (density_pos 3) (density_trace 3)
  simpa using h

example : ∃ σ : ∀ a, a ≤ 4 → Matrix (Fin (dim a)) (Fin (dim a)) ℂ,
    (∀ a ha, (σ a ha).PosSemidef ∧ (σ a ha).trace = 1) ∧
    σ 4 le_rfl = Matrix.equivReindexMap (finCongr (by decide : dim 4 = dim 0).symm)
      (σ 0 (by omega)) ∧
    ∀ a b (hab : a ≤ b) (hb : b ≤ 4),
      Matrix.channelInterval site a b hab (σ b hb) = σ a (hab.trans hb) :=
  Matrix.exists_compatible_channelInterval_densities site 4 (by decide) (by decide)
    (fun i _ => site_cptp i)

end RectangularWindowRegression
