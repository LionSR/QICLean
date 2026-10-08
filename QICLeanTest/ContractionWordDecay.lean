/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionWordDecay

/-! Regressions for empty alphabets, one label, and noncommuting chronological factors. -/

open Matrix
open scoped InnerProductSpace MatrixOrder ComplexOrder

namespace ContractionWordDecayTest

section Abstract

variable {n : Type*} [Fintype n] [DecidableEq n]

example {ι : Type*} [Fintype ι] (k : ι → Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    contractionWordSum k 0 v = ‖v‖ ^ 2 := contractionWordSum_zero k v

example (k : Fin 0 → Matrix n n ℂ) (v : EuclideanSpace ℂ n) (m : ℕ) :
    contractionWordSum k (m + 1) v = 0 := by
  classical
  simp [contractionWordSum]

example (k : Matrix n n ℂ) (m : ℕ) (w : Fin m → Unit) :
    contractionWord (fun _ : Unit => k) m w = CFC.sqrt (1 - k) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => simp [contractionWord, ih, pow_succ']

example (k : Matrix n n ℂ) (v : EuclideanSpace ℂ n) (m : ℕ) :
    contractionWordSum (fun _ : Unit => k) (m + 1) v =
      ‖toEuclideanLin (CFC.sqrt (1 - k))
        (toEuclideanLin (contractionWord (fun _ : Unit => k) m (fun _ => ())) v)‖ ^ 2 := by
  simp [contractionWordSum_succ]

example {ι : Type*} [Fintype ι] (k : ι → Matrix n n ℂ) (hk : ∀ i, k i ≤ 1)
    {Ω v : EuclideanSpace ℂ n} {g : ℝ}
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (hv : ⟪Ω, v⟫_ℂ = 0) (hg : (Fintype.card ι : ℝ) < g) :
    ∀ m, contractionWordSum k m v = 0 := by
  rw [eq_zero_of_card_lt_gap k hk hgap hv hg]
  intro m
  simp [contractionWordSum]

end Abstract

/-- Two noncommuting projections on the two-dimensional excited sector. -/
private def k₀ : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 1, 0; 0, 0, 0]

private noncomputable def k₁ : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2]

private theorem noncommuting : k₀ * k₁ ≠ k₁ * k₀ := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 1 2) h
  norm_num [k₀, k₁, Matrix.mul_apply, Fin.sum_univ_succ] at he

-- The latest factor is on the left even when reversing the factors changes the matrix.
example : k₀ * k₁ ≠ k₁ * k₀ ∧
    contractionWord ![k₀, k₁] 2 ![0, 1] =
      CFC.sqrt (1 - k₁) * CFC.sqrt (1 - k₀) := by
  refine ⟨noncommuting, ?_⟩
  simp [contractionWord]

private theorem bounds_of_projection {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hstar : Pᴴ = P) (hsq : P * P = P) : 0 ≤ P ∧ P ≤ 1 := by
  have hp : 0 ≤ P := nonneg_iff_posSemidef.mpr (by
    simpa [hstar, hsq] using posSemidef_conjTranspose_mul_self P)
  have he : (1 - P)ᴴ * (1 - P) = 1 - P := by
    simp only [conjTranspose_sub, conjTranspose_one, hstar, sub_mul, mul_sub,
      Matrix.one_mul, Matrix.mul_one, hsq, sub_self, sub_zero]
  have hc := posSemidef_conjTranspose_mul_self (1 - P)
  rw [he] at hc
  exact ⟨hp, sub_nonneg.mp (nonneg_iff_posSemidef.mpr hc)⟩

private theorem k₀_bounds : 0 ≤ k₀ ∧ k₀ ≤ 1 := by
  apply bounds_of_projection
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [k₀, conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [k₀, mul_apply, Fin.sum_univ_succ]

private theorem k₁_bounds : 0 ≤ k₁ ∧ k₁ ≤ 1 := by
  apply bounds_of_projection
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [k₁, conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [k₁, mul_apply, Fin.sum_univ_succ]

private def Ω : EuclideanSpace ℂ (Fin 3) := WithLp.toLp 2 ![1, 0, 0]

private theorem norm_ground : ‖Ω‖ = 1 := by
  have hs : ‖Ω‖ ^ 2 = 1 := by
    simp [EuclideanSpace.norm_sq_eq, Ω, Fin.sum_univ_succ]
  nlinarith [norm_nonneg Ω]

private theorem ground (i : Fin 2) : toEuclideanLin (![k₀, k₁] i) Ω = 0 := by
  apply WithLp.ofLp_injective
  fin_cases i <;> ext j <;> fin_cases j <;>
    norm_num [toLpLin_apply, Ω, k₀, k₁, mulVec, dotProduct, Fin.sum_univ_succ]

private noncomputable def R : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, 0, 0; 0, 1, 1 / 2; 0, 1 / 2, 0]

private theorem gap : ((1 / 4 : ℝ) : ℂ) •
    (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
      ∑ i : Fin 2, ![k₀, k₁] i := by
  apply sub_nonneg.mp
  have he : (∑ i : Fin 2, ![k₀, k₁] i) - ((1 / 4 : ℝ) : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) = Rᴴ * R := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Ω, R, k₀, k₁, mul_apply, Fin.sum_univ_succ, conjTranspose_apply,
        vecMulVec, Matrix.one_apply, map_ofNat]
  rw [he]
  exact nonneg_iff_posSemidef.mpr (posSemidef_conjTranspose_mul_self R)

-- A concrete positive-gap application uses actual noncommuting positive contractions.
example (v : EuclideanSpace ℂ (Fin 3)) (hv : ⟪Ω, v⟫_ℂ = 0) (m : ℕ) :
    ‖Ω‖ = 1 ∧ contractionWordSum ![k₀, k₁] m v ≤ (7 / 4 : ℝ) ^ m * ‖v‖ ^ 2 := by
  refine ⟨norm_ground, ?_⟩
  have hk : ∀ i : Fin 2, ![k₀, k₁] i ≤ 1 := by
    intro i
    fin_cases i
    · exact k₀_bounds.2
    · exact k₁_bounds.2
  have h := contractionWordSum_le_pow ![k₀, k₁] hk ground gap (by norm_num) hv m
  norm_num at h ⊢
  exact h

end ContractionWordDecayTest
