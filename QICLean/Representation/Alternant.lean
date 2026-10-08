/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.WeylRecursion

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Alternants and the vertical-strip Pieri rule

For exponents `α : Fin q → ℕ` the alternant is `a_α(y) = det [y_i ^ α_j]`. The Weyl character
formula used in the proof of Lemma 6.2 of the area-law paper (*A two-dimensional area law
from a global spectral gap*, `05-replicas.tex`, lines 336–364: "the Weyl denominator cancels
`Δ(s^t)` in the density") writes the character of a multiplicity space as a quotient of two
alternants. This file proves the algebraic facts about alternants that the character formula
needs:

* `a_α = 0` when two exponents coincide;
* the vertical-strip Pieri rule `a_α e_r = ∑_{|S| = r} a_{α + 1_S}`, with
  `e_r(y) = ∑_{|S| = r} ∏_{i ∈ S} y_i` the elementary symmetric polynomial;
* its dimension form `∑_{|S| = r} V(α + 1_S) = binom(q, r) V(α)` for the Vandermonde product
  `V(t) = ∏_{i<j} (t_i - t_j)`, obtained by evaluating the Pieri rule at
  `y = (1, z, …, z^{q-1})` and letting `z → 1`.

The proofs are written from the standard theory; no Lean source was adapted.

## Main declarations

* `Partition.alternant`, `Partition.elemSymm`, `Partition.indic`.
* `Partition.alternant_eq_zero_of_eq` — coinciding exponents.
* `Partition.alternant_mul_elemSymm` — the vertical-strip Pieri rule.
* `Partition.sum_vand_add_indic` — `∑_{|S| = r} V(α + 1_S) = binom(q, r) V(α)`.
* `Partition.sum_weylFormula_add_indic` — the same for the Weyl dimension formula.
-/

open Finset Matrix Polynomial

namespace Partition

variable {q : ℕ} {R : Type*} [CommRing R]

/-- The alternant `a_α(y) = det [y_i ^ α_j]`. -/
def alternant (α : Fin q → ℕ) (y : Fin q → R) : R :=
  (Matrix.of fun i j => y i ^ α j).det

/-- The elementary symmetric polynomial `e_r(y) = ∑_{|S| = r} ∏_{i ∈ S} y_i`. -/
def elemSymm (r : ℕ) (y : Fin q → R) : R :=
  ∑ S ∈ powersetCard r (univ : Finset (Fin q)), ∏ i ∈ S, y i

/-- The indicator vector `1_S` of a set of rows. -/
def indic (S : Finset (Fin q)) : Fin q → ℕ := fun i => if i ∈ S then 1 else 0

theorem indic_injective : Function.Injective (indic : Finset (Fin q) → Fin q → ℕ) := by
  intro S T h
  ext a
  have := congrFun h a
  simp only [indic] at this
  by_cases ha : a ∈ S <;> by_cases hb : a ∈ T <;> simp [ha, hb] at this ⊢

theorem alternant_eq_sum (α : Fin q → ℕ) (y : Fin q → R) :
    alternant α y = ∑ σ : Equiv.Perm (Fin q),
      (Equiv.Perm.sign σ : R) * ∏ i, y (σ i) ^ α i := by
  rw [alternant, det_apply]
  refine sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp

/-- An alternant with two equal exponents vanishes. -/
theorem alternant_eq_zero_of_eq {α : Fin q → ℕ} (y : Fin q → R) {i j : Fin q} (hij : i ≠ j)
    (h : α i = α j) : alternant α y = 0 :=
  det_zero_of_column_eq hij fun a => by simp [h]

/-- Reindexing the elementary symmetric polynomial by a permutation of the rows. -/
theorem elemSymm_eq_perm (r : ℕ) (y : Fin q → R) (σ : Equiv.Perm (Fin q)) :
    elemSymm r y = ∑ S ∈ powersetCard r (univ : Finset (Fin q)), ∏ i ∈ S, y (σ i) := by
  rw [elemSymm]
  refine sum_nbij' (fun S => S.map σ.symm.toEmbedding) (fun S => S.map σ.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [mem_powersetCard, subset_univ, true_and] at hS ⊢
    rw [card_map]; exact hS
  · intro S hS
    simp only [mem_powersetCard, subset_univ, true_and] at hS ⊢
    rw [card_map]; exact hS
  · intro S _
    simp [Finset.map_map]
  · intro S _
    simp [Finset.map_map]
  · intro S _
    rw [prod_map]
    simp

theorem prod_pow_indic (S : Finset (Fin q)) (f : Fin q → R) :
    ∏ i, f i ^ indic S i = ∏ i ∈ S, f i := by
  simp [indic, pow_ite, prod_ite_mem]

/-- **The vertical-strip Pieri rule for alternants**: `a_α e_r = ∑_{|S| = r} a_{α + 1_S}`. -/
theorem alternant_mul_elemSymm (α : Fin q → ℕ) (r : ℕ) (y : Fin q → R) :
    alternant α y * elemSymm r y =
      ∑ S ∈ powersetCard r (univ : Finset (Fin q)), alternant (α + indic S) y := by
  simp only [alternant_eq_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rw [elemSymm_eq_perm r y σ, mul_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [mul_assoc, ← prod_pow_indic S (fun i => y (σ i)), ← prod_mul_distrib]
  simp only [Pi.add_apply, pow_add]

/-! ### The dimension form -/

/-- The alternant at the geometric point `(1, z, …, z^{q-1})` is a Vandermonde determinant. -/
theorem alternant_geom (α : Fin q → ℕ) (z : R) :
    alternant α (fun i => z ^ (i : ℕ)) = ∏ i, ∏ j ∈ Ioi i, (z ^ α j - z ^ α i) := by
  have : (Matrix.of fun (i j : Fin q) => (z ^ (i : ℕ)) ^ α j) =
      (vandermonde fun j => z ^ α j)ᵀ := by
    ext i j
    simp [vandermonde_apply, ← pow_mul, mul_comm]
  rw [alternant, this, det_transpose, det_vandermonde]

/-- The truncated geometric sum `1 + X + ⋯ + X^{n-1}`. -/
noncomputable def geomPoly (n : ℕ) : ℤ[X] := ∑ m ∈ range n, X ^ m

theorem X_pow_sub_X_pow (a b : ℕ) :
    (X : ℤ[X]) ^ b - X ^ a = (X - 1) * (geomPoly b - geomPoly a) := by
  have hb := geom_sum_mul (X : ℤ[X]) b
  have ha := geom_sum_mul (X : ℤ[X]) a
  simp only [geomPoly]
  linear_combination -hb + ha

theorem eval_one_geomPoly (n : ℕ) : (geomPoly n).eval 1 = n := by
  simp [geomPoly, eval_finsetSum]

/-- The reduced Vandermonde product `∏_{i<j} (G(α_j) - G(α_i))` of geometric sums. -/
noncomputable def geomVand (α : Fin q → ℕ) : ℤ[X] :=
  ∏ i, ∏ j ∈ Ioi i, (geomPoly (α j) - geomPoly (α i))

theorem alternant_geom_eq (α : Fin q → ℕ) :
    alternant α (fun i => (X : ℤ[X]) ^ (i : ℕ)) =
      (X - 1) ^ (∑ i : Fin q, (Ioi i).card) * geomVand α := by
  rw [alternant_geom, geomVand, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_const, ← prod_mul_distrib]
  exact prod_congr rfl fun j _ => X_pow_sub_X_pow _ _

theorem eval_one_elemSymm_geom (r : ℕ) :
    (elemSymm r (fun i : Fin q => (X : ℤ[X]) ^ (i : ℕ))).eval 1 = (q.choose r : ℤ) := by
  simp [elemSymm, eval_finsetSum, eval_prod, card_powersetCard]

theorem eval_one_geomVand (α : Fin q → ℕ) :
    (geomVand α).eval 1 = ∏ i, ∏ j ∈ Ioi i, ((α j : ℤ) - α i) := by
  simp [geomVand, eval_prod, eval_one_geomPoly]

/-- The vertical-strip Pieri rule at `y = 1`, in reduced Vandermonde form. -/
theorem sum_prod_add_indic (α : Fin q → ℕ) (r : ℕ) :
    ∑ S ∈ powersetCard r (univ : Finset (Fin q)),
        ∏ i, ∏ j ∈ Ioi i, (((α + indic S) j : ℤ) - (α + indic S) i) =
      (q.choose r : ℤ) * ∏ i, ∏ j ∈ Ioi i, ((α j : ℤ) - α i) := by
  have h := alternant_mul_elemSymm α r (fun i : Fin q => (X : ℤ[X]) ^ (i : ℕ))
  simp only [alternant_geom_eq] at h
  rw [← mul_sum, mul_assoc] at h
  have hX : ((X : ℤ[X]) - 1) ^ (∑ i : Fin q, (Ioi i).card) ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero 1)
  have h' := mul_left_cancel₀ hX h
  have := congrArg (eval 1) h'
  rw [eval_mul, eval_finsetSum, eval_one_geomVand, eval_one_elemSymm_geom] at this
  simp only [eval_one_geomVand] at this
  rw [← this, mul_comm]

theorem prod_Ioi_eq_vand (t : Fin q → ℝ) :
    ∏ i, ∏ j ∈ Ioi i, (t j - t i) = (-1) ^ (rowPairs q).card * vand t := by
  have h : ∏ ij ∈ rowPairs q, (t ij.2 - t ij.1) = ∏ i, ∏ j ∈ Ioi i, (t j - t i) := by
    rw [rowPairs, prod_filter, ← univ_product_univ, prod_product]
    refine prod_congr rfl fun i _ => ?_
    rw [← prod_filter]
    congr 1
    ext j
    simp
  rw [← h, vand, ← prod_neg]
  exact prod_congr rfl fun ij _ => by ring

/-- **The vertical-strip Pieri rule in dimension form**:
`∑_{|S| = r} V(α + 1_S) = binom(q, r) V(α)` for the Vandermonde product `V`. -/
theorem sum_vand_add_indic (α : Fin q → ℕ) (r : ℕ) :
    ∑ S ∈ powersetCard r (univ : Finset (Fin q)),
        vand (fun i => ((α + indic S) i : ℝ)) = (q.choose r : ℝ) * vand (fun i => (α i : ℝ)) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (sum_prod_add_indic α r)
  push_cast at h
  have hs : ∀ β : Fin q → ℕ, ∏ i, ∏ j ∈ Ioi i, ((β j : ℝ) - β i) =
      (-1) ^ (rowPairs q).card * vand (fun i => (β i : ℝ)) :=
    fun β => prod_Ioi_eq_vand _
  simp only [hs] at h
  rw [← mul_sum, mul_left_comm] at h
  have hu : ((-1 : ℝ) ^ (rowPairs q).card) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hu h

theorem shiftedPart_add_indic (p : Fin q → ℕ) (S : Finset (Fin q)) :
    shiftedPart (p + indic S) = shiftedPart p + indic S := by
  funext i
  simp only [shiftedPart, Pi.add_apply]
  ring

/-- **The vertical-strip Pieri rule for the Weyl dimension formula**:
`∑_{|S| = r} W_{λ + 1_S} = binom(q, r) W_λ`. Summands whose part vector is not a partition
vanish when `λ` is one. -/
theorem sum_weylFormula_add_indic (p : Fin q → ℕ) (r : ℕ) :
    ∑ S ∈ powersetCard r (univ : Finset (Fin q)), weylFormula (p + indic S) =
      (q.choose r : ℝ) * weylFormula p := by
  simp only [weylFormula_eq_vand, ← sum_div, shiftedPart_add_indic]
  rw [mul_div_assoc']
  congr 1
  exact sum_vand_add_indic (shiftedPart p) r

end Partition
