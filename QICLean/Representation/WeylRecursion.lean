/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.HookRecursion

/-!
# The Pieri recursion for the Weyl dimension formula

For a partition `λ` padded to length `q` with shifted parts `l_i = λ_i + q - 1 - i`, let
`W_λ = ∏_{i<j} (l_i - l_j)/(j - i)` be the right-hand side of the Weyl dimension formula of
the area-law paper (*A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, equation `replicas:dimensions`). Adding a box to row `i` multiplies `W_λ`
by `∏_{j ≠ i} (l_i + 1 - l_j)/(l_i - l_j)`, and the interpolation identity
`∑_i ∏_{j ≠ i} (t_i + 1 - t_j)/(t_i - t_j) = q` gives the Pieri recursion
`∑_i W_{λ + e_i} = q W_λ` (`05-replicas.tex`, lines 237–241: `V_ν ⊗ ℂ^q = ⊕ V_{ν + e_i}`).

## Main declarations

* `Partition.sum_prod_add_one_div_eq_card` — the interpolation identity.
* `Partition.weylFormula_update_add_mul`, `Partition.sum_weylFormula_add`.
-/

open Finset Polynomial

namespace Partition

variable {q : ℕ}

/-- `∑_i ∏_{j ≠ i} (t_i + 1 - t_j)/(t_i - t_j) = q` for distinct nodes. -/
theorem sum_prod_add_one_div_eq_card {t : Fin q → ℝ} (ht : Function.Injective t) :
    ∑ i, (∏ j ∈ univ.erase i, (t i + 1 - t j)) / ∏ j ∈ univ.erase i, (t i - t j) = q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  set A : ℝ[X] := Lagrange.nodal univ fun j => t j - 1
  set B : ℝ[X] := Lagrange.nodal univ t
  have hA : A.Monic := Lagrange.nodal_monic
  have hB : B.Monic := Lagrange.nodal_monic
  have hAd : A.natDegree = q := by simp [A, Lagrange.natDegree_nodal]
  have hBd : B.natDegree = q := by simp [B, Lagrange.natDegree_nodal]
  have hdeg : (A - B).degree < #(univ : Finset (Fin q)) := by
    rw [card_univ, Fintype.card_fin, degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_sub]
    rcases hm.lt_or_eq with hm | rfl
    · rw [coeff_eq_zero_of_natDegree_lt (hAd ▸ hm), coeff_eq_zero_of_natDegree_lt (hBd ▸ hm),
        sub_zero]
    · have h1 : A.coeff q = 1 := hAd ▸ hA.coeff_natDegree
      have h2 : B.coeff q = 1 := hBd ▸ hB.coeff_natDegree
      rw [h1, h2, sub_self]
  have hL := Lagrange.coeff_eq_sum (s := univ) (v := t) (fun _ _ _ _ h => ht h) hdeg
  rw [card_univ, Fintype.card_fin, coeff_sub] at hL
  have hcA : A.coeff (q - 1) = -∑ j, (t j - 1) := by
    have := prod_X_sub_C_coeff_card_pred (univ : Finset (Fin q)) (fun j => t j - 1)
      (by simpa using hq)
    simpa [A, Lagrange.nodal] using this
  have hcB : B.coeff (q - 1) = -∑ j, t j := by
    have := prod_X_sub_C_coeff_card_pred (univ : Finset (Fin q)) t (by simpa using hq)
    simpa [B, Lagrange.nodal] using this
  rw [hcA, hcB] at hL
  have hval : ∀ i, (A - B).eval (t i) = ∏ j ∈ univ.erase i, (t i + 1 - t j) := by
    intro i
    rw [eval_sub, Lagrange.eval_nodal_at_node (mem_univ i), sub_zero, Lagrange.eval_nodal,
      ← mul_prod_erase univ _ (mem_univ i)]
    simp only [sub_sub_cancel, one_mul]
    exact prod_congr rfl fun j _ => by ring
  simp only [hval] at hL
  rw [← hL, sum_sub_distrib]
  simp

theorem weylFormula_eq_vand (p : Fin q → ℕ) :
    weylFormula p = vand (fun j => (shiftedPart p j : ℝ)) /
      ∏ ij ∈ rowPairs q, ((ij.2 : ℝ) - ij.1) := by
  rw [weylFormula, prod_div_distrib, vand]

theorem rowPairs_denom_pos : (0 : ℝ) < ∏ ij ∈ rowPairs q, ((ij.2 : ℝ) - ij.1) :=
  prod_pos fun ij hij => by
    have : (ij.1 : ℕ) < ij.2 := (mem_filter.mp hij).2
    have : ((ij.1 : ℕ) : ℝ) < (ij.2 : ℕ) := by exact_mod_cast this
    linarith

/-- The Weyl dimension formula of the empty partition is one. -/
theorem weylFormula_zero : weylFormula (0 : Fin q → ℕ) = 1 := by
  refine prod_eq_one fun ij hij => ?_
  have hlt : (ij.1 : ℕ) < ij.2 := (mem_filter.mp hij).2
  have hne : ((ij.2 : ℝ) - ij.1) ≠ 0 := by
    have : ((ij.1 : ℕ) : ℝ) < (ij.2 : ℕ) := by exact_mod_cast hlt
    linarith
  rw [div_eq_one_iff_eq hne]
  simp only [shiftedPart, Pi.zero_apply, zero_add]
  have e : ∀ a : ℕ, a < q → ((q - 1 - a : ℕ) : ℝ) = q - 1 - a := fun a ha => by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  rw [e _ ij.1.2, e _ ij.2.2]
  ring

theorem weylFormula_eq_zero_of_shiftedPart_eq (p : Fin q → ℕ) {a b : Fin q} (hab : a < b)
    (h : shiftedPart p a = shiftedPart p b) : weylFormula p = 0 := by
  rw [weylFormula, prod_eq_zero (i := (a, b)) (by simp [rowPairs, hab]) (by simp [h])]

/-- Adding a box to row `i` multiplies the Weyl formula by
`∏_{j ≠ i} (l_i + 1 - l_j)/(l_i - l_j)`, in multiplied-out form. -/
theorem weylFormula_update_add_mul (p : Fin q → ℕ) (i : Fin q) :
    weylFormula (Function.update p i (p i + 1)) *
        ∏ j ∈ univ.erase i, ((shiftedPart p i : ℝ) - shiftedPart p j) =
      weylFormula p * ∏ j ∈ univ.erase i, ((shiftedPart p i : ℝ) + 1 - shiftedPart p j) := by
  set L : Fin q → ℝ := fun j => (shiftedPart p j : ℝ)
  have hsh : (fun j => (shiftedPart (Function.update p i (p i + 1)) j : ℝ)) =
      Function.update L i (L i + 1) := by
    rw [shiftedPart_update]
    funext j
    by_cases hij : j = i
    · subst hij
      simp only [Function.update_self, L, shiftedPart]
      push_cast
      ring
    · simp [hij, L]
  rw [weylFormula_eq_vand, weylFormula_eq_vand, hsh, div_mul_eq_mul_div, vand_update_mul,
    div_mul_eq_mul_div]

/-- **Pieri recursion for the Weyl formula**: `∑_i W_{λ + e_i} = q W_λ`, where the terms for
rows that cannot gain a box vanish. -/
theorem sum_weylFormula_add {p : Fin q → ℕ} (hp : Antitone p) :
    ∑ i, weylFormula (Function.update p i (p i + 1)) = q * weylFormula p := by
  set L : Fin q → ℝ := fun j => (shiftedPart p j : ℝ)
  have hinj := shiftedPart_injective hp
  have hD : ∀ i, ∏ j ∈ univ.erase i, (L i - L j) ≠ 0 := fun i =>
    prod_ne_zero_iff.mpr fun j hj => sub_ne_zero.mpr fun h => (mem_erase.mp hj).1 (hinj h).symm
  have hterm : ∀ i, weylFormula (Function.update p i (p i + 1)) =
      weylFormula p *
        ((∏ j ∈ univ.erase i, (L i + 1 - L j)) / ∏ j ∈ univ.erase i, (L i - L j)) := by
    intro i
    have := weylFormula_update_add_mul p i
    field_simp [hD i]
    simp only [L] at this ⊢
    linear_combination this
  rw [sum_congr rfl fun i _ => hterm i, ← mul_sum, sum_prod_add_one_div_eq_card hinj, mul_comm]

end Partition
