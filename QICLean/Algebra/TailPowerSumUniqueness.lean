/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Uniqueness of finite power sums on a tail

Two finite multisets of nonzero complex numbers whose power sums agree for every
sufficiently large exponent are equal, including multiplicities.  Repeated
values contribute an integer multiplicity to a power sum, and a Vandermonde
argument on the finitely many distinct values recovers those multiplicities
from finitely many tail exponents; no genuine cancellation among *distinct*
weights can persist on an entire tail.

Source: TNLean note `Notes/OpenProblemsTN/followup/asymmetric_mpoa/sections/t1_unblocked.tex`,
Lemma `moa-t1:powers`.

As an application, if a finite family of nonzero complex numbers `μ₁, …, μₙ` has power sums
`s_L = ∑ₖ μₖ^L` of modulus one at every positive exponent `L`, then the family has exactly one
member, and that member is a phase. Indeed `|s_L|² = ∑_{k,l} (μₖ conj μₗ)^L`, so the multiset
`{μₖ conj μₗ}` of `n²` nonzero numbers has the power sums of `{1}` at every positive exponent; by
uniqueness of power sums on a tail the two multisets agree, and `n² = 1`. This is the analytic
step of arXiv:2405.00439, lines 571–574 of the source, where it is argued by comparing the
exponents `N` and `2N` after bringing all `μₖ^N` close to the positive real axis. The argument
here replaces that approximation step by power-sum uniqueness.

Moved from TNLean, `TNLean/Algebra/TailPowerSumUniqueness.lean` and
`TNLean/Algebra/UnimodularPowerSum.lean` at commit `49b78ed821` (Apache-2.0). Changes: the two
files are merged.

## Main results

* `Multiset.eq_of_notMem_zero_of_forall_sum_map_pow_eq` — the multiset
  uniqueness statement.
* `Multiset.eq_zero_of_notMem_zero_of_forall_sum_map_pow_eq_zero` — the
  vanishing corollary: a nonempty multiset of nonzero weights cannot have all
  sufficiently large power sums equal to zero.
* `Complex.exists_norm_eq_one_sum_pow_eq_pow`: power sums of unit modulus are the powers of
  one phase.

## Relation to other power-sum statements

`Matrix.sum_pow_eq_implies_card_eq_and_multiset_eq_of_le_max_card` in
`QICLean.Algebra.ScalarPowerSumIdentity` compares power sums at the exponents `1, …, max m n`;
the statements here use only the exponents of a tail `L ≥ n₀`.
-/

open scoped BigOperators

namespace Multiset

variable {Λ Λ' : Multiset ℂ}

/-- **Uniqueness of finite power sums on a tail.**

Two finite multisets of nonzero complex numbers whose power sums agree for every
sufficiently large integer exponent are equal, including multiplicities.

Source: TNLean note `t1_unblocked.tex`, Lemma `moa-t1:powers`. -/
theorem eq_of_notMem_zero_of_forall_sum_map_pow_eq
    (hΛ : (0 : ℂ) ∉ Λ) (hΛ' : (0 : ℂ) ∉ Λ')
    (h : ∃ n₀ : ℕ, ∀ L, n₀ ≤ L → (Λ.map (· ^ L)).sum = (Λ'.map (· ^ L)).sum) :
    Λ = Λ' := by
  classical
  obtain ⟨n₀, hn₀⟩ := h
  set S : Finset ℂ := Λ.toFinset ∪ Λ'.toFinset with hS
  set b : ℂ → ℂ := fun x => (Λ.count x : ℂ) - (Λ'.count x : ℂ) with hb
  have hΛeq : ∀ L : ℕ, (Λ.map (· ^ L)).sum = ∑ x ∈ S, (Λ.count x : ℂ) * x ^ L := by
    intro L
    rw [Finset.sum_multiset_map_count Λ (fun x => x ^ L)]
    rw [← Finset.sum_subset (Finset.subset_union_left (s₁ := Λ.toFinset) (s₂ := Λ'.toFinset))]
    · exact Finset.sum_congr rfl fun x _ => by rw [nsmul_eq_mul]
    · intro x _ hx
      rw [Multiset.count_eq_zero_of_notMem fun hmem => hx (Multiset.mem_toFinset.mpr hmem)]
      simp
  have hΛ'eq : ∀ L : ℕ, (Λ'.map (· ^ L)).sum = ∑ x ∈ S, (Λ'.count x : ℂ) * x ^ L := by
    intro L
    rw [Finset.sum_multiset_map_count Λ' (fun x => x ^ L)]
    rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := Λ.toFinset) (s₂ := Λ'.toFinset))]
    · exact Finset.sum_congr rfl fun x _ => by rw [nsmul_eq_mul]
    · intro x _ hx
      rw [Multiset.count_eq_zero_of_notMem fun hmem => hx (Multiset.mem_toFinset.mpr hmem)]
      simp
  have hSum : ∀ L : ℕ, n₀ ≤ L → ∑ x ∈ S, b x * x ^ L = 0 := by
    intro L hL
    have hcount := hn₀ L hL
    rw [hΛeq, hΛ'eq] at hcount
    have : ∑ x ∈ S, b x * x ^ L
        = (∑ x ∈ S, (Λ.count x : ℂ) * x ^ L) - ∑ x ∈ S, (Λ'.count x : ℂ) * x ^ L := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by rw [hb]; ring
    rw [this, hcount, sub_self]
  have hx0 : ∀ x ∈ S, x ≠ 0 := by
    intro x hx h0
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hΛ (h0 ▸ Multiset.mem_toFinset.mp hx)
    · exact hΛ' (h0 ▸ Multiset.mem_toFinset.mp hx)
  -- Vandermonde step: reindex the (finitely many) distinct values by a `Fin`-type.
  set q := Fintype.card {x // x ∈ S} with hq
  set eqv : {x // x ∈ S} ≃ Fin q := Fintype.equivFin {x // x ∈ S} with heqv
  set e : Fin q → ℂ := fun j => ((eqv.symm j : {x // x ∈ S}) : ℂ) with he
  have he_inj : Function.Injective e := by
    intro j j' hjj'
    exact eqv.symm.injective (Subtype.ext hjj')
  set v : Fin q → ℂ := fun j => b (e j) * (e j) ^ n₀ with hv
  have hattach : ∀ g : ℂ → ℂ, ∑ y : {x // x ∈ S}, g (y : ℂ) = ∑ x ∈ S, g x := by
    intro g
    simpa using Finset.sum_attach S g
  have hvzero : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero he_inj
    intro i
    have hreindex : ∑ j : Fin q, v j * (e j) ^ (i : ℕ) = ∑ x ∈ S, b x * x ^ (n₀ + i) := by
      have hcomp : ∑ j : Fin q, v j * (e j) ^ (i : ℕ)
          = ∑ j : Fin q, b (e j) * (e j) ^ (n₀ + i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hv]
        ring
      rw [hcomp]
      simp only [he]
      rw [Equiv.sum_comp eqv.symm (fun y : {x // x ∈ S} => b (y : ℂ) * (y : ℂ) ^ (n₀ + i))]
      exact hattach (fun x => b x * x ^ (n₀ + i))
    rw [hreindex]
    exact hSum (n₀ + i) (Nat.le_add_right n₀ i)
  have hb0 : ∀ x ∈ S, b x = 0 := by
    intro x hx
    have hxe : ∃ j : Fin q, e j = x := by
      refine ⟨eqv ⟨x, hx⟩, ?_⟩
      simp only [he, Equiv.symm_apply_apply]
    obtain ⟨j, hj⟩ := hxe
    have hvj : v j = 0 := by rw [hvzero]; rfl
    simp only [hv, hj] at hvj
    rcases mul_eq_zero.mp hvj with h | h
    · exact h
    · exact absurd h (pow_ne_zero n₀ (hx0 x hx))
  ext x
  by_cases hxS : x ∈ S
  · have hbx := hb0 x hxS
    simp only [hb] at hbx
    have hcast : (Λ.count x : ℂ) = (Λ'.count x : ℂ) := sub_eq_zero.mp hbx
    exact_mod_cast hcast
  · have hxΛ : x ∉ Λ.toFinset := fun h => hxS (Finset.mem_union_left _ h)
    have hxΛ' : x ∉ Λ'.toFinset := fun h => hxS (Finset.mem_union_right _ h)
    rw [Multiset.count_eq_zero_of_notMem (fun h => hxΛ (Multiset.mem_toFinset.mpr h)),
      Multiset.count_eq_zero_of_notMem (fun h => hxΛ' (Multiset.mem_toFinset.mpr h))]

/-- A nonempty finite multiset of nonzero complex numbers cannot have all its
sufficiently large power sums equal to zero.

Source: TNLean note `t1_unblocked.tex`, Lemma `moa-t1:powers`, "in particular" clause. -/
theorem eq_zero_of_notMem_zero_of_forall_sum_map_pow_eq_zero
    (hΛ : (0 : ℂ) ∉ Λ)
    (h : ∃ n₀ : ℕ, ∀ L, n₀ ≤ L → (Λ.map (· ^ L)).sum = 0) :
    Λ = 0 := by
  have h0 : (0 : ℂ) ∉ (0 : Multiset ℂ) := by simp
  refine eq_of_notMem_zero_of_forall_sum_map_pow_eq hΛ h0 ?_
  obtain ⟨n₀, hn₀⟩ := h
  exact ⟨n₀, fun L hL => by rw [hn₀ L hL]; simp⟩

end Multiset

open scoped ComplexConjugate

namespace Complex

/-- **Power sums of unit modulus come from one phase.** If `μ₁, …, μₙ` are
nonzero and `‖∑ₖ μₖ^L‖ = 1` for every positive `L`, then there is `λ` with `‖λ‖ = 1` and
`∑ₖ μₖ^L = λ^L` for every `L`, and `n = 1`. -/
theorem exists_norm_eq_one_sum_pow_eq_pow {n : ℕ} (μ : Fin n → ℂ) (hμ : ∀ k, μ k ≠ 0)
    (h : ∀ L : ℕ, 0 < L → ‖(∑ k, μ k ^ L)‖ = 1) :
    n = 1 ∧ ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ L : ℕ, ∑ k, μ k ^ L = lam ^ L := by
  classical
  set Λ : Multiset ℂ :=
    (Finset.univ : Finset (Fin n × Fin n)).val.map (fun p ↦ μ p.1 * conj (μ p.2)) with hΛ
  have hΛ0 : (0 : ℂ) ∉ Λ := by
    rw [hΛ, Multiset.mem_map]
    rintro ⟨p, -, hp⟩
    exact mul_ne_zero (hμ p.1) ((map_ne_zero _).2 (hμ p.2)) hp
  have hsum : ∀ L : ℕ, 1 ≤ L → (Λ.map (· ^ L)).sum = (({1} : Multiset ℂ).map (· ^ L)).sum := by
    intro L hL
    have hL' := h L hL
    rw [hΛ, Multiset.map_map]
    change ∑ p : Fin n × Fin n, (μ p.1 * conj (μ p.2)) ^ L = _
    simp only [Multiset.map_singleton, one_pow, Multiset.sum_singleton, mul_pow,
      ← map_pow, Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, hL', one_pow, Complex.ofReal_one]
  have hEq := Multiset.eq_of_notMem_zero_of_forall_sum_map_pow_eq hΛ0 (by simp) ⟨1, hsum⟩
  have hcard := congrArg Multiset.card hEq
  simp only [hΛ, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Multiset.card_singleton] at hcard
  obtain rfl : n = 1 := Nat.eq_one_of_mul_eq_one_right hcard
  refine ⟨rfl, μ 0, ?_, fun L ↦ by rw [Fin.sum_univ_one]⟩
  simpa [Fin.sum_univ_one] using h 1 one_pos

end Complex
