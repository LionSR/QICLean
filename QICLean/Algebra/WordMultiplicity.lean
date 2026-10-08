/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Multiplicities of finite words

The coefficient of a monomial in a power of the sum of variables counts words
with the prescribed multiplicities. Comparing this expansion with the
multinomial theorem gives the exact cardinality, including an empty alphabet.
This is the combinatorial intermediate for the fixed-time count and ordering
calculation in `09-amplification.tex`, lines 49–54 and 237–253.
-/

open scoped BigOperators Nat

namespace WordMultiplicity

variable {ι : Type*} {m : ℕ}

/-- The multiplicity of every letter in a finite word. -/
noncomputable def countsFinsupp (w : Fin m → ι) : ι →₀ ℕ :=
  ∑ j, Finsupp.single (w j) 1

variable [Fintype ι]

/-- The letter multiplicities sum to the word length. -/
lemma sum_counts (w : Fin m → ι) : (∑ i, countsFinsupp w i) = m := by
  classical
  simp only [countsFinsupp, Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp

private lemma sum_monomial_counts (m : ℕ) :
    (∑ i, MvPolynomial.X i : MvPolynomial ι ℕ) ^ m =
      ∑ w : Fin m → ι, MvPolynomial.monomial (countsFinsupp w) 1 := by
  classical
  have h : (∑ i, MvPolynomial.X i : MvPolynomial ι ℕ) ^ m =
      ∏ _j : Fin m, ∑ i, MvPolynomial.X i := by simp
  rw [h, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  simpa only [countsFinsupp, MvPolynomial.X] using
    (MvPolynomial.monomial_sum_one (R := ℕ) Finset.univ
      (fun j : Fin m ↦ Finsupp.single (w j) 1)).symm

/-- The number of words of a fixed length with prescribed multiplicities. -/
lemma card_counts_eq (m : ℕ) (n : ι → ℕ) :
    Fintype.card {w : Fin m → ι // (countsFinsupp w : ι → ℕ) = n} =
      if ∑ i, n i = m then Nat.multinomial Finset.univ n else 0 := by
  classical
  let d : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm n
  have hd : d.sum (fun _ k ↦ k) = ∑ i, n i := by
    rw [Finsupp.sum_fintype]
    · rfl
    · intro i
      rfl
  have hmult : d.multinomial = Nat.multinomial Finset.univ n := by
    exact Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)
  have h := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℕ) d m
  rw [sum_monomial_counts, MvPolynomial.coeff_sum, hd, hmult] at h
  simp only [MvPolynomial.coeff_monomial, Nat.cast_id] at h
  have heq (w : Fin m → ι) : countsFinsupp w = d ↔ (countsFinsupp w : ι → ℕ) = n := by
    exact ⟨fun h ↦ congrArg DFunLike.coe h, fun h ↦ DFunLike.coe_injective h⟩
  simp_rw [heq] at h
  simpa only [Fintype.card_subtype, Finset.sum_boole, Nat.cast_id] using h

end WordMultiplicity
