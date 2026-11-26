/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Multiplicities of finite words

The coefficient of a monomial in a power of the sum of variables counts words
with the prescribed multiplicities. Comparing this expansion with the
multinomial theorem gives the exact cardinality, including an empty alphabet.
This is the combinatorial intermediate for the fixed-time count and ordering
calculation in `09-amplification.tex`, lines 49–54 and 237–253.

It also contains the following results.

* `Fintype.sum_pow_eq_sum_ordered_words`, `Fintype.smul_sub_average_pow_eq_sum_ordered_words`:
  ordered words in a power of a finite sum.
* `Polynomial.coeff_pow_sum_smul_add_C_mul_X_eq_sum_counts`: polynomial coefficients grouped by
  ordered-word frequencies.
-/

section

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

section WordCoefficient

/-!
# Actual ordered-word coefficients

The coefficient of a prescribed frequency vector is the sum of all ordered products
with those letter counts. Renaming the alphabet bijectively preserves the counts.

Source: AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 604--617.
-/

open scoped BigOperators

namespace WordMultiplicity

/-- The actual ordered-word coefficient for a prescribed full frequency vector.
AKLV, arXiv:1301.1162v1, Lemma 4.2, lines 604--617. -/
noncomputable def wordCoefficient {ι R : Type*} [Fintype ι] [Semiring R]
    (H : ι → R) (degree : ℕ) (α : ι → ℕ) : R :=
  open Classical in
  ∑ w ∈ (Finset.univ : Finset (Fin degree → ι)).filter
      (fun w ↦ (countsFinsupp w : ι → ℕ) = α),
    (List.ofFn (fun p ↦ H (w p))).prod

/-- Counts are preserved when the alphabet is renamed bijectively.
AKLV, arXiv:1301.1162v1, the word-frequency expansion in Lemma 4.2. -/
theorem countsFinsupp_equiv {ι κ : Type*} (e : ι ≃ κ) {degree : ℕ}
    (w : Fin degree → ι) (a : ι) :
    countsFinsupp (fun p ↦ e (w p)) (e a) = countsFinsupp w a := by
  classical
  simp only [countsFinsupp, Finsupp.finsetSum_apply, Finsupp.single_apply,
    e.injective.eq_iff]

end WordMultiplicity

end WordCoefficient

end

section FiniteSumPowers

/-!
## Ordered words in a power of a finite sum

A power of a finite sum is the sum of its ordered words. The identity
holds in an arbitrary semiring and does not require commuting summands.
It includes the empty alphabet and exponent zero. For a nonempty alphabet
in a complex algebra, the same identity gives the normalized expansion
into words of the complementary operators.

This is the word expansion used in LVV, arXiv:1307.5143v1, equation
eq:a-exp, lines 606–609, and AKLV, arXiv:1301.1162v1, Lemma l:agsp,
lines 604–617. The spectral properties of the power approximation and
the collection of words with prescribed multiplicities are separate results.
-/

open scoped BigOperators

/-- Ordered expansion of a power of a finite sum. LVV, arXiv:1307.5143v1,
equation eq:a-exp, lines 606–609; AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 604–617. -/
theorem Fintype.sum_pow_eq_sum_ordered_words
    {ι R : Type*} [Fintype ι] [Semiring R] (P : ι → R) (m : ℕ) :
    (∑ i, P i) ^ m =
      ∑ w : Fin m → ι, (List.ofFn (fun j => P (w j))).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum]
    rw [← Fintype.sum_prod_type (fun p : ι × (Fin m → ι) =>
      P p.1 * (List.ofFn (fun j => P (p.2 j))).prod)]
    refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => ι)) _ _ ?_
    simp [Fin.consEquiv, List.ofFn_succ]

/-- Algebraic normalization of the ordered expansion in LVV,
arXiv:1307.5143v1, equation eq:a-exp, lines 599–609.
In the chain application, the alphabet includes an identity padding term,
represented by an additional index with h = 0. -/
theorem Fintype.smul_sub_average_pow_eq_sum_ordered_words
    {ι R : Type*} [Fintype ι] [Nonempty ι] [Ring R] [Algebra ℂ R]
    (h : ι → R) (c : ℂ) (m : ℕ) :
    (c • (1 - (Fintype.card ι : ℂ)⁻¹ • ∑ i, h i)) ^ m =
      (c / (Fintype.card ι : ℂ)) ^ m •
        ∑ w : Fin m → ι, (List.ofFn (fun j => 1 - h (w j))).prod := by
  have hN : (Fintype.card ι : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (∑ i, (1 - h i)) =
      (Fintype.card ι : ℂ) • (1 : R) - ∑ i, h i := by
    simp [Finset.sum_sub_distrib, Nat.cast_smul_eq_nsmul]
  have hnorm : c • (1 - (Fintype.card ι : ℂ)⁻¹ • ∑ i, h i) =
      (c / (Fintype.card ι : ℂ)) • ∑ i, (1 - h i) := by
    simp [hsum, smul_sub, smul_smul, div_eq_mul_inv, hN]
  rw [hnorm, smul_pow, Fintype.sum_pow_eq_sum_ordered_words]

end FiniteSumPowers

section WordCoefficientExpansion

/-!
## Polynomial coefficients grouped by ordered-word frequencies

A central polynomial variable records occurrences of a distinguished operator.
Complex scalar weights record the ordinary letters. Expanding a power into
ordered words and collecting their frequencies identifies its actual coefficient
with the corresponding monomial family. The operator factors remain in their
original order throughout the calculation.

The ordinary alphabet may be empty, and the exponent may be zero. Operator
coefficients may coincide or vanish. Selected sums of the coefficient operators
and local operator Schmidt-rank bounds are separate statements.

Source: AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 604–617 and 626–635.
-/

open scoped BigOperators

namespace Polynomial

private theorem list_monomial_factor
    {ι R : Type*} [Semiring R] [Algebra ℂ R]
    (H : ι → R) (T : R) (z : ι → ℂ) (L : List (Option ι)) :
    (L.map (fun a ↦ match a with
      | none => Polynomial.C T * Polynomial.X
      | some j => Polynomial.C (z j • H j))).prod =
      Polynomial.monomial
        ((L.map (fun a ↦ if a = none then 1 else 0)).sum)
        ((L.map (Option.elim' (1 : ℂ) z)).prod •
          (L.map (Option.elim' T H)).prod) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
    cases a <;> simp only [Option.elim', reduceIte, Option.some_ne_none,
      Polynomial.X, ← Polynomial.monomial_zero_left,
      Polynomial.monomial_mul_monomial, zero_add, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

private theorem word_weight {ι : Type*} [Fintype ι] (z : ι → ℂ)
    {d : ℕ} (w : Fin d → Option ι) :
    (List.ofFn (fun p ↦ Option.elim' (1 : ℂ) z (w p))).prod =
      ∏ j, z j ^ WordMultiplicity.countsFinsupp w (some j) := by
  calc
    _ = ∏ p, Option.elim' (1 : ℂ) z (w p) := List.prod_ofFn
    _ = (WordMultiplicity.countsFinsupp w).prod
        (fun a n ↦ (Option.elim' (1 : ℂ) z a) ^ n) := by
      simpa only [WordMultiplicity.countsFinsupp, Finsupp.prod_single_index,
        pow_zero, pow_one] using
        (Finsupp.prod_finsetSum_index (s := Finset.univ)
          (g := fun p ↦ Finsupp.single (w p) 1)
          (h := fun a n ↦ (Option.elim' (1 : ℂ) z a) ^ n)
          (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _))
    _ = _ := by rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]; simp

private theorem word_polynomial {ι R : Type*} [Fintype ι] [Semiring R] [Algebra ℂ R]
    (H : ι → R) (T : R) (z : ι → ℂ) {d : ℕ} (w : Fin d → Option ι) :
    (List.ofFn (fun p ↦ match w p with
      | none => Polynomial.C T * Polynomial.X
      | some j => Polynomial.C (z j • H j))).prod =
      Polynomial.monomial (WordMultiplicity.countsFinsupp w none)
        ((∏ j, z j ^ WordMultiplicity.countsFinsupp w (some j)) •
          (List.ofFn (fun p ↦ Option.elim' T H (w p))).prod) := by
  have hd : (List.ofFn (fun p ↦ if w p = none then 1 else 0)).sum =
      WordMultiplicity.countsFinsupp w none := by
    simp [Fin.sum_ofFn, WordMultiplicity.countsFinsupp, Finsupp.finsetSum_apply,
      Finsupp.single_apply]
  simpa only [List.map_ofFn, Function.comp_def, hd, word_weight] using
    list_monomial_factor H T z (List.ofFn w)

open Classical in
/-- Fixed distinguished-letter coefficient, AKLV arXiv:1301.1162v1,
Lemma l:agsp, lines 604–617 and 626–635. No operator commutation is assumed. -/
theorem coeff_pow_sum_smul_add_C_mul_X_eq_sum_counts
    {ι R : Type*} [Fintype ι] [Semiring R] [Algebra ℂ R]
    (H : ι → R) (T : R) (z : ι → ℂ) (m k : ℕ) :
    let E := Finset.piAntidiag (Finset.univ : Finset ι) m
    let f : E → R := fun a ↦
      ∑ w ∈ (Finset.univ : Finset (Fin (m + k) → Option ι)).filter
          (fun w ↦ WordMultiplicity.countsFinsupp w none = k ∧
            ∀ j : ι, WordMultiplicity.countsFinsupp w (some j) = a.val j),
        (List.ofFn (fun p ↦ match w p with
          | none => T
          | some j => H j)).prod
    ((Polynomial.C (∑ j, z j • H j) + Polynomial.C T * Polynomial.X) ^
      (m + k)).coeff k =
      ∑ a : E, (∏ j, z j ^ a.val j) • f a := by
  have hbase : Polynomial.C (∑ j, z j • H j) + Polynomial.C T * Polynomial.X =
      ∑ a : Option ι, match a with
        | none => Polynomial.C T * Polynomial.X
        | some j => Polynomial.C (z j • H j) := by
    simp [Fintype.sum_option, add_comm]
  simp_rw [hbase, Fintype.sum_pow_eq_sum_ordered_words,
    Polynomial.finsetSum_coeff, word_polynomial, Polynomial.coeff_monomial]
  have hmem (w : Fin (m + k) → Option ι)
      (hw : WordMultiplicity.countsFinsupp w none = k) :
      (fun j : ι ↦ WordMultiplicity.countsFinsupp w (some j)) ∈
        Finset.piAntidiag Finset.univ m :=
    Finset.mem_piAntidiag.mpr ⟨by
      have hs := WordMultiplicity.sum_counts w
      simp only [Fintype.sum_option, hw] at hs
      omega, fun _ _ ↦ Finset.mem_univ _⟩
  rw [← Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun w : Fin (m + k) → Option ι ↦
      WordMultiplicity.countsFinsupp w none = k))
    (t := Finset.piAntidiag Finset.univ m)
    (g := fun (w : Fin (m + k) → Option ι) (j : ι) ↦
      WordMultiplicity.countsFinsupp w (some j))
    (fun w hw ↦ hmem w (Finset.mem_filter.mp hw).2)]
  rw [← Finset.sum_coe_sort (Finset.piAntidiag Finset.univ m)]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  simp only [Finset.filter_filter, funext_iff, Finset.smul_sum]
  exact Finset.sum_congr rfl fun w hw ↦ by
    simp only [(Finset.mem_filter.mp hw).2.2]
    exact congrArg (fun v : Fin (m + k) → R ↦
      (∏ j, z j ^ a.val j) • (List.ofFn v).prod)
      (funext fun p ↦ by cases w p <;> rfl)

end Polynomial

end WordCoefficientExpansion
