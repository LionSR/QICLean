/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Gap.ContractionWordDecay
import QICLean.Probability.PoissonWord.Partition
import QICLean.Probability.PoissonWord.RealOccupation

/-!
# One clock realization for the full, retained and truncated products

The local-products lemma compares three chronological products on the same clock
realization: the full product `D` of the roots `(I - k_i)^{1/2}`, the retained product
`D_ret` over the events anchored near `S`, and its radius truncation. The truncation
estimate is stated for the product over the retained letters of a full Poisson word,
and the omission estimate for the product over a list of letters filtered by the same
predicate. This module identifies the two descriptions: a chronological product is the
product of its roots in reverse list order, and the retained product of a full word is
the product over the filtered list of its letters.

It also records that every chronological product of roots of positive contractions
annihilating `Ω`, and its adjoint, fix `Ω` and the projection onto `Ω`; that such a product
is a contraction, with the norm of the difference of two products bounded by the sum of the
differences of their letters; and the resulting integrability and expectation bounds under a
Poisson clock.

## Main statements

* `Matrix.contractionWord_eq_prod_reverse`: a chronological product as a list product.
* `Matrix.contractionWord_partitionWords_fst`: the retained product of a full word is the
  product over its filtered letters.
* `Matrix.contractionWord_mul_vecMulVec_self` and
  `Matrix.conjTranspose_contractionWord_mulVec_self`: the products fix the ground
  projection and their adjoints fix the ground vector.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 10.1 (`lem:amplification-local-products`), `09-amplification.tex`, lines 50–56
  and 70 (one clock realization for the three products), and lines 501–504 (every exact
  factor fixes the ground vector in both directions).
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- A chronological product of roots is the product of the roots of its letters in reverse
order, so that later letters act on the left.
Source: `09-amplification.tex`, lines 52–54. -/
theorem contractionWord_eq_prod_reverse (k : ι → Matrix n n ℂ) :
    ∀ (m : ℕ) (w : Fin m → ι),
      contractionWord k m w = ((List.ofFn w).reverse.map fun i => CFC.sqrt (1 - k i)).prod
  | 0, w => by simp
  | m + 1, w => by
    rw [contractionWord, contractionWord_eq_prod_reverse k m, List.ofFn_succ',
      List.concat_eq_append, List.reverse_append]
    simp

/-- **The retained product on the full realization.** The chronological product over the
letters of a full word that satisfy `P` equals the product over the `P`-filtered list of
its letters, with later letters on the left.
Source: `09-amplification.tex`, lines 52–56 and 70. -/
theorem contractionWord_partitionWords_fst (P : ι → Prop) [DecidablePred P]
    (k : ι → Matrix n n ℂ) (w : PoissonWord.Word ι) :
    contractionWord (fun i : {i // P i} => k i) (PoissonWord.partitionWords P w).1.1
        (PoissonWord.partitionWords P w).1.2 =
      (((List.ofFn w.2).filter fun i => decide (P i)).reverse.map
        fun i => CFC.sqrt (1 - k i)).prod := by
  rw [contractionWord_eq_prod_reverse, ← PoissonWord.ofFn_partitionWords_fst,
    List.map_reverse, List.map_reverse, List.map_map]
  rfl

/-- A chronological product of roots of contractions annihilating `Ω` fixes the
projection `|Ω⟩⟨Ω|` from the left.
Source: `09-amplification.tex`, lines 501–503. -/
theorem contractionWord_mul_vecMulVec_self (k : ι → Matrix n n ℂ) (hk : ∀ i, k i ≤ 1)
    {Ω : n → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0) (m : ℕ) (w : Fin m → ι) :
    contractionWord k m w * vecMulVec Ω (star Ω) = vecMulVec Ω (star Ω) := by
  have h0 : ∀ i, toEuclideanLin (k i) (WithLp.toLp 2 Ω) = 0 := fun i => by
    ext j; simp [hΩ i]
  have h := contractionWord_fix k hk h0 m w
  have h' : contractionWord k m w *ᵥ Ω = Ω := by
    simpa using congrArg WithLp.ofLp h
  rw [mul_vecMulVec, h']

/-- The adjoint of a chronological product of roots of positive contractions annihilating
`Ω` fixes `Ω`. Each root is Hermitian and fixes `Ω`.
Source: `09-amplification.tex`, lines 501–504. -/
theorem conjTranspose_contractionWord_mulVec_self (k : ι → Matrix n n ℂ)
    (hk : ∀ i, k i ≤ 1) {Ω : n → ℂ} (hΩ : ∀ i, k i *ᵥ Ω = 0) :
    ∀ (m : ℕ) (w : Fin m → ι), (contractionWord k m w)ᴴ *ᵥ Ω = Ω
  | 0, w => by simp
  | m + 1, w => by
    have hG : (CFC.sqrt (1 - k (w (Fin.last m))))ᴴ = CFC.sqrt (1 - k (w (Fin.last m))) :=
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq
    rw [contractionWord, conjTranspose_mul, hG, ← mulVec_mulVec,
      sqrt_one_sub_mulVec_eq_self (hk _) (hΩ _),
      conjTranspose_contractionWord_mulVec_self k hk hΩ m]

end Matrix

section
open MeasureTheory
open scoped BigOperators NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Matrix

section Generic

variable {n ι : Type*} [Fintype n] [DecidableEq n]

private theorem norm_sqrt_one_sub_le_one {k : Matrix n n ℂ} (hk₀ : 0 ≤ k) :
    ‖CFC.sqrt (1 - k)‖ ≤ 1 :=
  norm_le_one_of_nonneg_of_le_one (CFC.sqrt_nonneg _) (sqrt_le_one (sub_le_self 1 hk₀))

/-- A chronological product of the roots `(I - k_i)^{1/2}` of positive constraints
is a contraction. Source: area law, `09-amplification.tex`, line 63. -/
theorem norm_contractionWord_le_one (k : ι → Matrix n n ℂ) (hk₀ : ∀ i, 0 ≤ k i) :
    ∀ (m : ℕ) (w : Fin m → ι), ‖contractionWord k m w‖ ≤ 1
  | 0, w => by
    rw [contractionWord_zero]
    exact norm_le_one_of_nonneg_of_le_one zero_le_one le_rfl
  | m + 1, w => by
    rw [contractionWord]
    exact (norm_mul_le _ _).trans ((mul_le_mul (norm_sqrt_one_sub_le_one (hk₀ _))
      (norm_contractionWord_le_one k hk₀ m _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1))

/-- Replacing each root by one within `ε` changes a chronological product of
`m` roots by at most `m ε`. This is the telescoping step in area law,
`09-amplification.tex`, lines 230–232. -/
theorem norm_contractionWord_sub_le (k k' : ι → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk'₀ : ∀ i, 0 ≤ k' i) {ε : ℝ}
    (hε : ∀ i, ‖CFC.sqrt (1 - k i) - CFC.sqrt (1 - k' i)‖ ≤ ε) :
    ∀ (m : ℕ) (w : Fin m → ι),
      ‖contractionWord k m w - contractionWord k' m w‖ ≤ m * ε
  | 0, w => by simp
  | m + 1, w => by
    rw [contractionWord, contractionWord]
    set G := CFC.sqrt (1 - k (w (Fin.last m)))
    set G' := CFC.sqrt (1 - k' (w (Fin.last m)))
    set X := contractionWord k m fun j => w j.castSucc
    set X' := contractionWord k' m fun j => w j.castSucc
    have hsplit : G * X - G' * X' = G * (X - X') + (G - G') * X' := by
      rw [Matrix.mul_sub, Matrix.sub_mul]; abel
    have hG : ‖G‖ ≤ 1 := norm_sqrt_one_sub_le_one (hk₀ _)
    have hX' : ‖X'‖ ≤ 1 := norm_contractionWord_le_one k' hk'₀ m _
    have hXX : ‖X - X'‖ ≤ m * ε := norm_contractionWord_sub_le k k' hk₀ hk'₀ hε m _
    have hGG : ‖G - G'‖ ≤ ε := hε _
    have hε0 : 0 ≤ ε := (norm_nonneg _).trans hGG
    rw [hsplit]
    calc ‖G * (X - X') + (G - G') * X'‖
        ≤ ‖G‖ * ‖X - X'‖ + ‖G - G'‖ * ‖X'‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ 1 * (m * ε) + ε * 1 :=
          add_le_add (mul_le_mul hG hXX (norm_nonneg _) zero_le_one)
            (mul_le_mul hGG hX' (norm_nonneg _) hε0)
      _ = ((m + 1 : ℕ) : ℝ) * ε := by push_cast; ring

variable [Fintype ι]

/-- Under the Poisson word law on a finite alphabet, the expected norm of the
difference of two chronological root products whose factors differ by at most
`ε` is at most `ε |ι| t`. Source: area law, `09-amplification.tex`,
lines 228–232. -/
theorem integrable_and_integral_norm_contractionWord_sub_le (k k' : ι → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk'₀ : ∀ i, 0 ≤ k' i) {ε : ℝ}
    (hε : ∀ i, ‖CFC.sqrt (1 - k i) - CFC.sqrt (1 - k' i)‖ ≤ ε) (t : ℝ≥0) :
    Integrable (fun u : PoissonWord.Word ι =>
        ‖contractionWord k u.1 u.2 - contractionWord k' u.1 u.2‖)
      (PoissonWord.measure ι t) ∧
      (∫ u, ‖contractionWord k u.1 u.2 - contractionWord k' u.1 u.2‖
        ∂PoissonWord.measure ι t) ≤ ε * Fintype.card ι * t := by
  have hint : Integrable (fun u : PoissonWord.Word ι =>
      ‖contractionWord k u.1 u.2 - contractionWord k' u.1 u.2‖)
      (PoissonWord.measure ι t) :=
    PoissonWord.integrable_of_nonneg_le_const t _ (fun _ => norm_nonneg _) (C := 1 + 1)
      fun u => (norm_sub_le _ _).trans (add_le_add
        (norm_contractionWord_le_one k hk₀ _ _) (norm_contractionWord_le_one k' hk'₀ _ _))
  refine ⟨hint, ?_⟩
  calc (∫ u, ‖contractionWord k u.1 u.2 - contractionWord k' u.1 u.2‖
        ∂PoissonWord.measure ι t)
      ≤ ∫ u : PoissonWord.Word ι, ε * (u.1 : ℝ) ∂PoissonWord.measure ι t :=
        integral_mono hint ((PoissonWord.integrable_length t).const_mul ε)
          fun u => (norm_contractionWord_sub_le k k' hk₀ hk'₀ hε u.1 u.2).trans_eq
            (mul_comm _ _)
    _ = ε * Fintype.card ι * t := by
        rw [integral_const_mul, PoissonWord.integral_length, mul_assoc]

/-- The same estimate on the coupled realization: both products are evaluated on
the retained part of one full word, and the bound counts only retained labels.
Source: area law, `09-amplification.tex`, lines 70 and 228–232. -/
theorem integrable_and_integral_norm_contractionWord_retained_sub_le
    (P : ι → Prop) [DecidablePred P] (k k' : {i // P i} → Matrix n n ℂ)
    (hk₀ : ∀ i, 0 ≤ k i) (hk'₀ : ∀ i, 0 ≤ k' i) {ε : ℝ}
    (hε : ∀ i, ‖CFC.sqrt (1 - k i) - CFC.sqrt (1 - k' i)‖ ≤ ε) (t : ℝ≥0) :
    Integrable (fun w : PoissonWord.Word ι =>
        ‖contractionWord k (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2 -
          contractionWord k' (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2‖)
      (PoissonWord.measure ι t) ∧
      (∫ w, ‖contractionWord k (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2 -
          contractionWord k' (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2‖ ∂PoissonWord.measure ι t) ≤
        ε * Fintype.card {i // P i} * t := by
  set g : PoissonWord.Word ι → PoissonWord.Word {i // P i} :=
    fun w => (PoissonWord.partitionWords P w).1
  set f : PoissonWord.Word {i // P i} → ℝ :=
    fun u => ‖contractionWord k u.1 u.2 - contractionWord k' u.1 u.2‖
  obtain ⟨hint, hle⟩ := integrable_and_integral_norm_contractionWord_sub_le k k' hk₀ hk'₀ hε t
  have hmap : Measure.map g (PoissonWord.measure ι t) = PoissonWord.measure {i // P i} t :=
    PoissonWord.map_partitionWords_fst P t
  have hgm : AEMeasurable g (PoissonWord.measure ι t) := Measurable.of_discrete.aemeasurable
  have hfm : AEStronglyMeasurable f (Measure.map g (PoissonWord.measure ι t)) :=
    AEStronglyMeasurable.of_discrete
  have hint' : Integrable f (Measure.map g (PoissonWord.measure ι t)) := by
    rw [hmap]; exact hint
  refine ⟨(integrable_map_measure hfm hgm).mp hint', ?_⟩
  have h := integral_map (f := f) hgm hfm
  rw [hmap] at h
  change (∫ w, f (g w) ∂PoissonWord.measure ι t) ≤ _
  rw [← h]
  exact hle

end Generic

end Matrix
end
