/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# A finite sum separated by two windows

Two disjoint windows of length `2 * ℓ` divide a finite array into five
consecutive parts. The sum over the array is the sum over these parts,
including empty windows or empty complementary intervals. For a finite
index type `Fin N`, every shifted index is derived from the two
window-admissibility inequalities.

This is the additive identity supporting ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821. No commutation of operator products is used.

Moved from TNLean, `TNLean/Algebra/TwoWindowSum.lean` at commit `49b78ed821` (Apache-2.0).

Moved from TNLean, `TNLean/Algebra/TwoWindowFamily.lean` at commit `021ba0bd19` (Apache-2.0).
-/

open scoped BigOperators

/-- Decomposition of a finite sum over an interval into two windows and their three
complements. This is the additive identity underlying ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. The two windows
are required to lie in the finite interval. Empty complementary
intervals and windows of length zero are allowed. -/
theorem Finset.sum_range_eq_five_parts_of_two_windows
    {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    (a b ℓ N : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N) :
    (∑ t ∈ Finset.range N, f t) =
      (∑ t ∈ Finset.range a, f t) +
      (∑ r ∈ Finset.range (2 * ℓ), f (a + r)) +
      (∑ r ∈ Finset.range (b - (a + 2 * ℓ)), f (a + 2 * ℓ + r)) +
      (∑ r ∈ Finset.range (2 * ℓ), f (b + r)) +
      (∑ r ∈ Finset.range (N - (b + 2 * ℓ)), f (b + 2 * ℓ + r)) := by
  have hlast : (∑ t ∈ Finset.range N, f t) =
      (∑ t ∈ Finset.range (b + 2 * ℓ), f t) +
      ∑ r ∈ Finset.range (N - (b + 2 * ℓ)), f (b + 2 * ℓ + r) := by
    simpa only [Nat.add_sub_of_le hbN] using
      Finset.sum_range_add f (b + 2 * ℓ) (N - (b + 2 * ℓ))
  have hmiddle : (∑ t ∈ Finset.range b, f t) =
      (∑ t ∈ Finset.range (a + 2 * ℓ), f t) +
      ∑ r ∈ Finset.range (b - (a + 2 * ℓ)), f (a + 2 * ℓ + r) := by
    simpa only [Nat.add_sub_of_le hab] using
      Finset.sum_range_add f (a + 2 * ℓ) (b - (a + 2 * ℓ))
  rw [hlast, Finset.sum_range_add f b (2 * ℓ), hmiddle,
    Finset.sum_range_add f a (2 * ℓ)]

/-- The five-part window decomposition for a finite array indexed by `Fin N`.
Supporting additive identity for ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821. All five index bounds follow from the two
window-admissibility inequalities. -/
theorem Fin.sum_univ_eq_five_parts_of_two_windows
    {A : Type*} [AddCommMonoid A] {N : ℕ} (f : Fin N → A)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N) :
    (∑ t, f t) =
      (∑ t : Fin a, f ⟨t.val, by omega⟩) +
      (∑ r : Fin (2 * ℓ), f ⟨a + r.val, by omega⟩) +
      (∑ r : Fin (b - (a + 2 * ℓ)), f ⟨a + 2 * ℓ + r.val, by omega⟩) +
      (∑ r : Fin (2 * ℓ), f ⟨b + r.val, by omega⟩) +
      (∑ r : Fin (N - (b + 2 * ℓ)), f ⟨b + 2 * ℓ + r.val, by omega⟩) := by
  classical
  let g : ℕ → A := fun t ↦ if h : t < N then f ⟨t, h⟩ else 0
  have hshift (o n : ℕ) (h : o + n ≤ N) :
      (∑ r : Fin n, f ⟨o + r.val, by omega⟩) =
        ∑ r ∈ Finset.range n, g (o + r) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [g]
    rw [dite_eq_left (by omega)]
  have htotal : (∑ t, f t) = ∑ r ∈ Finset.range N, g r := by
    simpa only [Nat.zero_add] using hshift 0 N (by omega)
  have hhead : (∑ t : Fin a, f ⟨t.val, by omega⟩) =
      ∑ r ∈ Finset.range a, g r := by
    simpa only [Nat.zero_add] using hshift 0 a (by omega)
  rw [htotal, hhead, hshift a (2 * ℓ) (by omega),
    hshift (a + 2 * ℓ) (b - (a + 2 * ℓ)) (by omega),
    hshift b (2 * ℓ) hbN, hshift (b + 2 * ℓ) (N - (b + 2 * ℓ)) (by omega)]
  exact Finset.sum_range_eq_five_parts_of_two_windows g a b ℓ N hab hbN

section

open Matrix
open scoped BigOperators

namespace Finset

/-- A finite shifted window enumerates exactly the corresponding interval
of indices. Auxiliary indexing identity for ALVV, `eq:H-mid-cut`,
lines 810–821. Empty windows and empty ambient intervals are allowed. -/
private theorem sum_fin_window_eq_filter
    {M : Type*} [AddCommMonoid M] {N : ℕ} (h : Fin N → M)
    (o n : ℕ) (hon : o + n ≤ N) :
    (∑ r : Fin n, h ⟨o + r.val, by omega⟩) =
      ∑ i ∈ (univ : Finset (Fin N)).filter
        (fun i ↦ o ≤ i.val ∧ i.val < o + n), h i := by
  classical
  refine Finset.sum_bij
    (fun r _ ↦ (⟨o + r.val, by omega⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro r _
    simp only [mem_filter, mem_univ, true_and]
    constructor <;> omega
  · intro r _ s _ hrs
    apply Fin.ext
    have heq := congrArg Fin.val hrs
    exact Nat.add_left_cancel heq
  · intro i hi
    have hip := (mem_filter.mp hi).2
    refine ⟨⟨i.val - o, by omega⟩, mem_univ _, ?_⟩
    apply Fin.ext
    change o + (i.val - o) = i.val
    omega
  · intro r _
    rfl

end Finset

namespace Fin

/-- The sums over the three complementary intervals and over the two complete
windows reproduce the sum over all `L - 1` nearest-neighbour terms. Auxiliary to ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821, and
`def:hard-trunc`, lines 873–886. Every term is retained once.
The identity includes zero-length windows. -/
theorem sum_univ_eq_actual_two_window_alphabet
    {M : Type*} [AddCommMonoid M] (L a b ell : ℕ)
    (hab : a + 2 * ell ≤ b) (hb : b + 2 * ell ≤ L - 1)
    (h : Fin (L - 1) → M) :
    let k : Fin 6 → ℕ := ![0, a + 1, a + 2 * ell, b + 1, b + 2 * ell, L]
    let A : Fin 5 → M := fun j ↦ ∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), h i
    let WL : Fin (2 * ell) → M := fun r ↦ h ⟨a + r.val, by omega⟩
    let WR : Fin (2 * ell) → M := fun r ↦ h ⟨b + r.val, by omega⟩
    (∑ i, h i) = A 0 + (∑ r, WL r) + A 2 + (∑ r, WR r) + A 4 := by
  classical
  intro k A WL WR
  change (∑ i, h i) =
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ 0 ≤ i.val ∧ i.val + 1 < a + 1), h i) +
    (∑ r : Fin (2 * ell), h ⟨a + r.val, by omega⟩) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ a + 2 * ell ≤ i.val ∧ i.val + 1 < b + 1), h i) +
    (∑ r : Fin (2 * ell), h ⟨b + r.val, by omega⟩) +
    (∑ i ∈ (Finset.univ : Finset (Fin (L - 1))).filter
      (fun i ↦ b + 2 * ell ≤ i.val ∧ i.val + 1 < L), h i)
  rw [Finset.sum_fin_window_eq_filter h a (2 * ell) (by omega),
    Finset.sum_fin_window_eq_filter h b (2 * ell) hb]
  simp only [Finset.sum_filter]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have hcover :
      (0 ≤ i.val ∧ i.val + 1 < a + 1) ∨
      (a ≤ i.val ∧ i.val < a + 2 * ell) ∨
      (a + 2 * ell ≤ i.val ∧ i.val + 1 < b + 1) ∨
      (b ≤ i.val ∧ i.val < b + 2 * ell) ∨
      (b + 2 * ell ≤ i.val ∧ i.val + 1 < L) := by omega
  rcases hcover with h0 | hL | hM | hR | h4
  all_goals simp (disch := omega) only [ite_eq_left, ite_eq_right]
  all_goals simp

end Fin

end

section TwoWindowFamily

open scoped BigOperators

/-- The two original windows and three complementary bond sums in ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. The two inequalities
ensure that the windows are disjoint and lie in the original bond array.
All original window labels and all three bulk labels are retained. -/
def Fin.twoWindowFamily
    {A : Type*} [AddCommMonoid A] {N : ℕ} (f : Fin N → A)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N) :
    ((Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) → A :=
  Sum.elim
    (Sum.elim
      (fun r ↦ f ⟨a + r.val, by omega⟩)
      (fun r ↦ f ⟨b + r.val, by omega⟩))
    ![(∑ t : Fin a, f ⟨t.val, by omega⟩),
      (∑ r : Fin (b - (a + 2 * ℓ)), f ⟨a + 2 * ℓ + r.val, by omega⟩),
      (∑ r : Fin (N - (b + 2 * ℓ)), f ⟨b + 2 * ℓ + r.val, by omega⟩)]

/-- The literal grouped family has exactly the sum of the original bond
array. This is the additive grouping in ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821; no separate Hamiltonian identity is assumed. -/
theorem Fin.sum_twoWindowFamily
    {A : Type*} [AddCommMonoid A] {N : ℕ} (f : Fin N → A)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N) :
    (∑ α, Fin.twoWindowFamily f a b ℓ hab hbN α) = ∑ t, f t := by
  rw [Fin.twoWindowFamily, Fintype.sum_sumElim, Fintype.sum_sumElim,
    Fin.sum_univ_three]
  rw [Fin.sum_univ_eq_five_parts_of_two_windows f a b ℓ hab hbN]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ac_rfl

/-- Additive maps preserve the literal two-window grouping. This is the
finite-sum compatibility used with the decomposition in ALVV,
arXiv:1602.08828v2, `eq:H-mid-cut`, lines 810–821. -/
theorem Fin.twoWindowFamily_map
    {A B : Type*} [AddCommMonoid A] [AddCommMonoid B] {N : ℕ}
    (f : Fin N → A) (φ : A →+ B)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N)
    (α : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3) :
    Fin.twoWindowFamily (fun r ↦ φ (f r)) a b ℓ hab hbN α =
      φ (Fin.twoWindowFamily f a b ℓ hab hbN α) := by
  rcases α with (r | r) | t
  · rfl
  · rfl
  · fin_cases t <;> simp [Fin.twoWindowFamily]

end TwoWindowFamily

section TwoWindowTensorForms

open scoped BigOperators Kronecker

/-- Grouping two windows preserves every ordinary three-region tensor form.
This is the additive assembly used with ALVV, arXiv:1602.08828v2,
`eq:H-mid-cut`, lines 810–821. The original ordinary identities are the
explicit hypotheses of this auxiliary; physical locality supplies them
at the application. -/
theorem Matrix.twoWindowFamily_eq_three_region_forms
    {X Y Z : Type*} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    {N : ℕ}
    (H : Fin N → Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ)
    (HL : Fin N → Matrix X X ℂ) (HM : Fin N → Matrix Y Y ℂ)
    (HR : Fin N → Matrix Z Z ℂ)
    (a b ℓ : ℕ) (hab : a + 2 * ℓ ≤ b) (hbN : b + 2 * ℓ ≤ N)
    (p s : Fin (2 * ℓ))
    (hord : ∀ r : Fin N, r.val ≠ a + p.val → r.val ≠ b + s.val →
      H r = (HL r ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ) +
        ((1 : Matrix X X ℂ) ⊗ₖ HM r) ⊗ₖ (1 : Matrix Z Z ℂ) +
        (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ HR r)
    (α : (Fin (2 * ℓ) ⊕ Fin (2 * ℓ)) ⊕ Fin 3)
    (hαL : α ≠ Sum.inl (Sum.inl p)) (hαR : α ≠ Sum.inl (Sum.inr s)) :
    Fin.twoWindowFamily H a b ℓ hab hbN α =
      (Fin.twoWindowFamily HL a b ℓ hab hbN α ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ
          (1 : Matrix Z Z ℂ) +
        ((1 : Matrix X X ℂ) ⊗ₖ Fin.twoWindowFamily HM a b ℓ hab hbN α) ⊗ₖ
          (1 : Matrix Z Z ℂ) +
        (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ
          Fin.twoWindowFamily HR a b ℓ hab hbN α := by
  classical
  let k₁ : Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ →ₗ[ℂ]
      Matrix (X × Y) (X × Y) ℂ := Matrix.kroneckerBilinear
  let k₂ : Matrix (X × Y) (X × Y) ℂ →ₗ[ℂ] Matrix Z Z ℂ →ₗ[ℂ]
      Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ := Matrix.kroneckerBilinear
  let eL := (k₂.flip (1 : Matrix Z Z ℂ)).comp (k₁.flip (1 : Matrix Y Y ℂ))
  let eM := (k₂.flip (1 : Matrix Z Z ℂ)).comp (k₁ (1 : Matrix X X ℂ))
  let eR := k₂ (1 : Matrix (X × Y) (X × Y) ℂ)
  have hsum {k : ℕ} (idx : Fin k → Fin N)
      (hu : ∀ r, (idx r).val ≠ a + p.val)
      (hv : ∀ r, (idx r).val ≠ b + s.val) :
      (∑ r, H (idx r)) =
        ((∑ r, HL (idx r)) ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ) +
          ((1 : Matrix X X ℂ) ⊗ₖ (∑ r, HM (idx r))) ⊗ₖ (1 : Matrix Z Z ℂ) +
          (1 : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ (∑ r, HR (idx r)) := by
    change (∑ r, H (idx r)) =
      eL (∑ r, HL (idx r)) + eM (∑ r, HM (idx r)) + eR (∑ r, HR (idx r))
    rw [map_sum, map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ ↦ hord (idx r) (hu r) (hv r)
  rcases α with (r | r) | t
  · have hrp : r ≠ p := fun h ↦ hαL (congrArg Sum.inl (congrArg Sum.inl h))
    exact hord ⟨a + r.val, by omega⟩
      (fun h ↦ hrp (Fin.ext (Nat.add_left_cancel h)))
      (show a + r.val ≠ b + s.val by omega)
  · exact hord ⟨b + r.val, by omega⟩
      (show b + r.val ≠ a + p.val by omega)
      (fun h ↦ hαR (congrArg Sum.inl (congrArg Sum.inr
        (Fin.ext (Nat.add_left_cancel h)))))
  · rcases t with ⟨t, ht⟩
    have hcases : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact hsum (fun r : Fin a ↦ ⟨r.val, by omega⟩)
        (fun r ↦ (show r.val ≠ a + p.val by omega))
        (fun r ↦ (show r.val ≠ b + s.val by omega))
    · exact hsum (fun r : Fin (b - (a + 2 * ℓ)) ↦
          ⟨a + 2 * ℓ + r.val, by omega⟩)
        (fun r ↦ (show a + 2 * ℓ + r.val ≠ a + p.val by omega))
        (fun r ↦ (show a + 2 * ℓ + r.val ≠ b + s.val by omega))
    · exact hsum (fun r : Fin (N - (b + 2 * ℓ)) ↦
          ⟨b + 2 * ℓ + r.val, by omega⟩)
        (fun r ↦ (show b + 2 * ℓ + r.val ≠ a + p.val by omega))
        (fun r ↦ (show b + 2 * ℓ + r.val ≠ b + s.val by omega))

end TwoWindowTensorForms
