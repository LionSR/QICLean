/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.Channel.KrausFreedom

/-!
# Unitary freedom of Kraus representations (Wolf Theorem 2.1(4) / Eq. (2.10))

This file restates the directional Kraus-freedom lemmas already proved in
`TNLean.Channel.KrausRepresentation` and `TNLean.Channel.KrausFreedom` as
iff statements matching Wolf Theorem 2.1(4) (ensemble equivalence, Eq. (2.10)).

## Main results

* `kraus_isometry_freedom_iff` — two finite Kraus families define the same
  completely positive map if and only if, after padding the smaller family with
  zeros, they are related by an isometric mixing matrix.
* `kraus_unitary_freedom_iff` — same-size Kraus families define the same map if
  and only if they are related by a unitary mixing matrix.
* `kraus_unitary_freedom_iff_of_zeroPad` — arbitrary finite Kraus families
  define the same map if and only if their zero paddings to the larger
  cardinality are related by a unitary mixing matrix.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 2.1(4) and
  Equation (2.10)][Wolf2012QChannels]
-/

open scoped Matrix
open Matrix Finset BigOperators

variable {d d' : ℕ}

namespace Kraus

/-- Pad a finite Kraus family with zero operators to a prescribed length.

For `m ≤ n`, the first `m` operators are retained and the remaining `n - m`
operators are zero. This is the zero padding in Wolf Theorem 2.1(4) and
Proposition 7.4(2). -/
def zeroPad {m n : ℕ} (A : Fin m → Matrix (Fin d') (Fin d) ℂ) :
    Fin n → Matrix (Fin d') (Fin d) ℂ := fun i =>
  if h : (i : ℕ) < m then A ⟨i, h⟩ else 0

@[simp]
theorem zeroPad_castLE {m n : ℕ} (h : m ≤ n)
    (A : Fin m → Matrix (Fin d') (Fin d) ℂ) (i : Fin m) :
    zeroPad (n := n) A (Fin.castLE h i) = A i := by
  simp [zeroPad]

/-- Zero padding a Kraus family leaves its completely positive map unchanged. -/
theorem sum_zeroPad {m n : ℕ} (h : m ≤ n)
    (A : Fin m → Matrix (Fin d') (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i : Fin n, zeroPad A i * X * (zeroPad A i)ᴴ =
      ∑ j : Fin m, A j * X * (A j)ᴴ := by
  rw [Fin.sum_castLE_extend_zero (fun j => A j * X * (A j)ᴴ) h]
  apply Finset.sum_congr rfl
  intro i _
  simp only [zeroPad]
  split_ifs <;> simp

end Kraus

/-- **Wolf Theorem 2.1(4) (isometric form)**: two finite Kraus families define the
same completely positive map if and only if, after padding the smaller family
with zeros, they are related by an isometric mixing matrix. Stated for
rectangular Kraus operators `Matrix (Fin d') (Fin d) ℂ`; the square form is
the specialization `d = d'`. -/
theorem kraus_isometry_freedom_iff
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : ι₁ → Matrix (Fin d') (Fin d) ℂ)
    (A : ι₂ → Matrix (Fin d') (Fin d) ℂ)
    (hCard : Fintype.card ι₂ ≤ Fintype.card ι₁) :
    (∀ X : Matrix (Fin d) (Fin d) ℂ,
      ∑ α, B α * X * (B α)ᴴ = ∑ j, A j * X * (A j)ᴴ) ↔
      ∃ V : Matrix ι₁ ι₂ ℂ,
        Vᴴ * V = 1 ∧
        ∀ α, B α = ∑ j, V α j • A j := by
  refine ⟨fun h => kraus_rectangular_freedom' B A h hCard, ?_⟩
  rintro ⟨V, hV, hBA⟩
  exact kraus_same_map_of_isometry_combination (K := B) (K' := A) (W := V) hV hBA

/-- **Wolf Theorem 2.1(4) (unitary form)**: if two Kraus families have the same
finite index type, then they define the same completely positive map if and only
if they are related by a unitary mixing matrix. -/
theorem kraus_unitary_freedom_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A : ι → Matrix (Fin d') (Fin d) ℂ) :
    (∀ X : Matrix (Fin d) (Fin d) ℂ,
      ∑ α, B α * X * (B α)ᴴ = ∑ j, A j * X * (A j)ᴴ) ↔
      ∃ U : Matrix.unitaryGroup ι ℂ,
        ∀ α, B α = ∑ j, (U : Matrix ι ι ℂ) α j • A j := by
  -- Both directions share the translation between `Uᴴ * U = 1` and the bundled
  -- `Matrix.unitaryGroup` predicate via `Matrix.mem_unitaryGroup_iff'`.
  rw [kraus_isometry_freedom_iff B A le_rfl]
  refine ⟨fun ⟨V, hV, hBA⟩ => ⟨⟨V, Matrix.mem_unitaryGroup_iff'.2 hV⟩, hBA⟩,
          fun ⟨U, hBA⟩ => ⟨(U : Matrix ι ι ℂ), Matrix.mem_unitaryGroup_iff'.mp U.prop, hBA⟩⟩

/-- **Wolf Theorem 2.1(4) (zero-padded unitary form)**: two finite Kraus
families define the same completely positive map if and only if, after padding
both families with zeros to the larger cardinality, the primed family is a
unitary linear combination of the unprimed family. -/
theorem kraus_unitary_freedom_iff_of_zeroPad
    {r r' : ℕ}
    (L' : Fin r' → Matrix (Fin d') (Fin d) ℂ)
    (L : Fin r → Matrix (Fin d') (Fin d) ℂ) :
    (∀ X : Matrix (Fin d) (Fin d) ℂ,
      ∑ i, L' i * X * (L' i)ᴴ = ∑ j, L j * X * (L j)ᴴ) ↔
      ∃ U : Matrix.unitaryGroup (Fin (max r r')) ℂ,
        ∀ i, Kraus.zeroPad L' i =
          ∑ j, (U : Matrix (Fin (max r r')) (Fin (max r r')) ℂ) i j •
            Kraus.zeroPad L j := by
  constructor
  · intro h
    apply (kraus_unitary_freedom_iff
      (Kraus.zeroPad (n := max r r') L')
      (Kraus.zeroPad (n := max r r') L)).mp
    intro X
    rw [Kraus.sum_zeroPad (le_max_right r r') L' X,
      Kraus.sum_zeroPad (le_max_left r r') L X, h X]
  · intro h
    have hpad := (kraus_unitary_freedom_iff
      (Kraus.zeroPad (n := max r r') L')
      (Kraus.zeroPad (n := max r r') L)).mpr h
    intro X
    rw [← Kraus.sum_zeroPad (le_max_right r r') L' X,
      ← Kraus.sum_zeroPad (le_max_left r r') L X, hpad X]
