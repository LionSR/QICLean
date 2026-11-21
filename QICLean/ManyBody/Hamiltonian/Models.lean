/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.InteractionOperations
import QICLean.ManyBody.Sites.Lattice.Line
import QICLean.ManyBody.Sites.Lattice.Plane
import QICLean.ManyBody.Sites.Lattice.Rectangle
import QICLean.ManyBody.Sites.Lattice.Ring
import QICLean.ManyBody.Sites.Lattice.Square

/-!
# The lattice models

A lattice model is a choice of sites, local dimension and supports, and its Hamiltonians are the
`ManyBody.Interaction`s for that choice. The abbreviations of this file name these choices:

* the chain of `L` sites with its supports of range `R`;
* a finite set `Λ ⊂ ℤ` with its supports of range `R` in the induced path graph;
* a finite set `Λ ⊂ ℤ × ℤ` with its supports of range `R` in the induced nearest-neighbour
  graph;
* the `width × height` square lattice with one term per vertex and one per edge, and the
  `L × L` square as its special case;
* the chain of `L` sites with one term on each bond `{i, i + 1}`.

Two maps relate the models. A bond interaction is the range-one chain interaction whose term
on the bond `{i, i + 1}` is the bond term and whose single-site terms vanish
(`ManyBody.BondInteraction.toChainInteraction`), and a rectangle interaction is the range-one
interaction on the rectangular domain of `ℤ × ℤ` whose term on the image of a vertex or an edge
is the transported term, the other terms vanishing
(`ManyBody.RectangleInteraction.toPlaneInteraction`). Both are extensions along an injection of
indices, `ManyBody.Interaction.extend`. On the ring of `N` sites, the translation-invariant
interaction of one operator on `k` consecutive sites has the translates of that operator as its
terms when `k ≤ N`, and vanishes when the window is longer than the ring
(`ManyBody.Interaction.translationInvariant`); on the open chain of `N` sites,
the translates of that operator along the windows starting at `0, …, N - k` form
`ManyBody.Interaction.chainTranslates`. A bond interaction on the first `L ≤ N` sites of a
chain of `N` sites, padded with one matrix at each added site, is a bond interaction on the `N`
sites (`ManyBody.BondInteraction.padded`).

They exist for field notation and readability; they add no structure. Hermiticity of the terms
(or only of their sum), the norm bound `J`, the range and the degree are hypotheses of the
statements that use them, and every `Interaction` lemma applies to these types as it stands.

These replace TNLean's structures `ChainHamiltonian L q R J`, `DomainHamiltonian Λ q R J`,
`Lattice.LocalHamiltonian Λ q R J`, `RectangularHamiltonian width height q J` and
`SquareHamiltonian L q J` (TNLean commit `71c1185e9352a3b5237b37a6840640751da6ca2d`): each is one
of these interactions together with the hypotheses that were its fields.

## Main definitions

* `ManyBody.ChainInteraction`, `ManyBody.DomainInteraction`, `ManyBody.PlaneInteraction`,
  `ManyBody.RectangleInteraction`, `ManyBody.SquareInteraction`, `ManyBody.BondInteraction`.
* `ManyBody.bondSupport`, `ManyBody.BondInteraction.toChainInteraction`.
* `ManyBody.BondInteraction.padded` — a bond interaction on the first `L` sites of a chain of
  `N` sites, with one matrix at each added site on the bond ending there.
* `ManyBody.RectangleInteraction.toPlaneInteraction`.
* `ManyBody.Interaction.translationInvariant`, `ManyBody.Interaction.chainTranslates`.

## Main results

* `ManyBody.BondInteraction.hamiltonian_padded` — the Hamiltonian of the padding is the
  Hamiltonian of `Φ` on the first `L` sites plus the matrices at the added sites other than
  the site `0`.

* `ManyBody.RectangleInteraction.hamiltonian_toPlaneInteraction` — the map to the plane keeps
  the Hamiltonian, transported to the configurations of the domain.
* `ManyBody.Interaction.translationInvariant_term_of_le`,
  `ManyBody.Interaction.hamiltonian_translationInvariant_of_not_le` — the terms of a
  translation-invariant interaction are the translates of the operator when the window fits in
  the ring, and the Hamiltonian vanishes when it does not.
* `ManyBody.Interaction.translationInvariant_term_add_one`,
  `ManyBody.Interaction.sitePermOp_finRotate_mul_hamiltonian_translationInvariant` — the
  rotation of the ring permutes the terms of a translation-invariant interaction and fixes its
  Hamiltonian.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, Section 1, `eq:ham`, and `part0_preamble.tex`, `eq:ham`.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Theorem 1.1, `eq:hamiltonian`, and `eq:model`.
* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `eq:model`.
* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`, lines 209–211 and 283.
* N. Schuch, D. Pérez-García, J. I. Cirac, *Classifying quantum phases using matrix product
  states and projected entangled pair states*, arXiv:1010.3732,
  `sec:phases-definition-no-sym`, lines 407–427.
-/

open scoped Matrix

namespace ManyBody

/-- The finite-range interactions on the chain of `L` sites with local dimension `q`: one term
for each support of range `R`. TNLean note, Section 1, `eq:ham`. -/
abbrev ChainInteraction (L q R : ℕ) :=
  Interaction (fun _ : Fin L ↦ Fin q) (fun X : ChainSupport L R ↦ X.1)

/-- The finite-range interactions on a finite set `Λ ⊂ ℤ` with local dimension `q`: one term
for each support of range `R` in the induced path graph. TNLean note, `part0_preamble.tex`,
`eq:ham`. -/
abbrev DomainInteraction (Λ : Finset ℤ) (q R : ℕ) :=
  Interaction (fun _ : Fin Λ.card ↦ Fin q) (fun X : DomainSupport Λ R ↦ X.1)

/-- The finite-range interactions on a finite set `Λ ⊂ ℤ × ℤ` with local dimension `q`: one term
for each support of range `R` in the induced nearest-neighbour graph. Area law, Theorem 1.1,
`eq:hamiltonian`. -/
abbrev PlaneInteraction (Λ : Finset (ℤ × ℤ)) (q R : ℕ) :=
  Interaction (fun _ : ↥Λ ↦ Fin q) (fun X : AdmissibleSupport Λ R ↦ X.1)

/-- The site-and-edge interactions on the `width × height` square lattice with local dimension
`q`: one term on each vertex and one on the two endpoints of each edge. Area law and
polynomial-PEPS, `eq:model`. -/
abbrev RectangleInteraction (width height q : ℕ) :=
  Interaction (fun _ : SquareLatticeVertex width height ↦ Fin q)
    (squareLatticeSiteOrEdgeSupport (width := width) (height := height))

/-- The site-and-edge interactions on the `L × L` square. Polynomial-PEPS, `eq:model`. -/
abbrev SquareInteraction (L q : ℕ) :=
  RectangleInteraction L L q

/-! ### Bond interactions on the chain -/

section Bond

variable {L q : ℕ}

/-- The nearest-neighbour interactions on the chain of `L` sites with local dimension `q`: one
term for each bond `{i, i + 1}`, `i < L - 1`. Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`algo53.tex`, lines 209–211. -/
abbrev BondInteraction (L q : ℕ) :=
  Interaction (fun _ : Fin L ↦ Fin q) (fun i : Fin (L - 1) ↦ interval L i.val (i.val + 2))

/-- The bond `{i, i + 1}` of the chain of `L` sites as a support of range one. -/
def bondSupport (i : Fin (L - 1)) : ChainSupport L 1 :=
  ⟨interval L i.val (i.val + 2), ⟨⟨i.val, by omega⟩, mem_interval.mpr ⟨le_rfl, by simp⟩⟩,
    fun x hx y hy ↦ by
      rw [mem_interval] at hx hy
      omega⟩

/-- Distinct bonds are distinct supports. -/
theorem bondSupport_injective : Function.Injective (bondSupport (L := L)) := by
  intro i j hij
  have hi : (⟨i.val, by omega⟩ : Fin L) ∈ (bondSupport j).1 := by
    rw [← hij]
    exact mem_interval.mpr ⟨le_rfl, by simp⟩
  have hj : (⟨j.val, by omega⟩ : Fin L) ∈ (bondSupport i).1 := by
    rw [hij]
    exact mem_interval.mpr ⟨le_rfl, by simp⟩
  simp only [bondSupport, mem_interval] at hi hj
  exact Fin.ext (by omega)

/-- **A bond interaction as a range-one chain interaction.** The term on the support
`{i, i + 1}` is the bond term with index `i`, and the terms on all other supports of range one,
the single sites among them, vanish. It is the extension of the bond interaction along the
injection `bondSupport`, so the lemmas on `ManyBody.Interaction.extend` give its terms and its
Hamiltonian, which is the Hamiltonian of the bond interaction. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 209–211 and 283. -/
noncomputable abbrev BondInteraction.toChainInteraction (Φ : BondInteraction L q) :
    ChainInteraction L q 1 :=
  Φ.extend bondSupport bondSupport_injective (fun X ↦ X.1) fun _ ↦ subset_rfl

/-- On the chain of `N + 1` sites, the bond term with index `i : Fin N` is supported on the
bond `{i, i + 1}`. -/
theorem BondInteraction.term_mem_supportedOperators_chainBond {N : ℕ}
    (Φ : BondInteraction (N + 1) q) (i : Fin N) :
    Φ.term i ∈ supportedOperators (fun _ : Fin (N + 1) ↦ Fin q) (chainBond N i) :=
  interval_eq_chainBond i ▸ Φ.mem i

end Bond

/-! ### Padding a bond interaction -/

section Padded

open scoped MatrixOrder ComplexOrder

variable {L N q : ℕ}

/-- **Padding a bond interaction.** For `L ≤ N`, a bond interaction `Φ` on the chain of `L`
sites and a matrix `p v` on the basis at every site `v`, the bond interaction on the chain of
`N` sites whose bond `j < L - 1` carries the term of `Φ` with index `j` placed on the first `L`
sites, and whose bond `{j, j + 1}`, for `j ≥ L - 1`, carries `p (j + 1)` at the site `j + 1`.
For `L ≥ 1` these are the bonds `{v - 1, v}` of the sites `v ≥ L`, so its Hamiltonian is the
Hamiltonian of `Φ` on the first `L` sites plus the matrices `p v` at the added sites; for
`L = 0` it is the sum of the matrices `p v` at the sites `v ≥ 1`, the site `0` lying on no bond
`{v - 1, v}`. Landau, Vazirani and Vidick, arXiv:1307.5143v1, final induction,
lines 652–678, with `p v` the penalty for leaving a reference basis state. -/
noncomputable def BondInteraction.padded (hi : L ≤ N) (Φ : BondInteraction L q)
    (p : Fin N → Matrix (Fin q) (Fin q) ℂ) : BondInteraction N q where
  term j := if hj : j.val < L - 1 then
      placeAlong (X := fun _ : Fin N ↦ Fin q) (Fin.castLEEmb hi) (Φ.term ⟨j.val, hj⟩)
    else placeAt (X := fun _ : Fin N ↦ Fin q) ⟨j.val + 1, by omega⟩ (p ⟨j.val + 1, by omega⟩)
  mem j := by
    by_cases hj : j.val < L - 1
    · rw [dite_eq_left hj]
      refine supportedOperators_mono (fun v hv ↦ ?_)
        (placeAlong_mem_supportedOperators_map (X := fun _ : Fin N ↦ Fin q) (Fin.castLEEmb hi)
          (Φ.mem ⟨j.val, hj⟩))
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
      simpa using mem_interval.mp hu
    · rw [dite_eq_right hj]
      refine supportedOperators_mono (fun v hv ↦ ?_) (placeAt_mem_supportedOperators _ _)
      rw [Finset.mem_singleton.mp hv, mem_interval]
      simp only
      omega

variable {hi : L ≤ N} {Φ : BondInteraction L q} {p : Fin N → Matrix (Fin q) (Fin q) ℂ}

/-- The term of the padded interaction on a bond `j < L - 1` is the term of `Φ` with index `j`,
placed on the first `L` sites. -/
theorem BondInteraction.padded_term_of_lt {j : Fin (N - 1)} (hj : j.val < L - 1) :
    (Φ.padded hi p).term j = placeAlong (Fin.castLEEmb hi) (Φ.term ⟨j.val, hj⟩) := by
  simp only [padded, dite_eq_left hj]

/-- The term of the padded interaction on a bond `j ≥ L - 1` is `p` at the site `j + 1`. -/
theorem BondInteraction.padded_term_of_le {j : Fin (N - 1)} (hj : L - 1 ≤ j.val) :
    (Φ.padded hi p).term j =
      placeAt (X := fun _ : Fin N ↦ Fin q) ⟨j.val + 1, by omega⟩ (p ⟨j.val + 1, by omega⟩) :=
  dite_eq_right (not_lt.mpr hj)

/-- A property of operators that holds for every term of `Φ` placed on the first `L` sites and
for every matrix `p v` placed at its site holds for every term of the padded interaction. -/
theorem BondInteraction.forall_padded_term {P : Matrix (Fin N → Fin q) (Fin N → Fin q) ℂ → Prop}
    (hΦ : ∀ i, P (placeAlong (Fin.castLEEmb hi) (Φ.term i)))
    (hp : ∀ v, P (placeAt (X := fun _ : Fin N ↦ Fin q) v (p v))) (j : Fin (N - 1)) :
    P ((Φ.padded hi p).term j) := by
  by_cases hj : j.val < L - 1
  · rw [padded_term_of_lt hj]
    exact hΦ _
  · rw [padded_term_of_le (not_lt.mp hj)]
    exact hp _

/-- **The Hamiltonian of the padded interaction** is the Hamiltonian of `Φ` placed on the first
`L` sites plus the matrices `p v` at the sites `v ≥ max L 1`. -/
theorem BondInteraction.hamiltonian_padded :
    (Φ.padded hi p).hamiltonian = placeAlong (Fin.castLEEmb hi) Φ.hamiltonian +
      ∑ v : Fin N with max L 1 ≤ v.val, placeAt (X := fun _ : Fin N ↦ Fin q) v (p v) := by
  rw [Interaction.hamiltonian, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin (N - 1) ↦ j.val < L - 1), Interaction.hamiltonian, placeAlong_sum]
  congr 1
  · refine Finset.sum_bij' (fun j hj ↦ ⟨j.val, (Finset.mem_filter.mp hj).2⟩)
      (fun i _ ↦ ⟨i.val, by omega⟩) (fun _ _ ↦ Finset.mem_univ _)
      (fun i _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) fun j hj ↦ padded_term_of_lt (Finset.mem_filter.mp hj).2
  · refine Finset.sum_bij' (fun j _ ↦ ⟨j.val + 1, by omega⟩)
      (fun v hv ↦ ⟨v.val - 1, by have := (Finset.mem_filter.mp hv).2; omega⟩)
      (fun j hj ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        have := (Finset.mem_filter.mp hj).2; simp only; omega⟩)
      (fun v hv ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        have := (Finset.mem_filter.mp hv).2; simp only; omega⟩)
      (fun _ _ ↦ Fin.ext (by simp))
      (fun v hv ↦ Fin.ext (by have := (Finset.mem_filter.mp hv).2; simp only; omega))
      fun j hj ↦ padded_term_of_le (not_lt.mp (Finset.mem_filter.mp hj).2)

/-- The padding of positive terms by positive matrices has positive terms. -/
theorem BondInteraction.padded_term_nonneg (hΦ : ∀ i, 0 ≤ Φ.term i) (hp : ∀ v, 0 ≤ p v)
    (j : Fin (N - 1)) : 0 ≤ (Φ.padded hi p).term j :=
  forall_padded_term
    (fun i ↦ (posSemidef_placeAlong (X := fun _ : Fin N ↦ Fin q) (Fin.castLEEmb hi)
      (Matrix.nonneg_iff_posSemidef.mp (hΦ i))).nonneg)
    (fun v ↦ (posSemidef_placeAt (X := fun _ : Fin N ↦ Fin q)
      (Matrix.nonneg_iff_posSemidef.mp (hp v))).nonneg) j

/-- The padding of terms bounded by the identity by matrices bounded by the identity has terms
bounded by the identity. -/
theorem BondInteraction.padded_term_le_one (hΦ : ∀ i, Φ.term i ≤ 1) (hp : ∀ v, p v ≤ 1)
    (j : Fin (N - 1)) : (Φ.padded hi p).term j ≤ 1 :=
  forall_padded_term (P := fun M ↦ M ≤ 1)
    (fun i ↦ by
      rw [← placeAlong_one (X := fun _ : Fin N ↦ Fin q) (Fin.castLEEmb hi)]
      exact placeAlong_le_placeAlong (X := fun _ : Fin N ↦ Fin q) (Fin.castLEEmb hi) (hΦ i))
    (fun v ↦ by
      rw [← placeAt_one (X := fun _ : Fin N ↦ Fin q) v]
      exact placeAt_le_placeAt (X := fun _ : Fin N ↦ Fin q) (hp v)) j

/-- The padding of Hermitian terms by Hermitian matrices has Hermitian terms. -/
theorem BondInteraction.isHermitian_padded_term (hΦ : ∀ i, (Φ.term i).IsHermitian)
    (hp : ∀ v, (p v).IsHermitian) (j : Fin (N - 1)) : ((Φ.padded hi p).term j).IsHermitian :=
  forall_padded_term (fun i ↦ isHermitian_placeAlong (X := fun _ : Fin N ↦ Fin q) _ (hΦ i))
    (fun v ↦ isHermitian_placeAt (X := fun _ : Fin N ↦ Fin q) (hp v)) j

end Padded

/-! ### Translation-invariant interactions on the ring -/

section Ring

open Fin.CommRing

variable {k : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

/-- **The translation-invariant interaction on the ring** of `N` sites of one operator `h` on
`k` consecutive sites: for `k ≤ N` its term with index `i` is `h` placed on the window of `k`
consecutive sites starting at `i` (`ManyBody.Interaction.translationInvariant_term_of_le`), and
for `k > N`, when the window does not fit in the ring, every term vanishes. The term with index
`i` is supported on the sites `i + j`, `j < k`, which for `k ≤ N` form that window
(`ManyBody.map_ringWindow`) and for `k = 2` the bond `{i, i + 1}`
(`ManyBody.image_range_two_add`). Schuch, Pérez-García and Cirac, arXiv:1010.3732,
`sec:phases-definition-no-sym`, lines 407–427. -/
noncomputable def Interaction.translationInvariant (N : ℕ) [NeZero N]
    (h : Matrix (Fin k → α) (Fin k → α) ℂ) :
    Interaction (fun _ : Fin N ↦ α)
      (fun i ↦ (Finset.range k).image fun j : ℕ ↦ i + (j : Fin N)) where
  term i := if hk : k ≤ N then placeAlong (X := fun _ ↦ α) (ringWindow hk i) h else 0
  mem i := by
    by_cases hk : k ≤ N
    · rw [dite_eq_left hk, ← map_ringWindow hk]
      exact placeAlong_mem_supportedOperators (X := fun _ ↦ α) _ h
    · rw [dite_eq_right hk]
      exact zero_mem _

variable {N : ℕ} [NeZero N] (h : Matrix (Fin k → α) (Fin k → α) ℂ)

namespace Interaction

/-- For `k ≤ N`, the term with index `i` is `h` placed on the window starting at `i`. -/
theorem translationInvariant_term_of_le (hk : k ≤ N) (i : Fin N) :
    (translationInvariant N h).term i = placeAlong (X := fun _ ↦ α) (ringWindow hk i) h :=
  dite_eq_left hk

/-- For `k > N`, every term vanishes. -/
theorem translationInvariant_term_of_not_le (hk : ¬ k ≤ N) (i : Fin N) :
    (translationInvariant N h).term i = 0 :=
  dite_eq_right hk

/-- For `k ≤ N`, the Hamiltonian is the sum of the placements of `h` on the windows of `k`
consecutive sites. -/
theorem hamiltonian_translationInvariant_of_le (hk : k ≤ N) :
    (translationInvariant N h).hamiltonian =
      ∑ i, placeAlong (X := fun _ ↦ α) (ringWindow hk i) h :=
  Finset.sum_congr rfl fun i _ ↦ translationInvariant_term_of_le h hk i

/-- For `k > N`, the Hamiltonian vanishes. -/
theorem hamiltonian_translationInvariant_of_not_le (hk : ¬ k ≤ N) :
    (translationInvariant N h).hamiltonian = 0 :=
  Finset.sum_eq_zero fun i _ ↦ translationInvariant_term_of_not_le h hk i

variable {h} in
/-- A property of operators that holds for zero and for `h` placed on every window of `k ≤ N`
consecutive sites holds for every term. -/
theorem forall_translationInvariant_term {P : Matrix (Fin N → α) (Fin N → α) ℂ → Prop}
    (h0 : P 0) (hP : ∀ (hk : k ≤ N) i, P (placeAlong (X := fun _ ↦ α) (ringWindow hk i) h))
    (i : Fin N) : P ((translationInvariant N h).term i) := by
  by_cases hk : k ≤ N
  · rw [translationInvariant_term_of_le h hk]
    exact hP hk i
  · rw [translationInvariant_term_of_not_le h hk]
    exact h0

open scoped Matrix.Norms.L2Operator in
/-- Every term has at most the norm of `h`. -/
theorem norm_translationInvariant_term_le (i : Fin N) :
    ‖(translationInvariant N h).term i‖ ≤ ‖h‖ :=
  forall_translationInvariant_term (P := fun M ↦ ‖M‖ ≤ ‖h‖) (norm_zero.trans_le (norm_nonneg h))
    (fun hk i ↦ norm_placeAlong_le (X := fun _ ↦ α) (ringWindow hk i) h) i

variable {h}

/-- The terms of a Hermitian operator are Hermitian. -/
theorem isHermitian_translationInvariant_term (hh : h.IsHermitian) (i : Fin N) :
    ((translationInvariant N h).term i).IsHermitian :=
  forall_translationInvariant_term Matrix.isHermitian_zero
    (fun hk i ↦ isHermitian_placeAlong (X := fun _ ↦ α) (ringWindow hk i) hh) i

open scoped MatrixOrder ComplexOrder in
/-- The terms of a positive operator are positive. -/
theorem translationInvariant_term_nonneg (hh : 0 ≤ h) (i : Fin N) :
    0 ≤ (translationInvariant N h).term i :=
  forall_translationInvariant_term le_rfl (fun hk i ↦
    (posSemidef_placeAlong (X := fun _ ↦ α) (ringWindow hk i)
      (Matrix.nonneg_iff_posSemidef.mp hh)).nonneg) i

open scoped MatrixOrder ComplexOrder in
/-- The terms of an operator bounded by the identity are bounded by the identity. -/
theorem translationInvariant_term_le_one (hh : h ≤ 1) (i : Fin N) :
    (translationInvariant N h).term i ≤ 1 :=
  forall_translationInvariant_term (P := fun M ↦ M ≤ 1) zero_le_one (fun hk i ↦ by
    rw [← placeAlong_one (X := fun _ ↦ α) (ringWindow hk i)]
    exact placeAlong_le_placeAlong (X := fun _ ↦ α) (ringWindow hk i) hh) i

variable (h)

/-- **Rotating the terms.** Conjugating the term with index `i` by the rotation `j ↦ j + 1` of
the ring gives the term with index `i + 1`. -/
theorem translationInvariant_term_add_one (i : Fin N) :
    (translationInvariant N h).term (i + 1) =
      sitePermOp (finRotate N) * (translationInvariant N h).term i *
        (sitePermOp (finRotate N))ᴴ := by
  by_cases hk : k ≤ N
  · simp only [translationInvariant_term_of_le h hk, sitePermOp_mul_placeAlong_mul_conjTranspose,
      ringWindow_trans_finRotate]
  · simp only [translationInvariant_term_of_not_le h hk, Matrix.mul_zero, Matrix.zero_mul]

/-- **Translation invariance.** The Hamiltonian of a translation-invariant interaction on the ring
commutes with the rotation of the ring: conjugating it by the rotation leaves it unchanged. -/
theorem sitePermOp_finRotate_mul_hamiltonian_translationInvariant :
    sitePermOp (finRotate N) * (translationInvariant N h).hamiltonian *
        (sitePermOp (finRotate N))ᴴ = (translationInvariant N h).hamiltonian := by
  simp only [hamiltonian, Finset.mul_sum, Finset.sum_mul,
    ← Interaction.translationInvariant_term_add_one]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ ↦ rfl

end Interaction

end Ring

/-! ### Translates on the open chain -/

section Chain

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The translates on the open chain** of `N` sites of one operator `h` on `k` consecutive
sites: its term with index `i`, for the positions `i = 0, …, N - k`, is `h` placed on the window
of `k` consecutive sites starting at `i`, the interval `[i, i + k)` (`ManyBody.map_chainWindow`).
Its Hamiltonian is the open-boundary Hamiltonian `∑_{i ≤ N - k} hᵢ,ᵢ₊ₖ₋₁` of one local term.
LVV, arXiv:1307.5143v1, `algo53.tex`, lines 209–211. -/
noncomputable abbrev Interaction.chainTranslates (k N : ℕ)
    (h : Matrix (Fin k → α) (Fin k → α) ℂ) :
    Interaction (fun _ : Fin N ↦ α) (fun i : Fin (N + 1 - k) ↦
      Finset.univ.map (chainWindow (N := N) (k := k) i.val (by omega))) :=
  Interaction.translates (fun i : Fin (N + 1 - k) ↦
    chainWindow (N := N) (k := k) i.val (by omega)) h

end Chain

/-! ### Rectangle interactions on the plane -/

namespace RectangleInteraction

variable {width height q : ℕ}

/-- **A rectangle interaction as a range-one interaction on its domain of the plane.** The term
on the image of a vertex or an edge is its term, transported along the identification of the
vertices with the sites of the rectangular domain, and the terms on all other supports of
range one vanish. It is the relabelling of the sites followed by the extension along the
injection `rectangleSupport`. Area law, Corollary 1.2, and polynomial-PEPS, `eq:model`. -/
noncomputable abbrev toPlaneInteraction (Φ : RectangleInteraction width height q) :
    PlaneInteraction (rectangularDomain width height) q 1 :=
  (Φ.relabel (rectangleSiteEquiv width height) (fun _ ↦ Equiv.refl _)
      (fun i ↦ (rectangleSupport i).1) fun i v ↦ (mem_rectangleSupport_iff i v).symm).extend
    rectangleSupport (rectangleSupport_injective width height) (fun X ↦ X.1) fun _ ↦ subset_rfl

/-- The map to the plane keeps the Hamiltonian, transported to the configurations of the
rectangular domain. Area law, Corollary 1.2. -/
theorem hamiltonian_toPlaneInteraction (Φ : RectangleInteraction width height q) :
    Φ.toPlaneInteraction.hamiltonian =
      Matrix.reindex (siteConfigurationEquiv (rectangleSiteEquiv width height)
          fun _ ↦ Equiv.refl (Fin q))
        (siteConfigurationEquiv (rectangleSiteEquiv width height) fun _ ↦ Equiv.refl (Fin q))
        Φ.hamiltonian := by
  rw [Interaction.hamiltonian_extend, Interaction.hamiltonian_relabel]

end RectangleInteraction

end ManyBody
