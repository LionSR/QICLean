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
interaction of one operator on `k ≤ N` consecutive sites has the translates of that operator
as its terms (`ManyBody.Interaction.translationInvariant`); on the open chain of `N` sites,
the translates of that operator along the windows starting at `0, …, N - k` form
`ManyBody.Interaction.chainTranslates`. A bond interaction on the first `L` sites of a chain of
`N` sites, padded with one matrix at each added site, is a bond interaction on the `N` sites
(`ManyBody.BondInteraction.padded`).

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
  Hamiltonian of `Φ` on the first `L` sites plus the matrices at the added sites.

* `ManyBody.RectangleInteraction.hamiltonian_toPlaneInteraction` — the map to the plane keeps
  the Hamiltonian, transported to the configurations of the domain.
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

private theorem notMem_map_castLEEmb_iff (hi : L ≤ N) {v : Fin N} :
    v ∉ Finset.univ.map (Fin.castLEEmb hi) ↔ L ≤ v.val := by
  simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists, Fin.coe_castLEEmb,
    Fin.ext_iff, Fin.val_castLE]
  exact ⟨fun h ↦ not_lt.mp fun hv ↦ h ⟨v.val, hv⟩ rfl, fun h j hj ↦ by omega⟩

/-- The bond of the chain of `N ≥ L ≥ 1` sites that carries a term of the padded interaction:
the bond `i` for a bond `i` of the first `L` sites, and the bond `{v - 1, v}` for a site
`v ≥ L`. -/
def paddingBond (hL : 1 ≤ L) (hi : L ≤ N) :
    Fin (L - 1) ⊕ {v : Fin N // v ∉ Finset.univ.map (Fin.castLEEmb hi)} → Fin (N - 1)
  | .inl i => ⟨i.val, by omega⟩
  | .inr v => ⟨v.1.val - 1, by have := (notMem_map_castLEEmb_iff hi).mp v.2; omega⟩

theorem paddingBond_injective (hL : 1 ≤ L) (hi : L ≤ N) :
    Function.Injective (paddingBond hL hi) := by
  rintro (i | v) (j | w) h <;> simp only [paddingBond, Fin.ext_iff] at h
  · exact congrArg Sum.inl (Fin.ext h)
  · have := (notMem_map_castLEEmb_iff hi).mp w.2
    omega
  · have := (notMem_map_castLEEmb_iff hi).mp v.2
    omega
  · have := (notMem_map_castLEEmb_iff hi).mp v.2
    have := (notMem_map_castLEEmb_iff hi).mp w.2
    exact congrArg Sum.inr (Subtype.ext (Fin.ext (by omega)))

/-- **Padding a bond interaction.** For `1 ≤ L ≤ N`, a bond interaction `Φ` on the chain of `L`
sites and a matrix `p v` on the basis at every site `v`, the bond interaction on the chain of
`N` sites whose bond `i < L - 1` carries the term of `Φ` with index `i` on the first `L`
sites, and whose bond `{v - 1, v}`, for each site `v ≥ L`, carries `p v` at the site `v`. It is
the padding `ManyBody.Interaction.pad` of `Φ` along the first `L` sites, extended along
`paddingBond`, so its Hamiltonian is the Hamiltonian of `Φ` on the first `L` sites plus the
matrices `p v` at the added sites. Landau, Vazirani and Vidick, arXiv:1307.5143v1, final
induction, lines 652–678, with `p v` the penalty for leaving a reference basis state. -/
noncomputable def BondInteraction.padded (hL : 1 ≤ L) (hi : L ≤ N) (Φ : BondInteraction L q)
    (p : Fin N → Matrix (Fin q) (Fin q) ℂ) : BondInteraction N q :=
  (Φ.pad (X := fun _ : Fin N ↦ Fin q) (Fin.castLEEmb hi) p).extend (paddingBond hL hi)
    (paddingBond_injective hL hi) _ fun
      | .inl i => fun v hv ↦ by
          obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
          simpa [paddingBond] using mem_interval.mp hu
      | .inr v => fun u hu ↦ by
          rw [Finset.mem_singleton.mp hu]
          have := (notMem_map_castLEEmb_iff hi).mp v.2
          simp only [paddingBond, mem_interval]
          omega

variable {hL : 1 ≤ L} {hi : L ≤ N} {Φ : BondInteraction L q} {p : Fin N → Matrix (Fin q) (Fin q) ℂ}

/-- The term of the padded interaction on a bond `j < L - 1` is the term of `Φ` with index `j`,
placed on the first `L` sites. -/
theorem BondInteraction.padded_term_of_lt {j : Fin (N - 1)} (hj : j.val < L - 1) :
    (Φ.padded hL hi p).term j = placeAlong (Fin.castLEEmb hi) (Φ.term ⟨j.val, hj⟩) :=
  Interaction.extend_term_apply (f := paddingBond hL hi) (Sum.inl ⟨j.val, hj⟩)

/-- The term of the padded interaction on a bond `j ≥ L - 1` is `p` at the site `j + 1`. -/
theorem BondInteraction.padded_term_of_le {j : Fin (N - 1)} (hj : L - 1 ≤ j.val) :
    (Φ.padded hL hi p).term j =
      placeAt (X := fun _ : Fin N ↦ Fin q) ⟨j.val + 1, by omega⟩ (p ⟨j.val + 1, by omega⟩) := by
  have hv : (⟨j.val + 1, by omega⟩ : Fin N) ∉ Finset.univ.map (Fin.castLEEmb hi) :=
    (notMem_map_castLEEmb_iff hi).mpr (by simp only; omega)
  have hj' : paddingBond hL hi (.inr ⟨_, hv⟩) = j := Fin.ext (by simp [paddingBond])
  rw [← hj']
  exact Interaction.extend_term_apply (f := paddingBond hL hi) (Sum.inr ⟨_, hv⟩)

/-- **The Hamiltonian of the padded interaction** is the Hamiltonian of `Φ` placed on the first
`L` sites plus the matrices `p v` at the sites `v ≥ L`. -/
theorem BondInteraction.hamiltonian_padded :
    (Φ.padded hL hi p).hamiltonian = placeAlong (Fin.castLEEmb hi) Φ.hamiltonian +
      ∑ v : {v : Fin N // v ∉ Finset.univ.map (Fin.castLEEmb hi)},
        placeAt (X := fun _ : Fin N ↦ Fin q) v.1 (p v.1) := by
  rw [padded, Interaction.hamiltonian_extend, Interaction.hamiltonian_pad]

/-- The padding of positive terms by positive matrices has positive terms. -/
theorem BondInteraction.padded_term_nonneg (hΦ : ∀ i, 0 ≤ Φ.term i) (hp : ∀ v, 0 ≤ p v)
    (j : Fin (N - 1)) : 0 ≤ (Φ.padded hL hi p).term j :=
  Interaction.extend_term_nonneg (Interaction.pad_term_nonneg _ hΦ hp) j

/-- The padding of terms bounded by the identity by matrices bounded by the identity has terms
bounded by the identity. -/
theorem BondInteraction.padded_term_le_one (hΦ : ∀ i, Φ.term i ≤ 1) (hp : ∀ v, p v ≤ 1)
    (j : Fin (N - 1)) : (Φ.padded hL hi p).term j ≤ 1 :=
  Interaction.extend_term_le_one (Interaction.pad_term_le_one _ hΦ hp) j

/-- The padding of Hermitian terms by Hermitian matrices has Hermitian terms. -/
theorem BondInteraction.isHermitian_padded_term (hΦ : ∀ i, (Φ.term i).IsHermitian)
    (hp : ∀ v, (p v).IsHermitian) (j : Fin (N - 1)) : ((Φ.padded hL hi p).term j).IsHermitian :=
  Interaction.isHermitian_extend_term (Interaction.isHermitian_pad_term _ hΦ hp) j

end Padded

/-! ### Translation-invariant interactions on the ring -/

section Ring

variable {N k : ℕ} [NeZero N] {α : Type*} [Fintype α] [DecidableEq α]

/-- **The translation-invariant interaction on the ring** of `N` sites of one operator `h` on
`k ≤ N` consecutive sites: its term with index `i` is `h` placed on the window of `k`
consecutive sites starting at `i`. For `k = 2` these windows are the bonds `{i, i + 1}`
(`ManyBody.map_ringWindow_two`). Schuch, Pérez-García and Cirac, arXiv:1010.3732,
`sec:phases-definition-no-sym`, lines 407–427. -/
noncomputable abbrev Interaction.translationInvariant (hk : k ≤ N)
    (h : Matrix (Fin k → α) (Fin k → α) ℂ) :
    Interaction (fun _ : Fin N ↦ α) (fun i ↦ Finset.univ.map (ringWindow hk i)) :=
  Interaction.translates (ringWindow hk) h

variable (hk : k ≤ N) (h : Matrix (Fin k → α) (Fin k → α) ℂ)

/-- **Rotating the terms.** Conjugating the term with index `i` by the rotation `j ↦ j + 1` of
the ring gives the term with index `i + 1`. -/
theorem Interaction.translationInvariant_term_add_one (i : Fin N) :
    (translationInvariant hk h).term (i + 1) =
      sitePermOp (finRotate N) * (translationInvariant hk h).term i *
        (sitePermOp (finRotate N))ᴴ := by
  simp only [translationInvariant, translates_term, sitePermOp_mul_placeAlong_mul_conjTranspose,
    ringWindow_trans_finRotate]

/-- **Translation invariance.** The Hamiltonian of a translation-invariant interaction on the ring
commutes with the rotation of the ring: conjugating it by the rotation leaves it unchanged. -/
theorem Interaction.sitePermOp_finRotate_mul_hamiltonian_translationInvariant :
    sitePermOp (finRotate N) * (translationInvariant hk h).hamiltonian *
        (sitePermOp (finRotate N))ᴴ = (translationInvariant hk h).hamiltonian := by
  simp only [hamiltonian, Finset.mul_sum, Finset.sum_mul,
    ← Interaction.translationInvariant_term_add_one]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ fun _ ↦ rfl

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
