/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Sites.PlaceAlong
import QICLean.ManyBody.Sites.SitewiseProduct
import QICLean.ManyBody.Sites.Twirl
import QICLean.Spectral.Gap.DoubledSystemGap
import QICLean.Analysis.Norm.KroneckerOperatorNorm

/-!
# Operations on interactions

For an interaction `Φ = (hᵢ)_{i ∈ ι}` with supports `Sᵢ` on a system of sites `X`, this file
defines the operations that build new interactions or operators from `Φ`, each stated once for
every index type, every family of supports and every family of basis types:

* the **partial Hamiltonian** `H_s = ∑_{i ∈ s} hᵢ` of a finite set `s` of indices, supported
  on any region containing the supports of its terms;
* the **real multiple** `c Φ = (c hᵢ)ᵢ`, with the same supports;
* the **relabelling** of `Φ` along a bijection `e` of the sites and bijections of the basis
  types, with terms supported on the regions corresponding to the `Sᵢ`;
* the **extension** of `Φ` along an injection `f : ι → κ` of indices: the term at `f i` is
  `hᵢ`, and the terms at the other indices vanish;
* the **doubled interaction** `(hᵢ ⊗ 1 + 1 ⊗ hᵢ)ᵢ` on the system with basis `X v × X v` at
  every site `v`, whose Hamiltonian is the doubled Hamiltonian `H ⊗ 1 + 1 ⊗ H`;
* the **interaction of placed regional matrices** `(place Rᵢ hᵢ)ᵢ`, which every interaction is;
* the interaction **placed along an injection** `w : W ↪ V` of an interaction on the sites `W`,
  with supports the images of the supports, and its **padding** by one term at each site
  outside the image of `w`;
* the union of **two interactions on the same system**, indexed by the sum of the index types;
* the **conjugation** `(U hᵢ U†)ᵢ` by a matrix `U` that keeps every term on its support;
* the **translates** of one operator `h` on the configurations of a finite set `W` along a family
  of injections `wᵢ : W ↪ V`: the term with index `i` is `h` placed along `wᵢ`;
* the **termwise map** `(fᵢ hᵢ)ᵢ` by maps `fᵢ` that keep the supports, and two instances: the
  **restriction** to the indices with a property, whose other terms vanish, and the **range
  projections** of positive terms.

The two copies of `Φ` beside each other on the sites `V ⊕ V` are `Φ.sum Φ`
(`QICLean.ManyBody.Dynamics.InteractionSum`); the doubled interaction is the same pair of
replicas with the two copies of every site paired into one site.

These generalize TNLean's operations on the chain, domain and plane models (TNLean commit
`414a18fb88`): `ChainInteraction.termSum` (`MPS/AreaLaw/Hastings/ThreeWaySplitting.lean`) and
the sums over filters of supports `leftPart`, `bufferPart`, `rightPart`, `cutLeftPart`,
`cutBoundaryPart`; `ChainInteraction.smul` (`MPS/AreaLaw/Hastings/ProjectorFactorizationScaling`);
`ChainInteraction.doubled` and `DomainInteraction.doubled` (`MPS/AreaLaw/DoubledHamiltonian`,
`MPS/AreaLaw/DomainPartialSwap`), whose alphabet `Fin (q * q)` is the relabelling of
`Fin q × Fin q` along `finProdFinEquiv`; `DomainInteraction.toChain`
(`MPS/AreaLaw/ComponentReduction`), `ChainInteraction.ofBonds` and
`ChainInteraction.ofNearestNeighborPositive` (`MPS/AreaLaw/ViableSet/PowerProjector`,
`MPS/AreaLaw/Huang/PositiveChainHamiltonian`), each an extension along an injection of
indices; the window placements `MPOTensor.embedLocalOperator` of
`MPSTensor.interactionHamiltonian` (`MPS/Symmetry/GappedInteractionPath`); the padded chain
interaction `paddedInteraction` (`MPS/AreaLaw/ViableSet/ChainPadding`), the padding of a bond
interaction along `Fin.castLEEmb`; the regional parent Hamiltonian `regionParentHamiltonian`
(`PEPS/ParentHamiltonian/RegionParentHamiltonian`), the Hamiltonian of placed regional
matrices; and the conjugated doubled interactions `swappedDoubled` (`PEPS/Approximation/
SwappedPlaneInteraction`), the doubled interaction conjugated by `ManyBody.pairSwapOp`.

## Main definitions

* `ManyBody.Interaction.partialHamiltonian`, `ManyBody.Interaction.relabel`,
  `ManyBody.Interaction.extend`, `ManyBody.Interaction.doubled`,
  `ManyBody.Interaction.ofPlace`, `ManyBody.Interaction.pushforward`,
  `ManyBody.Interaction.pad`, `ManyBody.Interaction.append`, `ManyBody.Interaction.conj`,
  `ManyBody.Interaction.translates`, `ManyBody.Interaction.mapTerm`,
  `ManyBody.Interaction.restrict`, `ManyBody.Interaction.supportProj`, and the instance
  `SMul ℝ (ManyBody.Interaction X S)`.

## Main results

* `ManyBody.Interaction.partialHamiltonian_univ`,
  `ManyBody.Interaction.partialHamiltonian_filter_add_filter_not`,
  `ManyBody.Interaction.partialHamiltonian_mem_supportedOperators`,
  `ManyBody.Interaction.norm_partialHamiltonian_le`.
* `ManyBody.Interaction.hamiltonian_smul`, `ManyBody.Interaction.hamiltonian_relabel`,
  `ManyBody.Interaction.hamiltonian_extend`, `ManyBody.Interaction.hamiltonian_doubled`,
  `ManyBody.Interaction.hamiltonian_ofPlace`, `ManyBody.Interaction.hamiltonian_pushforward`,
  `ManyBody.Interaction.hamiltonian_pad`, `ManyBody.Interaction.hamiltonian_append`,
  `ManyBody.Interaction.hamiltonian_conj`, `ManyBody.Interaction.hamiltonian_mapTerm`,
  `ManyBody.Interaction.hamiltonian_restrict` — the Hamiltonians of the new interactions.
* `ManyBody.Interaction.hamiltonian_le_hamiltonian_supportProj`,
  `ManyBody.Interaction.hamiltonian_supportProj_mulVec_eq_zero_iff` — the range projections lie
  above the terms of norm at most one and keep the kernel of the Hamiltonian.
* `ManyBody.Interaction.exists_eq_ofPlace` — every interaction is one of placed regional
  matrices.
* Hermiticity, positivity and norm bounds of the new terms.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ManyBody

namespace Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {ι : Type*} {S : ι → Finset V}

/-! ### Partial Hamiltonians -/

section Partial

/-- The partial Hamiltonian `H_s = ∑_{i ∈ s} hᵢ` of a finite set `s` of indices. Hastings,
arXiv:0705.2024v4, `law16.tex`, lines 775–778. -/
noncomputable def partialHamiltonian (Φ : Interaction X S) (s : Finset ι) :
    Matrix (Config X) (Config X) ℂ :=
  ∑ i ∈ s, Φ.term i

variable (Φ : Interaction X S)

/-- The partial Hamiltonian of the empty set of indices vanishes. -/
@[simp]
theorem partialHamiltonian_empty : Φ.partialHamiltonian ∅ = 0 :=
  Finset.sum_empty

/-- The partial Hamiltonian of all indices is the Hamiltonian. -/
@[simp]
theorem partialHamiltonian_univ [Fintype ι] : Φ.partialHamiltonian Finset.univ = Φ.hamiltonian :=
  rfl

/-- The Hamiltonian is the sum of the partial Hamiltonians of the indices with a property and of
those without it. -/
theorem partialHamiltonian_filter_add_filter_not [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    Φ.partialHamiltonian (Finset.univ.filter p) +
        Φ.partialHamiltonian (Finset.univ.filter fun i ↦ ¬ p i) = Φ.hamiltonian :=
  Finset.sum_filter_add_sum_filter_not _ _ _

/-- A partial Hamiltonian of terms supported in `D` is supported on `D`. -/
theorem partialHamiltonian_mem_supportedOperators {s : Finset ι} {D : Finset V}
    (hs : ∀ i ∈ s, S i ⊆ D) : Φ.partialHamiltonian s ∈ supportedOperators X D :=
  sum_mem fun i hi ↦ supportedOperators_mono (hs i hi) (Φ.mem i)

variable {Φ}

/-- A partial Hamiltonian of Hermitian terms is Hermitian. -/
theorem isHermitian_partialHamiltonian {s : Finset ι}
    (hΦ : ∀ i ∈ s, (Φ.term i).IsHermitian) : (Φ.partialHamiltonian s).IsHermitian :=
  (isSelfAdjoint_sum s fun i hi ↦ (hΦ i hi).isSelfAdjoint).isHermitian

/-- A partial Hamiltonian of `|s|` terms of norm at most `J` has norm at most `|s| J`. -/
theorem norm_partialHamiltonian_le {s : Finset ι} {J : ℝ} (hΦ : ∀ i ∈ s, ‖Φ.term i‖ ≤ J) :
    ‖Φ.partialHamiltonian s‖ ≤ s.card * J := by
  refine (norm_sum_le _ _).trans ?_
  simpa using Finset.sum_le_card_nsmul s _ _ hΦ

end Partial

/-! ### Real multiples -/

section Smul

/-- The real multiple `c Φ = (c hᵢ)ᵢ` of an interaction, with the same supports. -/
noncomputable instance : SMul ℝ (Interaction X S) :=
  ⟨fun c Φ ↦ ⟨fun i ↦ c • Φ.term i, fun i ↦ by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c (Φ.term i)]
    exact (supportedOperators X (S i)).smul_mem (Φ.mem i) (c : ℂ)⟩⟩

variable (c : ℝ) (Φ : Interaction X S)

@[simp]
theorem smul_term (i : ι) : (c • Φ).term i = c • Φ.term i :=
  rfl

/-- The Hamiltonian of `c Φ` is `c H`. -/
theorem hamiltonian_smul [Fintype ι] : (c • Φ).hamiltonian = c • Φ.hamiltonian :=
  (Finset.smul_sum ..).symm

variable {Φ}

/-- Real multiples of Hermitian terms are Hermitian. -/
theorem isHermitian_smul_term {i : ι} (hΦ : (Φ.term i).IsHermitian) :
    ((c • Φ).term i).IsHermitian :=
  hΦ.smul (IsSelfAdjoint.all c)

variable (Φ) in
/-- The terms of `c Φ` have norm `|c| ‖hᵢ‖`. -/
theorem norm_smul_term (i : ι) : ‖(c • Φ).term i‖ = |c| * ‖Φ.term i‖ := by
  rw [smul_term, RCLike.real_smul_eq_coe_smul (K := ℂ), norm_smul, RCLike.norm_ofReal]

end Smul

/-! ### Relabelling sites and basis labels -/

section Relabel

variable {V' : Type*} [Fintype V'] [DecidableEq V'] {X' : V' → Type*} [∀ v, Fintype (X' v)]
  [∀ v, DecidableEq (X' v)]

/-- The relabelling of an interaction along a bijection `e` of the sites and bijections `f v` of
the basis labels: its terms are the terms of `Φ` in the transported configuration basis, and the
term with index `i` is supported on any region `T i` that corresponds to `S i` under `e`. -/
def relabel (Φ : Interaction X S) (e : V ≃ V') (f : ∀ v, X v ≃ X' (e v)) (T : ι → Finset V')
    (hT : ∀ i v, v ∈ S i ↔ e v ∈ T i) : Interaction X' T where
  term i := reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f) (Φ.term i)
  mem i := reindex_siteConfigurationEquiv_mem_supportedOperators e f (hT i) (Φ.mem i)

variable (Φ : Interaction X S) (e : V ≃ V') (f : ∀ v, X v ≃ X' (e v)) (T : ι → Finset V')
  (hT : ∀ i v, v ∈ S i ↔ e v ∈ T i)

@[simp]
theorem relabel_term (i : ι) :
    (Φ.relabel e f T hT).term i =
      reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f) (Φ.term i) :=
  rfl

/-- The Hamiltonian of the relabelled interaction is the relabelled Hamiltonian. -/
theorem hamiltonian_relabel [Fintype ι] :
    (Φ.relabel e f T hT).hamiltonian =
      reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f) Φ.hamiltonian := by
  ext σ τ
  simp [hamiltonian, Matrix.sum_apply]

/-- The relabelled terms have the norms of the original terms. -/
theorem norm_relabel_term (i : ι) : ‖(Φ.relabel e f T hT).term i‖ = ‖Φ.term i‖ :=
  Matrix.l2_opNorm_reindex_equiv _ _

variable {Φ} in
/-- The relabelled terms of Hermitian terms are Hermitian. -/
theorem isHermitian_relabel_term {i : ι} (hΦ : (Φ.term i).IsHermitian) :
    ((Φ.relabel e f T hT).term i).IsHermitian :=
  hΦ.reindex _

end Relabel

/-! ### Extension along an injection of indices -/

section Extend

variable {κ : Type*}

/-- The extension of an interaction along an injection `f : ι → κ` of indices: the term with
index `f i` is `hᵢ`, supported on any region `T (f i)` containing `S i`, and the terms with the
other indices vanish. -/
noncomputable def extend (Φ : Interaction X S) (f : ι → κ) (hf : f.Injective)
    (T : κ → Finset V) (hT : ∀ i, S i ⊆ T (f i)) : Interaction X T where
  term := Function.extend f Φ.term 0
  mem k := by
    by_cases hk : ∃ i, f i = k
    · obtain ⟨i, rfl⟩ := hk
      rw [hf.extend_apply]
      exact supportedOperators_mono (hT i) (Φ.mem i)
    · rw [Function.extend_apply' _ _ _ hk]
      exact zero_mem _

variable {Φ : Interaction X S} {f : ι → κ} {hf : f.Injective} {T : κ → Finset V}
  {hT : ∀ i, S i ⊆ T (f i)}

@[simp]
theorem extend_term_apply (i : ι) : (Φ.extend f hf T hT).term (f i) = Φ.term i :=
  hf.extend_apply _ _ i

/-- The terms of the extension with indices outside the range of `f` vanish. -/
theorem extend_term_eq_zero {k : κ} (hk : ∀ i, f i ≠ k) : (Φ.extend f hf T hT).term k = 0 :=
  Function.extend_apply' _ _ _ (not_exists.mpr hk)

/-- A property of operators that holds for zero and for every term of `Φ` holds for every term
of its extension. -/
theorem forall_extend_term {P : Matrix (Config X) (Config X) ℂ → Prop} (h0 : P 0)
    (hΦ : ∀ i, P (Φ.term i)) (k : κ) : P ((Φ.extend f hf T hT).term k) := by
  by_cases hk : ∃ i, f i = k
  · obtain ⟨i, rfl⟩ := hk
    simpa using hΦ i
  · rw [extend_term_eq_zero (not_exists.mp hk)]
    exact h0

/-- The extension has the Hamiltonian of `Φ`. -/
theorem hamiltonian_extend [Fintype ι] [Fintype κ] :
    (Φ.extend f hf T hT).hamiltonian = Φ.hamiltonian :=
  Finset.sum_extend_zero_of_injective Φ.term hf fun _ ↦ Finset.mem_univ _

/-- The extension of Hermitian terms has Hermitian terms. -/
theorem isHermitian_extend_term (hΦ : ∀ i, (Φ.term i).IsHermitian) (k : κ) :
    ((Φ.extend f hf T hT).term k).IsHermitian :=
  forall_extend_term isHermitian_zero hΦ k

/-- The extension keeps a nonnegative bound `J` on the norms of the terms. -/
theorem norm_extend_term_le {J : ℝ} (hJ : 0 ≤ J) (hΦ : ∀ i, ‖Φ.term i‖ ≤ J) (k : κ) :
    ‖(Φ.extend f hf T hT).term k‖ ≤ J :=
  forall_extend_term (P := fun M ↦ ‖M‖ ≤ J) (norm_zero.trans_le hJ) hΦ k

/-- The extension of positive terms has positive terms. -/
theorem extend_term_nonneg (hΦ : ∀ i, 0 ≤ Φ.term i) (k : κ) : 0 ≤ (Φ.extend f hf T hT).term k :=
  forall_extend_term le_rfl hΦ k

/-- The extension of terms bounded by the identity has terms bounded by the identity. -/
theorem extend_term_le_one (hΦ : ∀ i, Φ.term i ≤ 1) (k : κ) : (Φ.extend f hf T hT).term k ≤ 1 :=
  forall_extend_term (P := fun M ↦ M ≤ 1) zero_le_one hΦ k

end Extend

/-! ### The doubled interaction -/

section Doubled

/-- **The doubled interaction.** The terms `hᵢ ⊗ 1 + 1 ⊗ hᵢ` of two replicas of `Φ`, on the
system with basis `X v × X v` at every site `v`, with the supports of `Φ`. TNLean note,
`part2a_mps_information.tex`, lines 355–360. -/
noncomputable def doubled (Φ : Interaction X S) : Interaction (fun v ↦ X v × X v) S where
  term i := reindex (Equiv.arrowProdEquivProdArrow V X X).symm
    (Equiv.arrowProdEquivProdArrow V X X).symm (doubledHamiltonian (Φ.term i))
  mem i := by
    rw [doubledHamiltonian, reindex_apply, submatrix_add, ← Finset.union_self (S i)]
    exact add_mem (reindex_kronecker_mem_supportedOperators (Φ.mem i) (one_mem _))
      (reindex_kronecker_mem_supportedOperators (one_mem _) (Φ.mem i))

variable (Φ : Interaction X S)

/-- The doubled term with index `i` is `hᵢ ⊗ 1 + 1 ⊗ hᵢ`, with the two copies of every site
paired. -/
theorem doubled_term (i : ι) :
    Φ.doubled.term i = reindex (Equiv.arrowProdEquivProdArrow V X X).symm
      (Equiv.arrowProdEquivProdArrow V X X).symm (doubledHamiltonian (Φ.term i)) :=
  rfl

/-- The Hamiltonian of the doubled interaction is the doubled Hamiltonian `H ⊗ 1 + 1 ⊗ H`, with
the two copies of every site paired. -/
theorem hamiltonian_doubled [Fintype ι] :
    Φ.doubled.hamiltonian = reindex (Equiv.arrowProdEquivProdArrow V X X).symm
      (Equiv.arrowProdEquivProdArrow V X X).symm (doubledHamiltonian Φ.hamiltonian) := by
  ext σ τ
  simp only [hamiltonian, doubled_term, doubledHamiltonian, Matrix.sum_apply, reindex_apply,
    submatrix_apply, Matrix.add_apply, kroneckerMap_apply, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]

/-- Each doubled term has norm at most twice the norm of the original term. -/
theorem norm_doubled_term_le (i : ι) : ‖Φ.doubled.term i‖ ≤ 2 * ‖Φ.term i‖ := by
  rw [doubled_term, Matrix.l2_opNorm_reindex_equiv, doubledHamiltonian, two_mul]
  exact (norm_add_le _ _).trans
    (add_le_add (l2_opNorm_kronecker_one_le _) (l2_opNorm_one_kronecker_le _))

variable {Φ} in
/-- The doubled terms of Hermitian terms are Hermitian. -/
theorem isHermitian_doubled_term {i : ι} (hΦ : (Φ.term i).IsHermitian) :
    (Φ.doubled.term i).IsHermitian := by
  refine IsHermitian.reindex ?_ _
  rw [IsHermitian, doubledHamiltonian, conjTranspose_add, conjTranspose_kronecker,
    conjTranspose_kronecker, hΦ.eq, conjTranspose_one]

end Doubled

/-! ### Interactions of placed regional matrices -/

section OfPlace

variable (R : ι → Finset V) (h : ∀ i, Matrix (RegionConfig X (R i)) (RegionConfig X (R i)) ℂ)

/-- **The interaction of placed regional matrices.** For regions `Rᵢ` and matrices `hᵢ` on the
configurations of `Rᵢ`, the interaction whose term with index `i` is `hᵢ` placed on `Rᵢ`.
Every interaction with supports `R` is of this form (`exists_eq_ofPlace`). Cirac,
Pérez-García, Schuch and Verstraete, arXiv:2011.12127, `TN-Review-main.tex`, lines 2008–2011,
for the parent Hamiltonian of a projected entangled pair state on regions `Rᵢ`. -/
noncomputable def ofPlace : Interaction X R where
  term i := place (R i) (h i)
  mem i := place_mem_supportedOperators (h i)

@[simp]
theorem ofPlace_term (i : ι) : (ofPlace R h).term i = place (R i) (h i) :=
  rfl

/-- The Hamiltonian of placed regional matrices is the sum of the placements. -/
theorem hamiltonian_ofPlace [Fintype ι] : (ofPlace R h).hamiltonian = ∑ i, place (R i) (h i) :=
  rfl

/-- Placed matrices have at most the norms of the regional matrices. -/
theorem norm_ofPlace_term_le (i : ι) : ‖(ofPlace R h).term i‖ ≤ ‖h i‖ :=
  norm_place_le (h i)

variable {R} in
/-- Every interaction is an interaction of placed regional matrices. -/
theorem exists_eq_ofPlace (Φ : Interaction X R) :
    ∃ h : ∀ i, Matrix (RegionConfig X (R i)) (RegionConfig X (R i)) ℂ, Φ = ofPlace R h := by
  choose h hh using fun i ↦ exists_eq_place_of_mem_supportedOperators (Φ.mem i)
  exact ⟨h, Interaction.ext (funext hh)⟩

end OfPlace

/-! ### Placement along an injection of sites -/

section Pushforward

variable {W : Type*} [Fintype W] [DecidableEq W] (w : W ↪ V) {S : ι → Finset W}

/-- **Placing an interaction along an injection of sites.** For an injection `w : W ↪ V` and an
interaction `Φ` on the sites `W`, the site `u` carrying the basis `X (w u)`, the interaction on
`X` whose term with index `i` is `hᵢ` placed along `w`, supported on the image of `Sᵢ`. A chain
of `L` sites inside a chain of `N ≥ L` sites, a domain inside a larger domain, and the sites of
a region of a lattice are the main cases. -/
noncomputable def pushforward (Φ : Interaction (fun u ↦ X (w u)) S) :
    Interaction X fun i ↦ (S i).map w where
  term i := placeAlong w (Φ.term i)
  mem i := placeAlong_mem_supportedOperators_map w (Φ.mem i)

variable (Φ : Interaction (fun u ↦ X (w u)) S)

@[simp]
theorem pushforward_term (i : ι) : (Φ.pushforward w).term i = placeAlong w (Φ.term i) :=
  rfl

/-- The Hamiltonian of an interaction placed along an injection is the placed Hamiltonian. -/
theorem hamiltonian_pushforward [Fintype ι] :
    (Φ.pushforward w).hamiltonian = placeAlong w Φ.hamiltonian :=
  (placeAlong_sum w Finset.univ Φ.term).symm

/-- A partial Hamiltonian of an interaction placed along an injection is the placed partial
Hamiltonian. -/
theorem partialHamiltonian_pushforward (s : Finset ι) :
    (Φ.pushforward w).partialHamiltonian s = placeAlong w (Φ.partialHamiltonian s) :=
  (placeAlong_sum w s Φ.term).symm

/-- The placed terms have at most the norms of the terms. -/
theorem norm_pushforward_term_le (i : ι) : ‖(Φ.pushforward w).term i‖ ≤ ‖Φ.term i‖ :=
  norm_placeAlong_le w _

variable {Φ}

/-- Placed Hermitian terms are Hermitian. -/
theorem isHermitian_pushforward_term {i : ι} (hΦ : (Φ.term i).IsHermitian) :
    ((Φ.pushforward w).term i).IsHermitian :=
  isHermitian_placeAlong w hΦ

/-- Placed positive terms are positive. -/
theorem pushforward_term_nonneg {i : ι} (hΦ : 0 ≤ Φ.term i) : 0 ≤ (Φ.pushforward w).term i :=
  (posSemidef_placeAlong w (nonneg_iff_posSemidef.mp hΦ)).nonneg

/-- Placed terms bounded by the identity are bounded by the identity. -/
theorem pushforward_term_le_one {i : ι} (hΦ : Φ.term i ≤ 1) : (Φ.pushforward w).term i ≤ 1 := by
  rw [pushforward_term, ← placeAlong_one w]
  exact placeAlong_le_placeAlong w hΦ

end Pushforward

/-! ### Two interactions on the same system -/

section Append

variable {κ : Type*} {T : κ → Finset V}

/-- **Two interactions on the same system.** The interaction whose terms are those of `Φ`,
with indices `inl i`, and those of `Ψ`, with indices `inr k`, each with its support. -/
def append (Φ : Interaction X S) (Ψ : Interaction X T) : Interaction X (Sum.elim S T) where
  term := Sum.elim Φ.term Ψ.term
  mem
    | .inl i => Φ.mem i
    | .inr k => Ψ.mem k

variable (Φ : Interaction X S) (Ψ : Interaction X T)

@[simp]
theorem append_term_inl (i : ι) : (Φ.append Ψ).term (.inl i) = Φ.term i :=
  rfl

@[simp]
theorem append_term_inr (k : κ) : (Φ.append Ψ).term (.inr k) = Ψ.term k :=
  rfl

/-- The Hamiltonian of two interactions on the same system is the sum of their Hamiltonians. -/
theorem hamiltonian_append [Fintype ι] [Fintype κ] :
    (Φ.append Ψ).hamiltonian = Φ.hamiltonian + Ψ.hamiltonian :=
  Fintype.sum_sum_type _

variable {Φ Ψ}

/-- A property of operators that holds for every term of `Φ` and of `Ψ` holds for every term of
the two together. -/
theorem forall_append_term {P : Matrix (Config X) (Config X) ℂ → Prop} (hΦ : ∀ i, P (Φ.term i))
    (hΨ : ∀ k, P (Ψ.term k)) : ∀ j, P ((Φ.append Ψ).term j)
  | .inl i => hΦ i
  | .inr k => hΨ k

end Append

/-! ### Padding an interaction on fewer sites -/

section Pad

variable {W : Type*} [Fintype W] [DecidableEq W] (w : W ↪ V) {S : ι → Finset W}

/-- **Padding an interaction.** For an injection `w : W ↪ V`, an interaction `Φ` on the sites
`W`, the site `u` carrying the basis `X (w u)`, and a matrix `p v` on the basis at every site
`v`, the interaction on `X` whose terms are those of `Φ` placed along `w`, supported on the
images of their supports, and one term `p v` at every site `v` outside the image of `w`,
supported on `{v}`. A chain of `L` sites inside a chain of `N ≥ L` sites, with a penalty for
leaving a reference state on each added site, is the main case. -/
noncomputable def pad (Φ : Interaction (fun u ↦ X (w u)) S) (p : ∀ v, Matrix (X v) (X v) ℂ) :
    Interaction X (Sum.elim (fun i ↦ (S i).map w)
      fun v : {v // v ∉ Finset.univ.map w} ↦ ({v.1} : Finset V)) :=
  (Φ.pushforward w).append
    { term := fun v ↦ placeAt v.1 (p v.1)
      mem := fun v ↦ placeAt_mem_supportedOperators v.1 (p v.1) }

variable (Φ : Interaction (fun u ↦ X (w u)) S) (p : ∀ v, Matrix (X v) (X v) ℂ)

@[simp]
theorem pad_term_inl (i : ι) : (Φ.pad w p).term (.inl i) = placeAlong w (Φ.term i) :=
  rfl

@[simp]
theorem pad_term_inr (v : {v // v ∉ Finset.univ.map w}) :
    (Φ.pad w p).term (.inr v) = placeAt v.1 (p v.1) :=
  rfl

/-- The Hamiltonian of the padded interaction is the placed Hamiltonian of `Φ` plus the sum of
the terms at the sites outside the image. -/
theorem hamiltonian_pad [Fintype ι] :
    (Φ.pad w p).hamiltonian =
      placeAlong w Φ.hamiltonian + ∑ v : {v // v ∉ Finset.univ.map w}, placeAt v.1 (p v.1) := by
  rw [pad, hamiltonian_append, hamiltonian_pushforward]
  rfl

variable {Φ p}

/-- The padding of positive terms by positive matrices has positive terms. -/
theorem pad_term_nonneg (hΦ : ∀ i, 0 ≤ Φ.term i) (hp : ∀ v, 0 ≤ p v) :
    ∀ j, 0 ≤ (Φ.pad w p).term j :=
  forall_append_term (fun i ↦ pushforward_term_nonneg w (hΦ i)) fun v ↦
    (posSemidef_placeAt (nonneg_iff_posSemidef.mp (hp v.1))).nonneg

/-- The padding of terms bounded by the identity by matrices bounded by the identity has terms
bounded by the identity. -/
theorem pad_term_le_one (hΦ : ∀ i, Φ.term i ≤ 1) (hp : ∀ v, p v ≤ 1) :
    ∀ j, (Φ.pad w p).term j ≤ 1
  | .inl i => pushforward_term_le_one w (hΦ i)
  | .inr v => by simpa using placeAt_le_placeAt (X := X) (v := v.1) (hp v.1)

/-- The padding of Hermitian terms by Hermitian matrices has Hermitian terms. -/
theorem isHermitian_pad_term (hΦ : ∀ i, (Φ.term i).IsHermitian) (hp : ∀ v, (p v).IsHermitian) :
    ∀ j, ((Φ.pad w p).term j).IsHermitian :=
  forall_append_term (fun i ↦ isHermitian_pushforward_term w (hΦ i)) fun v ↦
    isHermitian_placeAt (hp v.1)

end Pad

/-! ### Conjugation by a matrix that keeps the supports -/

section Conj

/-- **Conjugation of an interaction.** For a matrix `U` with `U hᵢ U†` supported on `Sᵢ` for
every `i`, the interaction with terms `U hᵢ U†`. For a unitary `U` its Hamiltonian is `U H U†`,
which has the spectrum, ground spaces and gaps of `H` carried by `U`. -/
def conj (Φ : Interaction X S) (U : Matrix (Config X) (Config X) ℂ)
    (hU : ∀ i, U * Φ.term i * Uᴴ ∈ supportedOperators X (S i)) : Interaction X S where
  term i := U * Φ.term i * Uᴴ
  mem := hU

variable (Φ : Interaction X S) (U : Matrix (Config X) (Config X) ℂ)
  (hU : ∀ i, U * Φ.term i * Uᴴ ∈ supportedOperators X (S i))

@[simp]
theorem conj_term (i : ι) : (Φ.conj U hU).term i = U * Φ.term i * Uᴴ :=
  rfl

/-- The Hamiltonian of the conjugated interaction is the conjugated Hamiltonian. -/
theorem hamiltonian_conj [Fintype ι] : (Φ.conj U hU).hamiltonian = U * Φ.hamiltonian * Uᴴ := by
  simp only [hamiltonian, conj_term, Finset.mul_sum, Finset.sum_mul]

/-- Conjugation by a unitary keeps the norms of the terms. -/
theorem norm_conj_term {U : Matrix (Config X) (Config X) ℂ} (hU' : U ∈ unitaryGroup (Config X) ℂ)
    (hU : ∀ i, U * Φ.term i * Uᴴ ∈ supportedOperators X (S i)) (i : ι) :
    ‖(Φ.conj U hU).term i‖ = ‖Φ.term i‖ := by
  let V : unitary (Matrix (Config X) (Config X) ℂ) := ⟨U, hU'⟩
  calc ‖(Φ.conj U hU).term i‖
      = ‖(V : Matrix _ _ ℂ) * Φ.term i * ((star V : unitary _) : Matrix _ _ ℂ)‖ := rfl
    _ = ‖Φ.term i‖ := by rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

variable {Φ}

/-- Conjugated Hermitian terms are Hermitian. -/
theorem isHermitian_conj_term {i : ι} (hΦ : (Φ.term i).IsHermitian) :
    ((Φ.conj U hU).term i).IsHermitian :=
  isHermitian_mul_mul_conjTranspose U hΦ

/-- Conjugated positive terms are positive. -/
theorem conj_term_nonneg {i : ι} (hΦ : 0 ≤ Φ.term i) : 0 ≤ (Φ.conj U hU).term i :=
  ((nonneg_iff_posSemidef.mp hΦ).mul_mul_conjTranspose_same U).nonneg

end Conj

/-! ### Termwise maps -/

section MapTerm

variable (f : ι → Matrix (Config X) (Config X) ℂ → Matrix (Config X) (Config X) ℂ)
  (hf : ∀ i A, A ∈ supportedOperators X (S i) → f i A ∈ supportedOperators X (S i))

/-- **A termwise map of an interaction.** For maps `fᵢ` of operators that keep the operators
supported on `Sᵢ` supported on `Sᵢ`, the interaction with terms `fᵢ hᵢ` and the supports of
`Φ`. -/
def mapTerm (Φ : Interaction X S) : Interaction X S where
  term i := f i (Φ.term i)
  mem i := hf i _ (Φ.mem i)

variable (Φ : Interaction X S)

@[simp]
theorem mapTerm_term (i : ι) : (Φ.mapTerm f hf).term i = f i (Φ.term i) :=
  rfl

/-- A partial Hamiltonian of a termwise map is the sum of the mapped terms. -/
theorem partialHamiltonian_mapTerm (s : Finset ι) :
    (Φ.mapTerm f hf).partialHamiltonian s = ∑ i ∈ s, f i (Φ.term i) :=
  rfl

/-- The Hamiltonian of a termwise map is the sum of the mapped terms. -/
theorem hamiltonian_mapTerm [Fintype ι] : (Φ.mapTerm f hf).hamiltonian = ∑ i, f i (Φ.term i) :=
  rfl

end MapTerm

/-! ### Restriction to a set of indices -/

section Restrict

variable (Φ : Interaction X S) (p : ι → Prop) [DecidablePred p]

/-- **Restricting an interaction to the indices with a property.** The interaction with the
supports of `Φ` whose term with index `i` is `hᵢ` when `p i` holds and `0` otherwise. The
Hamiltonian of the restriction is the partial Hamiltonian of the indices with the property,
and its terms are the terms of `Φ` or zero, so they keep every termwise bound that zero
satisfies. -/
def restrict : Interaction X S :=
  Φ.mapTerm (fun i A ↦ if p i then A else 0) fun i A hA ↦ by
    split_ifs
    · exact hA
    · exact zero_mem _

theorem restrict_term (i : ι) : (Φ.restrict p).term i = if p i then Φ.term i else 0 :=
  rfl

variable {Φ p}

@[simp]
theorem restrict_term_of_pos {i : ι} (hi : p i) : (Φ.restrict p).term i = Φ.term i :=
  by simp [restrict_term, hi]

@[simp]
theorem restrict_term_of_neg {i : ι} (hi : ¬ p i) : (Φ.restrict p).term i = 0 :=
  by simp [restrict_term, hi]

/-- A property of operators that holds for zero and for the term of `Φ` with index `i` holds for
the term of the restriction with index `i`. -/
theorem forall_restrict_term {P : Matrix (Config X) (Config X) ℂ → Prop} (h0 : P 0) {i : ι}
    (hΦ : P (Φ.term i)) : P ((Φ.restrict p).term i) := by
  by_cases hi : p i
  · simpa [hi] using hΦ
  · simpa [hi] using h0

variable (Φ p)

/-- A partial Hamiltonian of the restriction is the partial Hamiltonian of the indices with the
property. -/
theorem partialHamiltonian_restrict (s : Finset ι) :
    (Φ.restrict p).partialHamiltonian s = Φ.partialHamiltonian (s.filter p) :=
  Finset.sum_filter _ _ |>.symm

/-- The Hamiltonian of the restriction is the partial Hamiltonian of the indices with the
property. -/
theorem hamiltonian_restrict [Fintype ι] :
    (Φ.restrict p).hamiltonian = Φ.partialHamiltonian (Finset.univ.filter p) :=
  partialHamiltonian_restrict Φ p Finset.univ

variable {Φ p}

/-- On a set of indices with the property, the restriction has the partial Hamiltonian of `Φ`. -/
theorem partialHamiltonian_restrict_of_forall {s : Finset ι} (hs : ∀ i ∈ s, p i) :
    (Φ.restrict p).partialHamiltonian s = Φ.partialHamiltonian s :=
  Finset.sum_congr rfl fun _ hi ↦ restrict_term_of_pos (hs _ hi)

/-- On a set of indices without the property, the partial Hamiltonian of the restriction
vanishes. -/
theorem partialHamiltonian_restrict_eq_zero {s : Finset ι} (hs : ∀ i ∈ s, ¬ p i) :
    (Φ.restrict p).partialHamiltonian s = 0 :=
  Finset.sum_eq_zero fun _ hi ↦ restrict_term_of_neg (hs _ hi)

/-- The restriction of a Hermitian term is Hermitian. -/
theorem isHermitian_restrict_term {i : ι} (hΦ : (Φ.term i).IsHermitian) :
    ((Φ.restrict p).term i).IsHermitian :=
  forall_restrict_term isHermitian_zero hΦ

/-- The restriction of a positive term is positive. -/
theorem restrict_term_nonneg {i : ι} (hΦ : 0 ≤ Φ.term i) : 0 ≤ (Φ.restrict p).term i :=
  forall_restrict_term le_rfl hΦ

/-- The restriction of a term bounded by the identity is bounded by the identity. -/
theorem restrict_term_le_one {i : ι} (hΦ : Φ.term i ≤ 1) : (Φ.restrict p).term i ≤ 1 :=
  forall_restrict_term (P := fun M ↦ M ≤ 1) zero_le_one hΦ

variable (Φ p) in
/-- The terms of the restriction have at most the norms of the terms. -/
theorem norm_restrict_term_le (i : ι) : ‖(Φ.restrict p).term i‖ ≤ ‖Φ.term i‖ :=
  forall_restrict_term (P := fun M ↦ ‖M‖ ≤ ‖Φ.term i‖) (by simp) le_rfl

end Restrict

/-! ### The range projections of positive terms -/

section SupportProj

variable (Φ : Interaction X S) (hΦ : ∀ i, (Φ.term i).PosSemidef)

/-- **The range projections of positive terms.** For an interaction with positive semidefinite
terms, the interaction with the supports of `Φ` whose term with index `i` is the orthogonal
projection onto the range of `hᵢ`. It has the kernel of `Φ`, and for terms of norm at most one
it lies above `Φ` in operator order. ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460. -/
noncomputable def supportProj : Interaction X S where
  term i := (hΦ i).supportProj
  mem i := supportProj_mem_supportedOperators (hΦ i).isHermitian (Φ.mem i)

@[simp]
theorem supportProj_term (i : ι) : (Φ.supportProj hΦ).term i = (hΦ i).supportProj :=
  rfl

/-- The terms of the range projections are orthogonal projections. -/
theorem isStarProjection_supportProj_term (i : ι) :
    IsStarProjection ((Φ.supportProj hΦ).term i) :=
  (hΦ i).isHermitian.isStarProjection_supportProj

/-- The terms of the range projections are positive. -/
theorem supportProj_term_nonneg (i : ι) : 0 ≤ (Φ.supportProj hΦ).term i :=
  (isStarProjection_supportProj_term Φ hΦ i).nonneg

/-- A positive term of norm at most one lies below its range projection. -/
theorem term_le_supportProj_term {i : ι} (hn : ‖Φ.term i‖ ≤ 1) :
    Φ.term i ≤ (Φ.supportProj hΦ).term i :=
  (hΦ i).le_supportProj_of_norm_le_one hn

/-- **Replacing the terms by their range projections increases the Hamiltonian** when every
term has norm at most one. ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460. -/
theorem hamiltonian_le_hamiltonian_supportProj [Fintype ι] (hn : ∀ i, ‖Φ.term i‖ ≤ 1) :
    Φ.hamiltonian ≤ (Φ.supportProj hΦ).hamiltonian :=
  Finset.sum_le_sum fun i _ ↦ term_le_supportProj_term Φ hΦ (hn i)

/-- **Replacing the terms by their range projections keeps the kernel of the Hamiltonian.** No
bound on the norms of the terms is needed. ALVV, arXiv:1602.08828v2, Section 6.1,
lines 1457–1460. -/
theorem hamiltonian_supportProj_mulVec_eq_zero_iff [Fintype ι] (x : Config X → ℂ) :
    (Φ.supportProj hΦ).hamiltonian *ᵥ x = 0 ↔ Φ.hamiltonian *ᵥ x = 0 :=
  PosSemidef.sum_supportProj_mulVec_eq_zero_iff (h := Φ.term) hΦ x

end SupportProj

end Interaction

/-! ### Translates of one operator -/

section Translates

variable {V : Type*} [Fintype V] [DecidableEq V] {W : Type*} [Fintype W]
  {α : Type*} [Fintype α] [DecidableEq α] {ι : Type*}

/-- **The translates of one operator.** For an operator `h` on the configurations of the sites
`W` and injections `wᵢ : W ↪ V`, the term with index `i` is `h` placed along `wᵢ`: it acts as
`h` on the image `wᵢ(W)`, the site `u` of `W` carried to `wᵢ u`. Schuch, Pérez-García and
Cirac, arXiv:1010.3732, `sec:phases-definition-no-sym`, lines 407–427, for the translates of a
nearest-neighbour term on a ring. -/
noncomputable def Interaction.translates (w : ι → W ↪ V) (h : Matrix (W → α) (W → α) ℂ) :
    Interaction (fun _ : V ↦ α) (fun i ↦ Finset.univ.map (w i)) where
  term i := placeAlong (X := fun _ ↦ α) (w i) h
  mem i := placeAlong_mem_supportedOperators (X := fun _ ↦ α) (w i) h

namespace Interaction

variable (w : ι → W ↪ V) (h : Matrix (W → α) (W → α) ℂ)

/-- The term with index `i` of the translates is `h` placed along `wᵢ`. -/
@[simp]
theorem translates_term (i : ι) :
    (translates w h).term i = placeAlong (X := fun _ ↦ α) (w i) h :=
  rfl

variable [DecidableEq W] in
/-- The translates of an operator have at most its norm. -/
theorem norm_translates_term_le (i : ι) : ‖(translates w h).term i‖ ≤ ‖h‖ :=
  norm_placeAlong_le (X := fun _ ↦ α) (w i) h

variable {h}

/-- The translates of a Hermitian operator are Hermitian. -/
theorem isHermitian_translates_term (hh : h.IsHermitian) (i : ι) :
    ((translates w h).term i).IsHermitian :=
  isHermitian_placeAlong (X := fun _ ↦ α) (w i) hh

/-- The translates of a positive operator are positive. -/
theorem translates_term_nonneg (hh : 0 ≤ h) (i : ι) : 0 ≤ (translates w h).term i :=
  (posSemidef_placeAlong (X := fun _ ↦ α) (w i) (nonneg_iff_posSemidef.mp hh)).nonneg

end Interaction

end Translates

end ManyBody
