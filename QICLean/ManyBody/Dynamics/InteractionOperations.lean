/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Sites.Placement
import QICLean.ManyBody.Sites.Relabel
import QICLean.ManyBody.Sites.SitewiseProduct
import QICLean.Analysis.DoubledSystemGap
import QICLean.Analysis.KroneckerOperatorNorm

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
* the **translates** of one operator `h` on the configurations of a finite set `W` along a family
  of injections `wᵢ : W ↪ V`: the term with index `i` is the placement of `h` on `wᵢ(W)`.

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
indices; and the window placements `MPOTensor.embedLocalOperator` of
`MPSTensor.interactionHamiltonian` (`MPS/Symmetry/GappedInteractionPath`).

## Main definitions

* `ManyBody.Interaction.partialHamiltonian`, `ManyBody.Interaction.relabel`,
  `ManyBody.Interaction.extend`, `ManyBody.Interaction.doubled`,
  `ManyBody.Interaction.translates`, and the instance `SMul ℝ (ManyBody.Interaction X S)`.
* `ManyBody.windowEquiv` — the sites of `W` identified with their image under an injection.

## Main results

* `ManyBody.Interaction.partialHamiltonian_univ`,
  `ManyBody.Interaction.partialHamiltonian_filter_add_filter_not`,
  `ManyBody.Interaction.partialHamiltonian_mem_supportedOperators`,
  `ManyBody.Interaction.norm_partialHamiltonian_le`.
* `ManyBody.Interaction.hamiltonian_smul`, `ManyBody.Interaction.hamiltonian_relabel`,
  `ManyBody.Interaction.hamiltonian_extend`, `ManyBody.Interaction.hamiltonian_doubled` — the
  Hamiltonians of the new interactions.
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

/-- Partial Hamiltonians add over disjoint sets of indices. -/
theorem partialHamiltonian_union [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t) :
    Φ.partialHamiltonian (s ∪ t) = Φ.partialHamiltonian s + Φ.partialHamiltonian t :=
  Finset.sum_union h

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

/-- A partial Hamiltonian of positive terms is positive. -/
theorem partialHamiltonian_nonneg {s : Finset ι} (hΦ : ∀ i ∈ s, 0 ≤ Φ.term i) :
    0 ≤ Φ.partialHamiltonian s :=
  Finset.sum_nonneg hΦ

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

end Interaction

/-! ### Translates of one operator -/

section Translates

variable {V : Type*} [Fintype V] [DecidableEq V] {W : Type*} [Fintype W]
  {α : Type*} [Fintype α] [DecidableEq α] {ι : Type*}

omit [DecidableEq V] in
/-- The sites `W` identified with their image under an injection `w : W ↪ V`. -/
noncomputable def windowEquiv (w : W ↪ V) : W ≃ ↥(Finset.univ.map w) :=
  (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans (Finset.univ.equivMap w)

omit [Fintype V] [DecidableEq V] in
@[simp]
theorem coe_windowEquiv (w : W ↪ V) (u : W) : (windowEquiv w u : V) = w u :=
  rfl

/-- **The translates of one operator.** For an operator `h` on the configurations of the sites
`W` and injections `wᵢ : W ↪ V`, the term with index `i` is the placement of `h` on the image
`wᵢ(W)`, with the site `u` of `W` carried to `wᵢ u`. Schuch, Pérez-García and Cirac,
arXiv:1010.3732, `sec:phases-definition-no-sym`, lines 407–427, for the translates of a
nearest-neighbour term on a ring. -/
noncomputable def Interaction.translates (w : ι → W ↪ V) (h : Matrix (W → α) (W → α) ℂ) :
    Interaction (fun _ : V ↦ α) (fun i ↦ Finset.univ.map (w i)) where
  term i := place (Finset.univ.map (w i))
    (reindex ((windowEquiv (w i)).arrowCongr (Equiv.refl α))
      ((windowEquiv (w i)).arrowCongr (Equiv.refl α)) h)
  mem _ := place_mem_supportedOperators _

namespace Interaction

variable (w : ι → W ↪ V) (h : Matrix (W → α) (W → α) ℂ)

/-- The term with index `i` of the translates is `h` placed on the image `wᵢ(W)`. -/
theorem translates_term (i : ι) :
    (translates w h).term i = place (Finset.univ.map (w i))
      (reindex ((windowEquiv (w i)).arrowCongr (Equiv.refl α))
        ((windowEquiv (w i)).arrowCongr (Equiv.refl α)) h) :=
  rfl

variable [DecidableEq W] in
/-- The translates of an operator have at most its norm. -/
theorem norm_translates_term_le (i : ι) : ‖(translates w h).term i‖ ≤ ‖h‖ := by
  rw [translates_term]
  exact (norm_place_le _).trans (Matrix.l2_opNorm_reindex_equiv _ _).le

variable {h}

/-- The translates of a Hermitian operator are Hermitian. -/
theorem isHermitian_translates_term (hh : h.IsHermitian) (i : ι) :
    ((translates w h).term i).IsHermitian := by
  rw [translates_term]
  exact isHermitian_place (hh.reindex _)

/-- The translates of a positive operator are positive. -/
theorem translates_term_nonneg (hh : 0 ≤ h) (i : ι) : 0 ≤ (translates w h).term i := by
  rw [translates_term]
  exact (posSemidef_place ((posSemidef_submatrix_equiv _).mpr (nonneg_iff_posSemidef.mp hh))).nonneg

end Interaction

end Translates

end ManyBody
