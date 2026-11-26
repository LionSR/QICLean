/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Config
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import QICLean.Analysis.Projection.DetectabilityLemma
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operators supported on a region

Let `X` be a system of sites with finite basis types, standing for `⊗_v ℂ^{X v}`. An operator
is supported on a region `D` when it acts as the identity on the sites outside `D`: its matrix
entry between two configurations vanishes when they differ outside `D`, and otherwise depends
only on their parts on `D`. The operators supported on `D` form a unital `*`-subalgebra
`ManyBody.supportedOperators X D` of the matrix algebra, isomorphic to the matrix algebra of
the region; the isomorphism is the placement of `QICLean.ManyBody.Sites.Placement`.

Statements about supported operators are written `A ∈ supportedOperators X D`. Closure under
sums, scalar multiples, products, powers and adjoints is membership in a `*`-subalgebra
(`add_mem`, `smul_mem`, `mul_mem`, `pow_mem`, `star_mem`, `sum_mem`, ...). No statement
requires a configuration to exist: when some basis type is empty the matrix algebra is zero
and every operator is supported on every region.

## Main definitions

* `ManyBody.supportedOperators` — the `*`-subalgebra of operators supported on a region.

## Main results

* `ManyBody.mem_supportedOperators_iff` — membership is the condition on matrix entries.
* `ManyBody.apply_eq_zero_of_mem_supportedOperators`,
  `ManyBody.IsSupportedOn.apply_eq` — the two halves of that condition in the
  form used in computations.
* `ManyBody.supportedOperators_mono`, `ManyBody.supportedOperators_univ`.
* `ManyBody.diagonal_mem_supportedOperators` — a diagonal matrix reading only the sites of `D` is
  supported on `D`.
* `ManyBody.reindex_kronecker_mem_supportedOperators`: two systems on the same sites, paired at
  every site.
* `QuantumCircuit.mem_supportedOperators_complementProd`: support of ordered complementary products.

## Implementation notes

`ManyBody.IsSupportedOn` is the condition on matrix entries, stated without the finiteness and
decidability assumptions that the algebra structure of the matrices needs. It is the carrier
of the subalgebra and has no interface of its own.
-/

section Support

open Matrix

namespace ManyBody

variable {V : Type*} {X : V → Type*}

/-- The condition on matrix entries that defines `ManyBody.supportedOperators`: the entries of
`A` vanish between configurations that differ outside `D`, and otherwise do not depend on the
common values outside `D`.

This is the carrier of the subalgebra; statements use `A ∈ supportedOperators X D`.
Area-law manuscript, Lemma 3.1, `02-initial.tex`, line 39: designated supports. -/
def IsSupportedOn (A : Matrix (Config X) (Config X) ℂ) (D : Finset V) : Prop :=
  (∀ σ τ : Config X, (∃ v ∉ D, σ v ≠ τ v) → A σ τ = 0) ∧
    ∀ σ τ σ' τ' : Config X, (∀ v ∈ D, σ v = σ' v) → (∀ v ∈ D, τ v = τ' v) →
      (∀ v ∉ D, σ v = τ v) → (∀ v ∉ D, σ' v = τ' v) → A σ τ = A σ' τ'

/-- Entries of an operator supported on `D` agree whenever the configurations agree on `D` and
have the same coincidence pattern outside it. -/
theorem IsSupportedOn.apply_eq {A : Matrix (Config X) (Config X) ℂ} {D : Finset V}
    (hA : IsSupportedOn A D) {σ τ σ' τ' : Config X} (h1 : ∀ v ∈ D, σ v = σ' v)
    (h2 : ∀ v ∈ D, τ v = τ' v) (h3 : ∀ v ∉ D, (σ v = τ v ↔ σ' v = τ' v)) :
    A σ τ = A σ' τ' := by
  by_cases h : ∃ v ∉ D, σ v ≠ τ v
  · obtain ⟨v, hv, hne⟩ := h
    rw [hA.1 σ τ ⟨v, hv, hne⟩, hA.1 σ' τ' ⟨v, hv, fun h' ↦ hne ((h3 v hv).mpr h')⟩]
  · push Not at h
    exact hA.2 σ τ σ' τ' h1 h2 h (fun v hv ↦ (h3 v hv).mp (h v hv))

/-- Support on a region implies support on every larger region. -/
theorem IsSupportedOn.mono {A : Matrix (Config X) (Config X) ℂ} {D D' : Finset V}
    (hA : IsSupportedOn A D) (h : D ⊆ D') : IsSupportedOn A D' := by
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ hA.1 σ τ ⟨v, fun hvD ↦ hv (h hvD), hne⟩,
    fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  refine hA.apply_eq (fun v hv ↦ h1 v (h hv)) (fun v hv ↦ h2 v (h hv)) fun v hv ↦ ?_
  by_cases hv' : v ∈ D'
  · rw [h1 v hv', h2 v hv']
  · exact ⟨fun _ ↦ h4 v hv', fun _ ↦ h3 v hv'⟩

section Carrier

variable [Fintype V] [DecidableEq V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]
  {D : Finset V} {A B : Matrix (Config X) (Config X) ℂ}

omit [DecidableEq V] [∀ v, Fintype (X v)] in
private theorem isSupportedOn_one (D : Finset V) :
    IsSupportedOn (1 : Matrix (Config X) (Config X) ℂ) D := by
  refine ⟨fun σ τ ⟨v, _, hne⟩ ↦ one_apply_ne fun h ↦ hne (congrFun h v),
    fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  have h : σ = τ ↔ σ' = τ' := by
    refine ⟨fun h ↦ funext fun v ↦ ?_, fun h ↦ funext fun v ↦ ?_⟩
    · by_cases hv : v ∈ D
      · rw [← h1 v hv, ← h2 v hv, h]
      · exact h4 v hv
    · by_cases hv : v ∈ D
      · rw [h1 v hv, h2 v hv, h]
      · exact h3 v hv
  simp only [one_apply, h]

omit [∀ v, DecidableEq (X v)] in
/-- Only the intermediate configurations that agree with `σ` outside `D` contribute to an
entry of `A * B`; they are the configurations of `D`, glued to the part of `σ` outside `D`. -/
private theorem IsSupportedOn.mul_apply (hA : IsSupportedOn A D) (σ τ : Config X) :
    (A * B) σ τ = ∑ a : RegionConfig X D,
      A σ ((cutEquiv X D).symm (a, (cutEquiv X D σ).2)) *
        B ((cutEquiv X D).symm (a, (cutEquiv X D σ).2)) τ := by
  rw [Matrix.mul_apply, ← (cutEquiv X D).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  refine Finset.sum_eq_single _ (fun y _ hy ↦ ?_) (fun h ↦ absurd (Finset.mem_univ _) h)
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hy
  rw [hA.1 _ _ ⟨v.1, v.2, ?_⟩, zero_mul]
  rw [cutEquiv_symm_apply_not_mem _ _ v.2]
  exact fun h ↦ hv h.symm

omit [∀ v, DecidableEq (X v)] in
theorem IsSupportedOn.mul (hA : IsSupportedOn A D) (hB : IsSupportedOn B D) :
    IsSupportedOn (A * B) D := by
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun ρ _ ↦ ?_
    by_cases hρ : σ v = ρ v
    · rw [hB.1 ρ τ ⟨v, hv, fun h ↦ hne (hρ.trans h)⟩, mul_zero]
    · rw [hA.1 σ ρ ⟨v, hv, hρ⟩, zero_mul]
  · rw [hA.mul_apply, hA.mul_apply]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hmem : ∀ (ρ : Config X) (v) (hv : v ∈ D),
        (cutEquiv X D).symm (a, (cutEquiv X D ρ).2) v = a ⟨v, hv⟩ :=
      fun ρ v hv ↦ cutEquiv_symm_apply_mem _ _ hv
    have hnot : ∀ (ρ : Config X) (v) (_ : v ∉ D),
        (cutEquiv X D).symm (a, (cutEquiv X D ρ).2) v = ρ v :=
      fun ρ v hv ↦ cutEquiv_symm_apply_not_mem _ _ hv
    rw [hA.2 σ _ σ' _ h1 (fun v hv ↦ by rw [hmem σ v hv, hmem σ' v hv])
        (fun v hv ↦ (hnot σ v hv).symm) (fun v hv ↦ (hnot σ' v hv).symm),
      hB.2 _ τ _ τ' (fun v hv ↦ by rw [hmem σ v hv, hmem σ' v hv]) h2
        (fun v hv ↦ (hnot σ v hv).trans (h3 v hv)) (fun v hv ↦ (hnot σ' v hv).trans (h4 v hv))]

end Carrier

/-- The operators supported on the region `D`, as a unital `*`-subalgebra of the matrix
algebra of the system: the operators that act as the identity on the sites outside `D`. -/
def supportedOperators [Fintype V] [DecidableEq V] (X : V → Type*) [∀ v, Fintype (X v)]
    [∀ v, DecidableEq (X v)] (D : Finset V) :
    StarSubalgebra ℂ (Matrix (Config X) (Config X) ℂ) where
  carrier := {A | IsSupportedOn A D}
  zero_mem' := ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ _ _ _ ↦ rfl⟩
  add_mem' {A B} hA hB := by
    refine ⟨fun σ τ h ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
    · rw [Matrix.add_apply, hA.1 σ τ h, hB.1 σ τ h, add_zero]
    · rw [Matrix.add_apply, Matrix.add_apply, hA.2 σ τ σ' τ' h1 h2 h3 h4,
        hB.2 σ τ σ' τ' h1 h2 h3 h4]
  one_mem' := isSupportedOn_one D
  mul_mem' hA hB := hA.mul hB
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    refine ⟨fun σ τ h ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
    · rw [Matrix.smul_apply, (isSupportedOn_one D).1 σ τ h, smul_zero]
    · rw [Matrix.smul_apply, Matrix.smul_apply, (isSupportedOn_one D).2 σ τ σ' τ' h1 h2 h3 h4]
  star_mem' {A} hA := by
    refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
    · rw [star_apply, hA.1 τ σ ⟨v, hv, Ne.symm hne⟩, star_zero]
    · rw [star_apply, star_apply,
        hA.2 τ σ τ' σ' h2 h1 (fun v hv ↦ (h3 v hv).symm) (fun v hv ↦ (h4 v hv).symm)]

variable [Fintype V] [DecidableEq V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]
  {D D' : Finset V} {A : Matrix (Config X) (Config X) ℂ}

/-- Membership in the subalgebra of operators supported on `D` is the condition on matrix
entries: they vanish between configurations that differ outside `D`, and otherwise do not
depend on the common values outside `D`. -/
theorem mem_supportedOperators_iff :
    A ∈ supportedOperators X D ↔
      (∀ σ τ : Config X, (∃ v ∉ D, σ v ≠ τ v) → A σ τ = 0) ∧
        ∀ σ τ σ' τ' : Config X, (∀ v ∈ D, σ v = σ' v) → (∀ v ∈ D, τ v = τ' v) →
          (∀ v ∉ D, σ v = τ v) → (∀ v ∉ D, σ' v = τ' v) → A σ τ = A σ' τ' :=
  Iff.rfl

/-- The entry of a supported operator between configurations that differ outside its region
vanishes. -/
theorem apply_eq_zero_of_mem_supportedOperators (hA : A ∈ supportedOperators X D)
    {σ τ : Config X} {v : V} (hv : v ∉ D) (hne : σ v ≠ τ v) : A σ τ = 0 :=
  hA.1 σ τ ⟨v, hv, hne⟩

/-- The subalgebra of supported operators grows with the region. -/
theorem supportedOperators_mono (h : D ⊆ D') :
    supportedOperators X D ≤ supportedOperators X D' :=
  fun _ hA ↦ IsSupportedOn.mono hA h

/-- Every operator is supported on the set of all sites. -/
@[simp]
theorem supportedOperators_univ : supportedOperators X Finset.univ = ⊤ :=
  top_unique fun A _ ↦ ⟨fun _ _ ⟨v, hv, _⟩ ↦ absurd (Finset.mem_univ v) hv,
    fun σ τ σ' τ' h1 h2 _ _ ↦ by
      rw [funext fun v ↦ h1 v (Finset.mem_univ v), funext fun v ↦ h2 v (Finset.mem_univ v)]⟩

/-- A diagonal matrix whose entries read only the sites of `D` is supported on `D`. -/
theorem diagonal_mem_supportedOperators {f : Config X → ℂ}
    (hf : ∀ σ τ : Config X, (∀ v ∈ D, σ v = τ v) → f σ = f τ) :
    diagonal f ∈ supportedOperators X D := by
  have hone := one_mem (supportedOperators X D)
  rw [← Matrix.mul_one (diagonal f)]
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [diagonal_mul, apply_eq_zero_of_mem_supportedOperators hone hv hne, mul_zero]
  · rw [diagonal_mul, diagonal_mul, (mem_supportedOperators_iff.mp hone).2 σ τ σ' τ' h1 h2 h3 h4,
      hf σ σ' h1]

/-! ### Disjoint regions -/

/-- An entry of a product of operators supported on disjoint regions `D` and `D'` is a single
product of entries, through the configuration equal to the column configuration on `D` and to
the row configuration elsewhere. -/
theorem mul_apply_of_mem_supportedOperators_of_disjoint {B : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X D) (hB : B ∈ supportedOperators X D') (h : Disjoint D D')
    (σ τ : Config X) :
    (A * B) σ τ = A σ (fun v ↦ if v ∈ D then τ v else σ v) *
      B (fun v ↦ if v ∈ D then τ v else σ v) τ := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single _ (fun ρ _ hρ ↦ ?_) (fun h ↦ absurd (Finset.mem_univ _) h)
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hρ
  by_cases hvD : v ∈ D
  · rw [ite_eq_left hvD] at hv
    rw [apply_eq_zero_of_mem_supportedOperators hB (Finset.disjoint_left.mp h hvD) hv, mul_zero]
  · rw [ite_eq_right hvD] at hv
    rw [apply_eq_zero_of_mem_supportedOperators hA hvD (Ne.symm hv), zero_mul]

/-- Operators supported on disjoint regions commute. -/
theorem commute_of_mem_supportedOperators_of_disjoint {B : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X D) (hB : B ∈ supportedOperators X D') (h : Disjoint D D') :
    Commute A B := by
  ext σ τ
  by_cases hστ : ∃ v ∉ D ∪ D', σ v ≠ τ v
  · -- Both products are supported on `D ∪ D'`.
    obtain ⟨v, hv, hne⟩ := hστ
    have hA' : A ∈ supportedOperators X (D ∪ D') :=
      supportedOperators_mono Finset.subset_union_left hA
    have hB' : B ∈ supportedOperators X (D ∪ D') :=
      supportedOperators_mono Finset.subset_union_right hB
    rw [apply_eq_zero_of_mem_supportedOperators (mul_mem hA' hB') hv hne,
      apply_eq_zero_of_mem_supportedOperators (mul_mem hB' hA') hv hne]
  · push Not at hστ
    have hD' : ∀ v ∈ D, v ∉ D' := fun v hv ↦ Finset.disjoint_left.mp h hv
    have hD : ∀ v ∈ D', v ∉ D := fun v hv ↦ Finset.disjoint_right.mp h hv
    rw [mul_apply_of_mem_supportedOperators_of_disjoint hA hB h,
      mul_apply_of_mem_supportedOperators_of_disjoint hB hA h.symm, mul_comm]
    congr 1
    · refine IsSupportedOn.apply_eq hB (fun v hv ↦ ?_) (fun v hv ↦ ?_)
        fun v hv ↦ ?_
      · rw [ite_eq_right (hD v hv)]
      · rw [ite_eq_left hv]
      · by_cases hvD : v ∈ D
        · simp [hvD, hv]
        · simp [hvD, hv, hστ v (by simp [hvD, hv])]
    · refine IsSupportedOn.apply_eq hA (fun v hv ↦ ?_) (fun v hv ↦ ?_)
        fun v hv ↦ ?_
      · rw [ite_eq_right (hD' v hv)]
      · rw [ite_eq_left hv]
      · by_cases hvD' : v ∈ D'
        · simp [hvD', hv]
        · simp [hvD', hv, hστ v (by simp [hvD', hv])]

/-- An operator in the coordinates of the cut along `D`: its matrix indexed by pairs of a
configuration of `D` and one of the other sites. -/
noncomputable abbrev cutOperator (D : Finset V) (A : Matrix (Config X) (Config X) ℂ) :
    Matrix (RegionConfig X D × ComplConfig X D) (RegionConfig X D × ComplConfig X D) ℂ :=
  reindex (cutEquiv X D) (cutEquiv X D) A

end ManyBody

end Support

section SitewiseProduct

/-!
## Two systems on the same sites, paired at every site

Two systems `X` and `Y` on the same sites `V` give the system with basis `X v × Y v` at the site
`v`. Its configurations are pairs of configurations of the two systems, along
`Equiv.arrowProdEquivProdArrow`, so an operator `A` on the first system and `B` on the second give
the operator `A ⊗ B` on the paired system. If `A` is supported on `S` and `B` on `T`, then
`A ⊗ B` is supported on `S ∪ T`. No basis type need be nonempty.

Generalizes TNLean's `QuantumCircuit.reindex_kronecker_mem_supportedOperators`
(`TNLean/Circuit/SitewiseTensorSupport.lean` at commit `414a18fb88`), which pairs the
alphabets `Fin d` and `Fin e` into `Fin (d * e)`; there the pairing of the alphabets is a
relabelling of the basis at every site.

### Main results

* `ManyBody.reindex_kronecker_mem_supportedOperators` — the support of `A ⊗ B`.
-/

open Matrix
open scoped Kronecker

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X Y : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] [∀ v, Fintype (Y v)] [∀ v, DecidableEq (Y v)]

/-- **The support of a paired product.** If `A` is supported on `S` and `B` on `T`, then
`A ⊗ B`, an operator on the system with basis `X v × Y v` at every site `v`, is supported on
`S ∪ T`. -/
theorem reindex_kronecker_mem_supportedOperators {S T : Finset V}
    {A : Matrix (Config X) (Config X) ℂ} {B : Matrix (Config Y) (Config Y) ℂ}
    (hA : A ∈ supportedOperators X S) (hB : B ∈ supportedOperators Y T) :
    reindex (Equiv.arrowProdEquivProdArrow V X Y).symm (Equiv.arrowProdEquivProdArrow V X Y).symm
        (A ⊗ₖ B) ∈ supportedOperators (fun v ↦ X v × Y v) (S ∪ T) := by
  have hentry (σ τ : (v : V) → X v × Y v) :
      reindex (Equiv.arrowProdEquivProdArrow V X Y).symm
          (Equiv.arrowProdEquivProdArrow V X Y).symm (A ⊗ₖ B) σ τ =
        A (fun v ↦ (σ v).1) (fun v ↦ (τ v).1) * B (fun v ↦ (σ v).2) (fun v ↦ (τ v).2) := by
    simp
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [Finset.mem_union, not_or] at hv
    rw [hentry]
    by_cases h : (σ v).1 = (τ v).1
    · rw [apply_eq_zero_of_mem_supportedOperators hB hv.2 fun h' ↦ hne (Prod.ext h h'), mul_zero]
    · rw [apply_eq_zero_of_mem_supportedOperators hA hv.1 h, zero_mul]
  · have hcases (v : V) : (σ v = σ' v ∧ τ v = τ' v) ∨ (σ v = τ v ∧ σ' v = τ' v) := by
      by_cases hST : v ∈ S ∪ T
      · exact Or.inl ⟨h1 v hST, h2 v hST⟩
      · exact Or.inr ⟨h3 v hST, h4 v hST⟩
    rw [hentry, hentry,
      hA.apply_eq (fun v hv ↦ by rw [h1 v (Finset.mem_union_left T hv)])
        (fun v hv ↦ by rw [h2 v (Finset.mem_union_left T hv)])
        (fun v _ ↦ by rcases hcases v with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp [h, h']),
      hB.apply_eq (fun v hv ↦ by rw [h1 v (Finset.mem_union_right S hv)])
        (fun v hv ↦ by rw [h2 v (Finset.mem_union_right S hv)])
        (fun v _ ↦ by rcases hcases v with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp [h, h'])]

end ManyBody

end SitewiseProduct

section SupportedComplementProduct

/-!
## Support of ordered complementary products

For operators `h_k`, the ordered product `(1 - h_{n-1}) ⋯ (1 - h_0)` of their complements
(`ContinuousLinearMap.complementProd`) is supported on every region on which all the `h_k` are
supported. No commutativity, projection or positivity assumption is needed. This is the support
argument for the regional parity products in ALVV, arXiv:1602.08828v2, `thm:FF-tH`,
lines 1543–1568.

Moved from TNLean, `TNLean/Circuit/SupportedComplementProduct.lean` at commit `49b78ed821`
(Apache-2.0). Changes: any finite set of sites with any basis at every site, in place of one
local dimension `q`.
-/

open ManyBody

namespace QuantumCircuit

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

local notation "T" => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Config X)

/-- An ordered complementary product belongs to the same supported-operator algebra as each
selected term. ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`, lines 1467–1487 and
1543–1568. -/
theorem mem_supportedOperators_complementProd
    (h : ℕ → EuclideanSpace ℂ (Config X) →L[ℂ] EuclideanSpace ℂ (Config X))
    (S : Finset V) (n : ℕ)
    (hh : ∀ k, k < n → (T).symm (h k) ∈ supportedOperators X S) :
    (T).symm (ContinuousLinearMap.complementProd h n) ∈ supportedOperators X S := by
  induction n with
  | zero =>
    simpa only [ContinuousLinearMap.complementProd_zero, map_one] using
      (one_mem (supportedOperators X S))
  | succ n ih =>
    rw [ContinuousLinearMap.complementProd_succ, map_mul, map_sub, map_one]
    exact mul_mem
      (sub_mem (one_mem (supportedOperators X S))
        (hh n (Nat.lt_succ_self n))) (ih fun k hk ↦ hh k (Nat.lt_succ_of_lt hk))

end QuantumCircuit

end SupportedComplementProduct
