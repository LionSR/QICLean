/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Config
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

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
  `ManyBody.apply_eq_of_mem_supportedOperators` — the two halves of that condition in the
  form used in computations.
* `ManyBody.supportedOperators_mono`, `ManyBody.supportedOperators_univ`.

## Implementation notes

`ManyBody.IsSupportedOn` is the condition on matrix entries, stated without the finiteness and
decidability assumptions that the algebra structure of the matrices needs. It is the carrier
of the subalgebra and has no interface of its own.
-/

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
private theorem IsSupportedOn.mul (hA : IsSupportedOn A D) (hB : IsSupportedOn B D) :
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

/-- Entries of a supported operator agree whenever the configurations agree on the region and
have the same coincidence pattern outside it. -/
theorem apply_eq_of_mem_supportedOperators (hA : A ∈ supportedOperators X D)
    {σ τ σ' τ' : Config X} (h1 : ∀ v ∈ D, σ v = σ' v) (h2 : ∀ v ∈ D, τ v = τ' v)
    (h3 : ∀ v ∉ D, (σ v = τ v ↔ σ' v = τ' v)) : A σ τ = A σ' τ' := by
  by_cases h : ∃ v ∉ D, σ v ≠ τ v
  · obtain ⟨v, hv, hne⟩ := h
    rw [hA.1 σ τ ⟨v, hv, hne⟩, hA.1 σ' τ' ⟨v, hv, fun h' ↦ hne ((h3 v hv).mpr h')⟩]
  · push Not at h
    exact hA.2 σ τ σ' τ' h1 h2 h (fun v hv ↦ (h3 v hv).mp (h v hv))

/-- The subalgebra of supported operators grows with the region. -/
theorem supportedOperators_mono (h : D ⊆ D') :
    supportedOperators X D ≤ supportedOperators X D' := by
  intro A hA
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ hA.1 σ τ ⟨v, fun hvD ↦ hv (h hvD), hne⟩,
    fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  refine apply_eq_of_mem_supportedOperators hA (fun v hv ↦ h1 v (h hv))
    (fun v hv ↦ h2 v (h hv)) fun v hv ↦ ?_
  by_cases hv' : v ∈ D'
  · rw [h1 v hv', h2 v hv']
  · exact ⟨fun _ ↦ h4 v hv', fun _ ↦ h3 v hv'⟩

/-- Every operator is supported on the set of all sites. -/
@[simp]
theorem supportedOperators_univ : supportedOperators X Finset.univ = ⊤ :=
  top_unique fun A _ ↦ ⟨fun _ _ ⟨v, hv, _⟩ ↦ absurd (Finset.mem_univ v) hv,
    fun σ τ σ' τ' h1 h2 _ _ ↦ by
      rw [funext fun v ↦ h1 v (Finset.mem_univ v), funext fun v ↦ h2 v (Finset.mem_univ v)]⟩

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
    · refine apply_eq_of_mem_supportedOperators hB (fun v hv ↦ ?_) (fun v hv ↦ ?_)
        fun v hv ↦ ?_
      · rw [ite_eq_right (hD v hv)]
      · rw [ite_eq_left hv]
      · by_cases hvD : v ∈ D
        · simp [hvD, hv]
        · simp [hvD, hv, hστ v (by simp [hvD, hv])]
    · refine apply_eq_of_mem_supportedOperators hA (fun v hv ↦ ?_) (fun v hv ↦ ?_)
        fun v hv ↦ ?_
      · rw [ite_eq_right (hD' v hv)]
      · rw [ite_eq_left hv]
      · by_cases hvD' : v ∈ D'
        · simp [hvD', hv]
        · simp [hvD', hv, hστ v (by simp [hvD', hv])]

end ManyBody
