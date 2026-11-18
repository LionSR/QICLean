/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Placement
import QICLean.Algebra.L2OpNormReindex

/-!
# Placement into a larger region

For regions `R ⊆ U`, a matrix `K` on the configurations of `R` extends to the matrix
`ManyBody.subregionPlace hRU K` on the configurations of `U`, which acts as `K` on the sites of
`R` and as the identity on the sites of `U` outside `R`. Placing the extension on the whole
system gives the placement of `K` (`ManyBody.place_subregionPlace`): placement factors through
any larger region.

The extension is a placement in its own right. The sites of `U` form a system of sites
`{v // v ∈ U}` with basis types `fun w ↦ X w.1`, whose configurations are those of the region
`U`, and `R` is the region `R.subtype (· ∈ U)` of that system.
`ManyBody.subregionPlace hRU K` is the placement there of `K`, relabelled along
`ManyBody.subregionConfigEquiv hRU`. The algebraic lemmas, the norm bound and the support
statement are therefore those of `ManyBody.place`.

No basis type need be nonempty. In contrast, writing `place R K` as a placement on `U` through
`ManyBody.exists_eq_place_of_mem_supportedOperators` and `ManyBody.supportedOperators_mono`
needs a reference configuration.

## Main definitions

* `ManyBody.subregionConfigEquiv` — configurations of `R` as configurations of the region
  `R.subtype (· ∈ U)` of the system of sites of `U`.
* `ManyBody.subregionPlace` — the extension of a matrix on `R` to `U` by the identity.

## Main results

* `ManyBody.subregionPlace_apply` — its entries.
* `ManyBody.place_subregionPlace` — `place U (subregionPlace hRU K) = place R K`.
* `ManyBody.subregionPlace_subregionPlace` — transitivity for `R ⊆ U ⊆ W`.
* `ManyBody.subregionPlace_self` — the extension to `R` itself is the identity map.
* The algebraic lemmas, `ManyBody.norm_subregionPlace_le` and
  `ManyBody.subregionPlace_mem_supportedOperators`.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, DecidableEq (X v)]
  {R U W : Finset V}

omit [Fintype V] [∀ v, DecidableEq (X v)] in
/-- The configurations of a region `R ⊆ U` are the configurations of the region
`R.subtype (· ∈ U)` of the system of sites of `U`. -/
def subregionConfigEquiv (hRU : R ⊆ U) :
    RegionConfig X R ≃ RegionConfig (fun w : {v // v ∈ U} ↦ X w.1) (R.subtype (· ∈ U)) where
  toFun a w := a ⟨w.1.1, Finset.mem_subtype.mp w.2⟩
  invFun b v := b ⟨⟨v.1, hRU v.2⟩, Finset.mem_subtype.mpr v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The extension `K ↦ K ⊗ 1` of a matrix on the configurations of `R ⊆ U` to the
configurations of `U`, by the identity on the sites of `U` outside `R`. It is the placement of
`K` in the system of sites of `U`. -/
noncomputable def subregionPlace (hRU : R ⊆ U)
    (K : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) :
    Matrix (RegionConfig X U) (RegionConfig X U) ℂ :=
  place (X := fun w : {v // v ∈ U} ↦ X w.1) (R.subtype (· ∈ U))
    (reindex (subregionConfigEquiv hRU) (subregionConfigEquiv hRU) K)

omit [Fintype V] in
/-- Entries of the extension: the entry of `K` at the parts on `R` when the two configurations
agree on the sites of `U` outside `R`, and zero otherwise. -/
theorem subregionPlace_apply (hRU : R ⊆ U)
    (K : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) (α β : RegionConfig X U) :
    subregionPlace hRU K α β =
      if ∀ w : {v // v ∈ U}, w.1 ∉ R → α w = β w then
        K (fun w ↦ α ⟨w.1, hRU w.2⟩) (fun w ↦ β ⟨w.1, hRU w.2⟩)
      else 0 := by
  rw [subregionPlace, place_apply]
  exact if_congr ⟨fun h w hw ↦ h w (by simpa using hw), fun h w hw ↦ h w (by simpa using hw)⟩
    rfl rfl

/-- **Nested placement.** Placing the extension of `K` from `R` to `U` on the whole system gives
the placement of `K`. -/
theorem place_subregionPlace (hRU : R ⊆ U)
    (K : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) :
    place U (subregionPlace hRU K) = place R K := by
  ext σ τ
  rw [place_apply, place_apply, subregionPlace_apply]
  split_ifs with hU hUR hR hR hR
  · rfl
  · push Not at hR
    obtain ⟨v, hvR, hne⟩ := hR
    by_cases hvU : v ∈ U
    · exact absurd (hUR ⟨v, hvU⟩ hvR) hne
    · exact absurd (hU v hvU) hne
  · exact absurd (fun (w : {v // v ∈ U}) hw ↦ hR w.1 hw) hUR
  · rfl
  · exact absurd (fun v hvU ↦ hR v fun hvR ↦ hvU (hRU hvR)) hU
  · rfl

/-- Every placement on `R ⊆ U` is a placement on `U`. -/
theorem exists_place_eq_place_of_subset (hRU : R ⊆ U)
    (K : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) :
    ∃ L : Matrix (RegionConfig X U) (RegionConfig X U) ℂ, place R K = place U L :=
  ⟨subregionPlace hRU K, (place_subregionPlace hRU K).symm⟩

omit [Fintype V] in
/-- Extending from a region to itself does nothing. -/
@[simp]
theorem subregionPlace_self (K : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) :
    subregionPlace (subset_refl R) K = K := by
  ext α β
  rw [subregionPlace_apply, ite_eq_left_of_eq_true _ _ (eq_true fun w hw ↦ absurd w.2 hw)]

omit [Fintype V] in
/-- **Transitivity.** Extending from `R` to `U` and then to `W` is extending from `R` to
`W`. -/
theorem subregionPlace_subregionPlace (hRU : R ⊆ U) (hUW : U ⊆ W)
    (K : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) :
    subregionPlace hUW (subregionPlace hRU K) = subregionPlace (hRU.trans hUW) K := by
  ext α β
  rw [subregionPlace_apply, subregionPlace_apply, subregionPlace_apply]
  split_ifs with hU hUR hR hR hR
  · rfl
  · push Not at hR
    obtain ⟨w, hwR, hne⟩ := hR
    by_cases hwU : w.1 ∈ U
    · exact absurd (hUR ⟨w.1, hwU⟩ hwR) hne
    · exact absurd (hU w hwU) hne
  · exact absurd (fun (w : {v // v ∈ U}) hw ↦ hR ⟨w.1, hUW w.2⟩ hw) hUR
  · rfl
  · exact absurd (fun w hwU ↦ hR w fun hwR ↦ hwU (hRU hwR)) hU
  · rfl

/-! ### Algebra, norm and support -/

section Algebra

omit [Fintype V]

variable (hRU : R ⊆ U) (K K' : Matrix (RegionConfig X R) (RegionConfig X R) ℂ)

@[simp]
theorem subregionPlace_zero :
    subregionPlace hRU (0 : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) = 0 := by
  simp [subregionPlace]

theorem subregionPlace_add :
    subregionPlace hRU (K + K') = subregionPlace hRU K + subregionPlace hRU K' := by
  rw [subregionPlace, subregionPlace, subregionPlace, ← place_add]
  rfl

theorem subregionPlace_smul (c : ℂ) :
    subregionPlace hRU (c • K) = c • subregionPlace hRU K := by
  rw [subregionPlace, subregionPlace, ← place_smul]
  rfl

theorem subregionPlace_sub :
    subregionPlace hRU (K - K') = subregionPlace hRU K - subregionPlace hRU K' := by
  rw [subregionPlace, subregionPlace, subregionPlace, ← place_sub]
  rfl

theorem subregionPlace_conjTranspose :
    subregionPlace hRU Kᴴ = (subregionPlace hRU K)ᴴ := by
  rw [subregionPlace, subregionPlace, ← conjTranspose_reindex, place_conjTranspose]

@[simp]
theorem subregionPlace_one :
    subregionPlace hRU (1 : Matrix (RegionConfig X R) (RegionConfig X R) ℂ) = 1 := by
  classical
  rw [subregionPlace, reindex_apply, submatrix_one_equiv, place_one]

variable [∀ v, Fintype (X v)]

theorem subregionPlace_mul :
    subregionPlace hRU (K * K') = subregionPlace hRU K * subregionPlace hRU K' := by
  classical
  rw [subregionPlace, subregionPlace, subregionPlace, reindex_apply, reindex_apply,
    reindex_apply, ← submatrix_mul_equiv _ _ _ (subregionConfigEquiv hRU).symm, place_mul]

/-- The extension lies in the subalgebra of operators of the system of sites of `U` supported
on `R`. -/
theorem subregionPlace_mem_supportedOperators :
    subregionPlace hRU K ∈
      supportedOperators (fun w : {v // v ∈ U} ↦ X w.1) (R.subtype (· ∈ U)) :=
  place_mem_supportedOperators _

/-- Extension does not increase the operator norm. -/
theorem norm_subregionPlace_le : ‖subregionPlace hRU K‖ ≤ ‖K‖ := by
  classical
  refine (norm_place_le (X := fun w : {v // v ∈ U} ↦ X w.1) _).trans_eq ?_
  exact Matrix.l2_opNorm_reindex_equiv _ K

end Algebra

end ManyBody
