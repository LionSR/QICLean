/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.LocalLift

/-!
# The algebra of operators supported on a region

On a finite tensor product `⊗_{v ∈ V} ℂ^{n_v}`, the operators supported on a region `D`,
those of the form `K ⊗ 1` with `K` acting on the sites of `D`, are closed under sums, scalar
multiples, products and adjoints, and contain the identity: they form a unital `*`-subalgebra
of the matrix algebra, isomorphic to the matrix algebra of the region. This file proves the
closure properties from the matrix-entry description `Entropy.IsSupportedOn` and packages them
as `Entropy.supportedOperators n D`.

No closure property requires the tensor product to be nonzero. When some `n_v` vanishes there
are no configurations and every statement holds trivially; the product and commutation lemmas
here treat that case, so they carry no reference configuration.

## Main definitions

* `Entropy.supportedOperators` — the `*`-subalgebra of operators supported on a region.

## Main results

* `Entropy.IsSupportedOn.zero`, `Entropy.IsSupportedOn.add`, `Entropy.IsSupportedOn.neg`,
  `Entropy.IsSupportedOn.sub`, `Entropy.IsSupportedOn.smul`, `Entropy.isSupportedOn_sum`.
* `Entropy.IsSupportedOn.conjTranspose`, `Entropy.isSupportedOn_one`.
* `Entropy.IsSupportedOn.mul_mem` — products, without a reference configuration.
* `Entropy.IsSupportedOn.commute_of_disjoint` — operators supported on disjoint regions
  commute, without a reference configuration.
* `Entropy.mem_supportedOperators` — membership in the subalgebra is the matrix-entry
  support condition.
* `Entropy.supportedOperators_mono`.
-/

open Matrix

namespace Entropy

variable {V : Type*} {n : V → ℕ} {D : Finset V}
  {X Y : Matrix (SiteConfig n) (SiteConfig n) ℂ}

/-! ### Linear structure and adjoints -/

/-- The zero operator is supported on every region. -/
theorem IsSupportedOn.zero (D : Finset V) :
    IsSupportedOn (0 : Matrix (SiteConfig n) (SiteConfig n) ℂ) D :=
  ⟨fun _ _ _ ↦ rfl, fun _ _ _ _ _ _ _ _ ↦ rfl⟩

/-- A sum of operators supported on `D` is supported on `D`. -/
theorem IsSupportedOn.add (hX : IsSupportedOn X D) (hY : IsSupportedOn Y D) :
    IsSupportedOn (X + Y) D := by
  refine ⟨fun σ τ h ↦ ?_, fun σ τ σ' τ' ha hb hc hd ↦ ?_⟩
  · rw [Matrix.add_apply, hX.1 σ τ h, hY.1 σ τ h, add_zero]
  · rw [Matrix.add_apply, Matrix.add_apply, hX.2 σ τ σ' τ' ha hb hc hd,
      hY.2 σ τ σ' τ' ha hb hc hd]

/-- The negative of an operator supported on `D` is supported on `D`. -/
theorem IsSupportedOn.neg (hX : IsSupportedOn X D) : IsSupportedOn (-X) D := by
  refine ⟨fun σ τ h ↦ ?_, fun σ τ σ' τ' ha hb hc hd ↦ ?_⟩
  · rw [Matrix.neg_apply, hX.1 σ τ h, neg_zero]
  · rw [Matrix.neg_apply, Matrix.neg_apply, hX.2 σ τ σ' τ' ha hb hc hd]

/-- A difference of operators supported on `D` is supported on `D`. -/
theorem IsSupportedOn.sub (hX : IsSupportedOn X D) (hY : IsSupportedOn Y D) :
    IsSupportedOn (X - Y) D := by
  rw [sub_eq_add_neg]
  exact hX.add hY.neg

/-- A scalar multiple of an operator supported on `D` is supported on `D`. -/
theorem IsSupportedOn.smul (hX : IsSupportedOn X D) (c : ℂ) : IsSupportedOn (c • X) D := by
  refine ⟨fun σ τ h ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · simp [hX.1 σ τ h]
  · simp [hX.2 σ τ σ' τ' h1 h2 h3 h4]

/-- A finite sum of operators supported on `D` is supported on `D`. -/
theorem isSupportedOn_sum {ι : Type*} (s : Finset ι)
    {h : ι → Matrix (SiteConfig n) (SiteConfig n) ℂ} (hs : ∀ i ∈ s, IsSupportedOn (h i) D) :
    IsSupportedOn (∑ i ∈ s, h i) D := by
  refine ⟨fun σ τ hστ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun i hi ↦ (hs i hi).1 σ τ hστ
  · rw [Matrix.sum_apply, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun i hi ↦ (hs i hi).2 σ τ σ' τ' h1 h2 h3 h4

/-- The adjoint of an operator supported on `D` is supported on `D`. -/
theorem IsSupportedOn.conjTranspose (hX : IsSupportedOn X D) : IsSupportedOn Xᴴ D := by
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [conjTranspose_apply, hX.1 τ σ ⟨v, hv, Ne.symm hne⟩, star_zero]
  · rw [conjTranspose_apply, conjTranspose_apply,
      hX.2 τ σ τ' σ' h2 h1 (fun v hv ↦ (h3 v hv).symm) (fun v hv ↦ (h4 v hv).symm)]

/-! ### Products and commutation -/

section Product

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The identity is supported on every region. -/
theorem isSupportedOn_one (D : Finset V) :
    IsSupportedOn (1 : Matrix (SiteConfig n) (SiteConfig n) ℂ) D := by
  classical
  rw [← localLift_one (D := D)]; exact isSupportedOn_localLift _

omit [Fintype V] [DecidableEq V] in
/-- `A ⊗ 1` and `1 ⊗ B` commute. -/
theorem kronecker_one_mul_one_kronecker_comm {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (KA : Matrix a a ℂ) (KB : Matrix b b ℂ) :
    KA.kroneckerMap (· * ·) (1 : Matrix b b ℂ) * (1 : Matrix a a ℂ).kroneckerMap (· * ·) KB =
      (1 : Matrix a a ℂ).kroneckerMap (· * ·) KB * KA.kroneckerMap (· * ·) (1 : Matrix b b ℂ) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul]; simp

/-- Operators supported on disjoint regions commute. -/
theorem commute_of_isSupportedOn_disjoint {D D' : Finset V}
    {X Y : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hX : IsSupportedOn X D)
    (hY : IsSupportedOn Y D') (hDD : Disjoint D' D) (σ₀ : SiteConfig n) : X * Y = Y * X := by
  have hcut : ∀ Z W : Matrix (SiteConfig n) (SiteConfig n) ℂ,
      cutOperator D (Z * W) = cutOperator D Z * cutOperator D W := fun Z W ↦ by
    simp [cutOperator, reindex_apply, submatrix_mul_equiv]
  have hX' := hX.cutOperator_eq_kronecker_one (B := D) subset_rfl ((cutEquiv n D) σ₀).2
  have hY' := hY.cutOperator_eq_one_kronecker hDD ((cutEquiv n D) σ₀).1
  have h : cutOperator D (X * Y) = cutOperator D (Y * X) := by
    rw [hcut, hcut, hX', hY']
    exact kronecker_one_mul_one_kronecker_comm _ _
  exact (reindex (cutEquiv n D) (cutEquiv n D)).injective h

omit [Fintype V] [DecidableEq V] in
/-- Without configurations, every operator is supported on every region. -/
theorem isSupportedOn_of_isEmpty [IsEmpty (SiteConfig n)]
    (X : Matrix (SiteConfig n) (SiteConfig n) ℂ) (D : Finset V) : IsSupportedOn X D :=
  ⟨fun σ ↦ isEmptyElim σ, fun σ ↦ isEmptyElim σ⟩

/-- Products of operators supported on `D` are supported on `D`. Unlike
`Entropy.IsSupportedOn.mul`, this takes no reference configuration. -/
theorem IsSupportedOn.mul_mem (hX : IsSupportedOn X D) (hY : IsSupportedOn Y D) :
    IsSupportedOn (X * Y) D := by
  cases isEmpty_or_nonempty (SiteConfig n) with
  | inl _ => exact isSupportedOn_of_isEmpty _ _
  | inr h => exact hX.mul hY h.some

/-- Operators supported on disjoint regions commute. Unlike
`Entropy.commute_of_isSupportedOn_disjoint`, this takes no reference configuration. -/
theorem IsSupportedOn.commute_of_disjoint {D' : Finset V} (hX : IsSupportedOn X D)
    (hY : IsSupportedOn Y D') (hDD : Disjoint D D') : Commute X Y := by
  cases isEmpty_or_nonempty (SiteConfig n) with
  | inl _ => exact Subsingleton.elim _ _
  | inr h => exact commute_of_isSupportedOn_disjoint hX hY hDD.symm h.some

end Product

/-! ### The subalgebra -/

section Subalgebra

variable [Fintype V] [DecidableEq V]

/-- The operators supported on the region `D`, as a unital `*`-subalgebra of the matrix
algebra on all the sites: the operators `K ⊗ 1` with `K` acting on the sites of `D`. -/
def supportedOperators (n : V → ℕ) (D : Finset V) :
    StarSubalgebra ℂ (Matrix (SiteConfig n) (SiteConfig n) ℂ) where
  carrier := {X | IsSupportedOn X D}
  mul_mem' hX hY := IsSupportedOn.mul_mem hX hY
  one_mem' := isSupportedOn_one D
  add_mem' hX hY := IsSupportedOn.add hX hY
  zero_mem' := IsSupportedOn.zero D
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (isSupportedOn_one D).smul c
  star_mem' hX := IsSupportedOn.conjTranspose hX

/-- Membership in the subalgebra of supported operators is the matrix-entry support
condition. -/
@[simp]
theorem mem_supportedOperators : X ∈ supportedOperators n D ↔ IsSupportedOn X D :=
  Iff.rfl

/-- The subalgebra of supported operators grows with the region. -/
theorem supportedOperators_mono {D' : Finset V} (h : D ⊆ D') :
    supportedOperators n D ≤ supportedOperators n D' :=
  fun _ hX ↦ IsSupportedOn.mono hX h

/-- A lifted regional matrix lies in the subalgebra of its region. -/
theorem localLift_mem_supportedOperators (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    localLift D K ∈ supportedOperators n D :=
  isSupportedOn_localLift K

/-- Powers of an operator supported on `D` are supported on `D`. -/
theorem IsSupportedOn.pow (hX : IsSupportedOn X D) (k : ℕ) : IsSupportedOn (X ^ k) D :=
  pow_mem (S := supportedOperators n D) hX k

end Subalgebra

end Entropy
