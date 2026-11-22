/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector

/-!
# Operators acting by maps of configurations

A permutation `σ` of the configurations of a system acts on vectors by its permutation matrix,
`(P_σ v)(x) = v (σ x)`. A permutation that changes only the sites of a set `S`, by a rule that
reads only the sites of `S`, has a permutation matrix supported on `S`
(`QuantumCircuit.IsLocalPerm.permMatrix_mem_supportedOperators`), and a product of on-site
permutation matrices permutes the label of every site (`Matrix.piKronecker_permMatrix_mulVec`).

More generally, a matrix `X` on `m` sites *acts by a configuration map* `f` when `X v = v ∘ f`
for every vector `v`; a permutation matrix acts this way (`Matrix.permMatrix_mulVec`). Placing
such matrices on pairwise disjoint sets of sites gives an operator that acts by the
configuration map changing each set of sites by its matrix and leaving the other sites alone
(`QuantumCircuit.noncommProd_placeAlong_mulVec_eq_comp`), with the case of a single matrix
(`QuantumCircuit.placeAlong_mulVec_eq_comp`). Controlled shifts, which add the value of one
register to another on computational basis states, are of this kind (arXiv:2103.13367,
Example 1; arXiv:2307.01696, the preparation of long-range states with measurements).

Moved from TNLean, `TNLean/Circuit/SitePermutation.lean`, `TNLean/Circuit/Gates/Permutation.lean`
and `TNLean/Circuit/ConfigurationLayers.lean` at commit `49b78ed821` (Apache-2.0). Changes: any
finite set of sites with any basis at every site for `QuantumCircuit.IsLocalPerm`, and any
finite set of sites with any common basis `α` in place of the chain `Fin n` with basis `Fin d`
for the configuration maps. The action of a product of on-site permutation matrices, with a
dependent family of bases over any finite set of sites, is `Matrix.piKronecker_permMatrix_mulVec`
in `QICLean.Algebra.Kronecker.PiKronecker`.

## Main definitions

* `QuantumCircuit.IsLocalPerm` — a permutation of configurations changing and reading only
  the sites of a set.
* `QuantumCircuit.layerCfg` — the configuration map of matrices placed on disjoint sets of
  sites.

## Main results

* `QuantumCircuit.IsLocalPerm.permMatrix_mem_supportedOperators`.
* `QuantumCircuit.noncommProd_placeAlong_mulVec_eq_comp`,
  `QuantumCircuit.placeAlong_mulVec_eq_comp`.
* `QuantumCircuit.placeAlong_mulVec_productVector` — a matrix applied to a product vector that
  is a basis vector `|z⟩` on its sites.

## References

* arXiv:2103.13367 (Piroli, Styliaris, Cirac), Example 1 (controlled shifts and single-site
  shifts).
-/

open Matrix ManyBody
open scoped BigOperators

namespace QuantumCircuit

/-! ### Permutations changing and reading only a set of sites -/

section LocalPerm

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- The permutation `σ` of the configurations changes only the sites of `S`, and the new values
at the sites of `S` depend only on the old values at the sites of `S`. -/
def IsLocalPerm (S : Finset V) (σ : Equiv.Perm (Config X)) : Prop :=
  (∀ x, ∀ v ∉ S, σ x v = x v) ∧
    ∀ x y, (∀ u ∈ S, x u = y u) → ∀ v ∈ S, σ x v = σ y v

omit [DecidableEq V] [∀ v, Fintype (X v)] in
private theorem permMatrix_cfg_apply (σ : Equiv.Perm (Config X)) (x y : Config X) :
    σ.permMatrix ℂ x y = if σ x = y then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/-- The permutation matrix of a permutation changing and reading only the sites of `S` is
supported on `S`. -/
theorem IsLocalPerm.permMatrix_mem_supportedOperators {S : Finset V}
    {σ : Equiv.Perm (Config X)} (h : IsLocalPerm S σ) :
    σ.permMatrix ℂ ∈ supportedOperators X S := by
  have key : ∀ x y x' y' : Config X, (∀ v ∈ S, x v = x' v) → (∀ v ∈ S, y v = y' v) →
      (∀ v ∉ S, x' v = y' v) → σ x = y → σ x' = y' := fun x y x' y' hx hy h' hσ ↦
    funext fun v ↦ by
      by_cases hv : v ∈ S
      · rw [h.2 x' x (fun u hu ↦ (hx u hu).symm) v hv, hσ, hy v hv]
      · rw [h.1 x' v hv, h' v hv]
  refine mem_supportedOperators_iff.mpr ⟨fun x y ⟨v, hv, hne⟩ ↦ ?_,
    fun x y x' y' h₁ h₂ h₃ h₄ ↦ ?_⟩
  · rw [permMatrix_cfg_apply, ite_eq_right_iff]
    rintro rfl
    exact absurd (h.1 x v hv).symm hne
  · rw [permMatrix_cfg_apply, permMatrix_cfg_apply]
    exact if_congr ⟨key x y x' y' h₁ h₂ h₄, key x' y' x y (fun v hv ↦ (h₁ v hv).symm)
      (fun v hv ↦ (h₂ v hv).symm) h₃⟩ rfl rfl

end LocalPerm

/-- An operator acting by a configuration map has the entry `1` at `(x, f x)` and `0`
elsewhere. -/
theorem apply_eq_ite_of_mulVec_eq_comp {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} {f : n → n} (hX : ∀ v, X *ᵥ v = v ∘ f) (x y : n) :
    X x y = if f x = y then 1 else 0 := by
  have h := congrFun (hX (Pi.single y 1)) x
  simpa [mulVec, dotProduct, Pi.single_apply] using h

/-! ### Matrices placed on disjoint sets of sites acting by configuration maps -/

variable {V : Type*} {α : Type*} {ι : Type*} {m : ι → ℕ}

/-- The sites of all the sets `e k`, indexed by pairs `(k, j)`. -/
def sigmaSite (e : ∀ k, Fin (m k) → V) : (Σ k, Fin (m k)) → V := fun p ↦ e p.1 p.2

theorem sigmaSite_injective {e : ∀ k, Fin (m k) → V} (he : ∀ k, Function.Injective (e k))
    (hdisj : ∀ k k', k ≠ k' → Disjoint (Set.range (e k)) (Set.range (e k'))) :
    Function.Injective (sigmaSite e) := by
  rintro ⟨k, j⟩ ⟨k', j'⟩ h
  by_cases hk : k = k'
  · subst hk
    obtain rfl : j = j' := he k h
    rfl
  · exact (Set.disjoint_left.mp (hdisj k k' hk) ⟨j, rfl⟩ ⟨j', h.symm⟩).elim

/-- The configuration map of matrices placed on disjoint sets of sites: on the sites `e k`, the
configuration is changed to `f k (x ∘ e k)`; the other sites keep their values. -/
noncomputable def layerCfg (e : ∀ k, Fin (m k) → V) (f : ∀ k, (Fin (m k) → α) → (Fin (m k) → α))
    (x : V → α) : V → α :=
  Function.extend (sigmaSite e) (fun p ↦ f p.1 (x ∘ e p.1) p.2) x

variable {e : ∀ k, Fin (m k) → V} (he : ∀ k, Function.Injective (e k))
  (hdisj : ∀ k k', k ≠ k' → Disjoint (Set.range (e k)) (Set.range (e k')))
  (f : ∀ k, (Fin (m k) → α) → (Fin (m k) → α))

include he hdisj in
theorem layerCfg_apply (x : V → α) (k : ι) (j : Fin (m k)) :
    layerCfg e f x (e k j) = f k (x ∘ e k) j :=
  (sigmaSite_injective he hdisj).extend_apply _ _ ⟨k, j⟩

include he hdisj in
theorem layerCfg_comp (x : V → α) (k : ι) : layerCfg e f x ∘ e k = f k (x ∘ e k) :=
  funext (layerCfg_apply he hdisj f x k)

theorem layerCfg_apply_of_forall_ne {x : V → α} {i : V} (hi : ∀ k j, e k j ≠ i) :
    layerCfg e f x i = x i :=
  Function.extend_apply' _ _ _ fun ⟨p, hp⟩ ↦ hi p.1 p.2 hp

include he hdisj in
theorem eq_layerCfg_iff (x y : V → α) :
    y = layerCfg e f x ↔
      (∀ i, (∀ k j, e k j ≠ i) → x i = y i) ∧ ∀ k, f k (x ∘ e k) = y ∘ e k := by
  constructor
  · rintro rfl
    exact ⟨fun i hi ↦ (layerCfg_apply_of_forall_ne f hi).symm,
      fun k ↦ (layerCfg_comp he hdisj f x k).symm⟩
  · rintro ⟨h1, h2⟩
    funext i
    by_cases hi : ∃ k j, e k j = i
    · obtain ⟨k, j, rfl⟩ := hi
      rw [layerCfg_apply he hdisj, h2 k]
      rfl
    · push Not at hi
      rw [layerCfg_apply_of_forall_ne f hi, h1 i hi]

variable [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α] [Fintype ι]

include he hdisj in
/-- **Placed matrices acting by configuration maps.** Matrices `X k` placed on pairwise disjoint
sets of sites `e k`, each acting by a configuration map `f k`, together act by
`layerCfg e f`. -/
theorem noncommProd_placeAlong_mulVec_eq_comp
    (X : ∀ k, Matrix (Fin (m k) → α) (Fin (m k) → α) ℂ) (hX : ∀ k v, X k *ᵥ v = v ∘ f k)
    (hcomm : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (Function.onFun Commute fun k ↦
        ManyBody.placeAlong (X := fun _ ↦ α) ⟨e k, he k⟩ (X k)))
    (v : (V → α) → ℂ) :
    Finset.univ.noncommProd (fun k ↦ ManyBody.placeAlong (X := fun _ ↦ α) ⟨e k, he k⟩ (X k))
        hcomm *ᵥ v = v ∘ layerCfg e f := by
  classical
  have happ := noncommProd_placeAlong_apply e he X Finset.univ
    (fun k _ k' _ h ↦ hdisj k k' h) hcomm
  funext x
  simp only [mulVec, dotProduct, Function.comp_apply, happ]
  rw [Finset.sum_eq_single (layerCfg e f x)]
  · have hx := (eq_layerCfg_iff he hdisj f x _).1 rfl
    rw [ite_eq_left fun i hi ↦ hx.1 i fun k j ↦ hi k (Finset.mem_univ k) j]
    simp [apply_eq_ite_of_mulVec_eq_comp (hX _), hx.2]
  · intro y _ hy
    split_ifs with h
    · have : ∃ k, f k (x ∘ e k) ≠ y ∘ e k := by
        by_contra hc
        push Not at hc
        exact hy ((eq_layerCfg_iff he hdisj f x y).2
          ⟨fun i hi ↦ h i fun k _ j ↦ hi k j, hc⟩)
      obtain ⟨k, hk⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ k)
        (by rw [apply_eq_ite_of_mulVec_eq_comp (hX k), ite_eq_right hk]), zero_mul]
    · rw [zero_mul]
  · simp

omit [Fintype ι] in
/-- A matrix on the sites `e₀`, acting by a configuration map `f₀`, acts by the configuration
map changing these sites by `f₀`. -/
theorem placeAlong_mulVec_eq_comp {m₀ : ℕ} {e₀ : Fin m₀ → V} (he₀ : Function.Injective e₀)
    {X : Matrix (Fin m₀ → α) (Fin m₀ → α) ℂ} {f₀ : (Fin m₀ → α) → (Fin m₀ → α)}
    (hX : ∀ v, X *ᵥ v = v ∘ f₀) (v : (V → α) → ℂ) :
    ManyBody.placeAlong (X := fun _ ↦ α) ⟨e₀, he₀⟩ X *ᵥ v =
      v ∘ layerCfg (fun _ : Unit ↦ e₀) fun _ ↦ f₀ := by
  have h := noncommProd_placeAlong_mulVec_eq_comp (ι := Unit) (m := fun _ ↦ m₀)
    (e := fun _ ↦ e₀) (fun _ ↦ he₀) (fun k k' h ↦ absurd (Subsingleton.elim k k') h)
    (fun _ ↦ f₀) (fun _ ↦ X) (fun _ ↦ hX) (fun _ _ _ _ h ↦ absurd (Subsingleton.elim _ _) h)
    v
  rwa [Finset.univ_unique, Finset.noncommProd_singleton] at h

omit [Fintype ι] in
/-- **A matrix applied to a product vector that is `|z⟩` on its sites.** If the site vectors of
`v` at the sites of `e₀` are `|z⟩`, then `(X ⊗ 1) |v⟩` has amplitude `X(y|_e, z ⋯ z)` times the
amplitude at `y` of the product vector with all-ones site vectors on the sites of `e₀`. -/
theorem placeAlong_mulVec_productVector {m₀ : ℕ} {e₀ : Fin m₀ → V} (he₀ : Function.Injective e₀)
    (X : Matrix (Fin m₀ → α) (Fin m₀ → α) ℂ) {v : V → α → ℂ} {z : α}
    (hv : ∀ j, v (e₀ j) = Pi.single z 1) (y : V → α) :
    (ManyBody.placeAlong (X := fun _ ↦ α) ⟨e₀, he₀⟩ X *ᵥ productVector v) y =
      X (y ∘ e₀) (fun _ ↦ z) *
        productVector (fun i ↦ if ∃ j, e₀ j = i then fun _ ↦ 1 else v i) y := by
  classical
  set w : V → α → ℂ := fun i ↦ if ∃ j, e₀ j = i then fun _ ↦ 1 else v i
  have hsplit : ∀ y', productVector v y' =
      (if y' ∘ e₀ = fun _ ↦ z then 1 else 0) * productVector w y' := fun y' ↦ by
    simp only [productVector]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i ↦ ∃ j, e₀ j = i),
      ← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ) (fun i ↦ ∃ j, e₀ j = i)
        (f := fun i ↦ w i (y' i))]
    have hw1 : ∏ i ∈ Finset.univ.filter (fun i ↦ ∃ j, e₀ j = i), w i (y' i) = 1 :=
      Finset.prod_eq_one fun i hi ↦ by
        rw [Finset.mem_filter] at hi; simp [w, hi.2]
    have hw2 : ∏ i ∈ Finset.univ.filter (fun i ↦ ¬∃ j, e₀ j = i), w i (y' i) =
        ∏ i ∈ Finset.univ.filter (fun i ↦ ¬∃ j, e₀ j = i), v i (y' i) :=
      Finset.prod_congr rfl fun i hi ↦ by
        rw [Finset.mem_filter] at hi; simp [w, hi.2]
    have hv1 : ∏ i ∈ Finset.univ.filter (fun i ↦ ∃ j, e₀ j = i), v i (y' i) =
        if y' ∘ e₀ = fun _ ↦ z then 1 else 0 := by
      have himg : Finset.univ.image e₀ = Finset.univ.filter (fun i ↦ ∃ j, e₀ j = i) := by
        ext i; simp
      rw [← himg, Finset.prod_image fun j _ j' _ h ↦ he₀ h]
      simp only [hv, Pi.single_apply]
      rw [Finset.prod_ite_zero]
      simp [funext_iff]
    rw [hw1, hw2, hv1, one_mul]
  have hoff : ∀ y', AgreeOff e₀ y y' → productVector w y' = productVector w y := fun y' h ↦ by
    simp only [productVector]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    by_cases hi : ∃ j, e₀ j = i
    · simp [w, hi]
    · rw [h i fun j hj ↦ hi ⟨j, hj⟩]
  have happ : ∀ x y' : V → α,
      ManyBody.placeAlong (X := fun _ ↦ α) ⟨e₀, he₀⟩ X x y' =
        if AgreeOff e₀ x y' then X (x ∘ e₀) (y' ∘ e₀) else 0 := fun x y' ↦
    (ManyBody.placeAlong_apply (X := fun _ ↦ α) ⟨e₀, he₀⟩ X x y').trans
      (by congr 1)
  set F : (Fin m₀ → α) → ℂ := fun u ↦ X (y ∘ e₀) u * (if u = fun _ ↦ z then 1 else 0) *
    productVector w y with hF
  rw [mulVec, dotProduct]
  refine (Finset.sum_congr rfl fun y' _ ↦ ?_).trans ((sum_agreeOff he₀ y F).trans ?_)
  · rw [happ, hsplit]
    by_cases h : AgreeOff e₀ y y'
    · rw [ite_eq_left h, ite_eq_left h, hoff y' h, hF]; ring
    · rw [ite_eq_right h, ite_eq_right h, zero_mul]
  · rw [Finset.sum_eq_single (fun _ ↦ z)]
    · simp [hF]
    · intro u _ hu; simp [hF, hu]
    · simp

end QuantumCircuit
