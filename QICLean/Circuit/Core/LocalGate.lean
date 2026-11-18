/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Layer
import QICLean.ManyBody.Sites.Placement
import QICLean.ManyBody.Sites.RegionUnion

/-!
# Gates from matrices on a local basis

A gate on a cell is a matrix on the configurations of the cell. Gates are usually written as
matrices on a smaller basis, such as `ℂ²` for a gate on one qubit or `ℂ² ⊗ ℂ²` for a gate on two,
and are transported to the cell along an equivalence of bases. For a cell `{a}` the
configurations are the basis of the site `a`, and for a cell `{a} ∪ {b}` with `a ≠ b` they are
pairs of basis vectors of `a` and `b`, the first factor at `a`.

The geometry of sites and ordered pairs has a cell for every site and for every ordered pair of
distinct sites; it is the geometry of circuits of one- and two-site gates with no locality
constraint.

## Main definitions

* `QuantumCircuit.siteEquiv`, `QuantumCircuit.pairEquiv` — the configurations of a site and of
  an ordered pair of distinct sites.
* `QuantumCircuit.KrausGate.ofMatrix` — the gate of one operator, a matrix on a local basis.
* `QuantumCircuit.Geometry.sitesAndPairs` — cells on every site and every ordered pair.

## Main results

* `QuantumCircuit.KrausGate.isUnitary_ofMatrix` — a unitary matrix gives a unitary gate.
* `QuantumCircuit.place_siteEquiv_mulVec`, `QuantumCircuit.place_pairEquiv_mulVec` — a matrix on
  one site, or on two, acting on a vector.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [DecidableEq S]

/-- The configurations of the region `{a}` are the basis of the site `a`. -/
def siteEquiv (X : S → Type) (a : S) : RegionConfig X {a} ≃ X a where
  toFun σ := σ ⟨a, Finset.mem_singleton_self a⟩
  invFun x v := (Finset.mem_singleton.mp v.2).symm ▸ x
  left_inv σ := by
    funext ⟨v, hv⟩
    obtain rfl := Finset.mem_singleton.mp hv
    rfl
  right_inv _ := rfl

/-- The configurations of the region `{a} ∪ {b}` of two distinct sites are pairs of basis
vectors, the first at `a`. -/
def pairEquiv (X : S → Type) {a b : S} (h : a ≠ b) :
    RegionConfig X ({a} ∪ {b}) ≃ X a × X b :=
  (regionUnionEquiv (Finset.disjoint_singleton.mpr h)).trans
    (Equiv.prodCongr (siteEquiv X a) (siteEquiv X b))

theorem pairEquiv_symm_apply_left (X : S → Type) {a b : S} (h : a ≠ b) (p : X a × X b) :
    (pairEquiv X h).symm p ⟨a, by simp⟩ = p.1 := by
  rw [pairEquiv, Equiv.symm_trans_apply]
  simp only [regionUnionEquiv, Equiv.coe_fn_symm_mk, Finset.mem_singleton_self, ↓reduceDIte,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_fst]
  rfl

theorem pairEquiv_symm_apply_right (X : S → Type) {a b : S} (h : a ≠ b) (p : X a × X b) :
    (pairEquiv X h).symm p ⟨b, by simp⟩ = p.2 := by
  rw [pairEquiv, Equiv.symm_trans_apply]
  simp only [regionUnionEquiv, Equiv.coe_fn_symm_mk, Finset.mem_singleton, Ne.symm h,
    ↓reduceDIte, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_snd]
  rfl

/-- The gate of one operator: the matrix `M` on a basis `β`, transported to the configurations
of the region `D` along `e`. -/
noncomputable def KrausGate.ofMatrix {D : Finset S} {X : S → Type} {β : Type}
    (e : RegionConfig X D ≃ β) (M : Matrix β β ℂ) : KrausGate D X X :=
  KrausFamily.single (M.submatrix e e)

/-- A unitary matrix on a local basis gives a unitary gate. -/
theorem KrausGate.isUnitary_ofMatrix {D : Finset S} {X : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] {β : Type} [Fintype β] [DecidableEq β]
    (e : RegionConfig X D ≃ β) {M : Matrix β β ℂ} (hM : M ∈ unitaryGroup β ℂ) :
    (KrausGate.ofMatrix e M).IsUnitary :=
  KrausFamily.isUnitary_single (submatrix_equiv_mem_unitary.mpr hM)

/-- A matrix placed on one site acts on a vector through the basis of that site. -/
theorem place_siteEquiv_mulVec [Fintype S] {X : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)]
    (a : S) (M : Matrix (X a) (X a) ℂ) (ψ : Config X → ℂ) (y : Config X) :
    (place {a} (M.submatrix (siteEquiv X a) (siteEquiv X a)) *ᵥ ψ) y =
      ∑ b : X a, M (y a) b * ψ (Function.update y a b) := by
  rw [place_mulVec_apply, ← (siteEquiv X a).symm.sum_comp]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [submatrix_apply, Equiv.apply_symm_apply]
  have hcut : (cutEquiv X {a}).symm ((siteEquiv X a).symm b, (cutEquiv X {a} y).2) =
      Function.update y a b := by
    funext v
    by_cases hv : v = a
    · subst hv
      rw [cutEquiv_symm_apply_mem _ _ (Finset.mem_singleton_self v), Function.update_self]
      rfl
    · rw [cutEquiv_symm_apply_not_mem _ _ (by simpa using hv), Function.update_of_ne hv]
      rfl
  rw [hcut]
  rfl

/-- A matrix placed on two distinct sites acts on a vector through the bases of the two sites. -/
theorem place_pairEquiv_mulVec [Fintype S] {X : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] {a b : S} (h : a ≠ b) (M : Matrix (X a × X b) (X a × X b) ℂ)
    (ψ : Config X → ℂ) (y : Config X) :
    (place ({a} ∪ {b}) (M.submatrix (pairEquiv X h) (pairEquiv X h)) *ᵥ ψ) y =
      ∑ q : X a × X b, M (y a, y b) q *
        ψ (Function.update (Function.update y a q.1) b q.2) := by
  rw [place_mulVec_apply, ← (pairEquiv X h).symm.sum_comp]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [submatrix_apply, Equiv.apply_symm_apply]
  have hcut : (cutEquiv X ({a} ∪ {b})).symm ((pairEquiv X h).symm q, (cutEquiv X ({a} ∪ {b}) y).2) =
      Function.update (Function.update y a q.1) b q.2 := by
    funext v
    by_cases hvb : v = b
    · subst hvb
      rw [cutEquiv_symm_apply_mem _ _ (by simp), Function.update_self]
      exact pairEquiv_symm_apply_right X h q
    · rw [Function.update_of_ne hvb]
      by_cases hva : v = a
      · subst hva
        rw [cutEquiv_symm_apply_mem _ _ (by simp), Function.update_self]
        exact pairEquiv_symm_apply_left X h q
      · rw [cutEquiv_symm_apply_not_mem _ _ (by simp [hva, hvb]), Function.update_of_ne hva]
        rfl
  rw [hcut]
  rfl

/-- The geometry with a cell on every site, at cost `c₁`, and on every ordered pair of distinct
sites `(a, b)`, the region `{a} ∪ {b}`, at cost `c₂`. -/
abbrev Geometry.sitesAndPairs (S : Type) [DecidableEq S] (c₁ c₂ : ℕ) : Geometry S where
  Cell := S ⊕ {p : S × S // p.1 ≠ p.2}
  cell
    | .inl a => {a}
    | .inr p => {p.1.1} ∪ {p.1.2}
  cost
    | .inl _ => c₁
    | .inr _ => c₂

instance [Fintype S] (c₁ c₂ : ℕ) : Fintype (Geometry.sitesAndPairs S c₁ c₂).Cell :=
  inferInstanceAs (Fintype (S ⊕ {p : S × S // p.1 ≠ p.2}))

theorem Geometry.mem_sitesAndPairs_cell_inl {c₁ c₂ : ℕ} {a v : S} :
    v ∈ (Geometry.sitesAndPairs S c₁ c₂).cell (.inl a) ↔ v = a :=
  Finset.mem_singleton

theorem Geometry.mem_sitesAndPairs_cell_inr {c₁ c₂ : ℕ} {p : {p : S × S // p.1 ≠ p.2}} {v : S} :
    v ∈ (Geometry.sitesAndPairs S c₁ c₂).cell (.inr p) ↔ v = p.1.1 ∨ v = p.1.2 := by
  simp

end QuantumCircuit
