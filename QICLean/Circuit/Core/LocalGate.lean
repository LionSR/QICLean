/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Layer
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

/-- The gate of one operator: the matrix `M` on a basis `β`, transported to the configurations
of the region `D` along `e`. -/
noncomputable def KrausGate.ofMatrix {D : Finset S} {X : S → Type} {β : Type}
    (e : RegionConfig X D ≃ β) (M : Matrix β β ℂ) : KrausGate D X X :=
  KrausFamily.single (M.submatrix e e)

/-- A unitary matrix on a local basis gives a unitary gate. -/
theorem KrausGate.isUnitary_ofMatrix {D : Finset S} {X : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] {β : Type} [Fintype β] [DecidableEq β]
    (e : RegionConfig X D ≃ β) {M : Matrix β β ℂ} (hM : M ∈ unitaryGroup β ℂ) :
    (KrausGate.ofMatrix e M).IsUnitary := by
  have hU : M.submatrix e e ∈ unitaryGroup (RegionConfig X D) ℂ :=
    submatrix_equiv_mem_unitary.mpr hM
  refine ⟨⟨inferInstanceAs (Unique Unit)⟩, fun _ ↦ ⟨?_, ?_⟩⟩
  · exact (mem_unitaryGroup_iff'.mp hU)
  · exact (mem_unitaryGroup_iff.mp hU)

/-- The geometry with a cell on every site, at cost `c₁`, and on every ordered pair of distinct
sites `(a, b)`, the region `{a} ∪ {b}`, at cost `c₂`. -/
def Geometry.sitesAndPairs (S : Type) [DecidableEq S] (c₁ c₂ : ℕ) : Geometry S where
  Cell := S ⊕ {p : S × S // p.1 ≠ p.2}
  cell
    | .inl a => {a}
    | .inr p => {p.1.1} ∪ {p.1.2}
  cost
    | .inl _ => c₁
    | .inr _ => c₂

instance [Fintype S] (c₁ c₂ : ℕ) : Fintype (Geometry.sitesAndPairs S c₁ c₂).Cell :=
  inferInstanceAs (Fintype (S ⊕ {p : S × S // p.1 ≠ p.2}))

end QuantumCircuit
