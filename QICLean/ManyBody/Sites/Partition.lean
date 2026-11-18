/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Config
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Configurations along a partition into blocks

Let the sites outside a region `D` be partitioned into blocks `r b`. A configuration of the
sites outside `D` is then the same as a family of configurations, one on each block. Sums of
products over the blocks therefore factor: summing over the configurations outside `D` a
product of functions of the blocks gives the product of the sums over each block.

This is the computation behind the locality of a layer of a circuit, whose Kraus operators are
products of local entries over its cells and its remaining sites.

The same module records that a system glued from two families by `Sum.elim`, such as data
qubits and ancillas, has finite basis types with decidable equality when both families do.

## Main definitions

* `ManyBody.complPartitionEquiv` — configurations outside `D` as families over the blocks.

## Main results

* `ManyBody.sum_prod_complPartition` — a sum of products over the blocks factors.
* `ManyBody.prod_ite_complPartition` — two configurations agree outside `D` exactly when they
  agree on every block.
-/

namespace ManyBody

variable {V : Type*} {X : V → Type*} {B : Type*}

/-- A partition of the sites outside `D` into the blocks `r b`: every such site `v` lies in the
block `blk v`, and only in it, and every block is disjoint from `D`. -/
structure IsComplPartition (D : Finset V) (r : B → Finset V) (blk : {v // v ∉ D} → B) :
    Prop where
  /-- Every block is disjoint from `D`. -/
  disjoint : ∀ b, Disjoint (r b) D
  /-- Every site outside `D` lies in its block. -/
  mem : ∀ v, v.1 ∈ r (blk v)
  /-- A site lies only in its own block. -/
  eq_of_mem : ∀ v b, v.1 ∈ r b → blk v = b

variable {D : Finset V} {r : B → Finset V} {blk : {v // v ∉ D} → B}

/-- The restriction of a configuration outside `D` to a block disjoint from `D`. -/
def complRestrict (h : ∀ b, Disjoint (r b) D) (w : ComplConfig X D) (b : B) :
    RegionConfig X (r b) :=
  fun v ↦ w ⟨v, Finset.disjoint_left.mp (h b) v.2⟩

/-- Configurations outside `D` are families of configurations of the blocks. -/
def complPartitionEquiv (h : IsComplPartition D r blk) :
    ComplConfig X D ≃ ((b : B) → RegionConfig X (r b)) where
  toFun w := complRestrict h.disjoint w
  invFun F v := F (blk v) ⟨v, h.mem v⟩
  left_inv _ := rfl
  right_inv F := by
    funext b v
    obtain ⟨v, hv⟩ := v
    have key : ∀ b' (_ : b' = b) (hv' : v ∈ r b'), F b' ⟨v, hv'⟩ = F b ⟨v, hv⟩ := by
      rintro b' rfl _; rfl
    exact key _ (h.eq_of_mem ⟨v, Finset.disjoint_left.mp (h.disjoint b) hv⟩ b hv) _

/-- A sum over the configurations outside `D` of a product of functions of the blocks is the
product over the blocks of the sums over their configurations. -/
theorem sum_prod_complPartition {R : Type*} [CommSemiring R] [Fintype B]
    [∀ b, Fintype (RegionConfig X (r b))] [Fintype (ComplConfig X D)]
    (h : IsComplPartition D r blk) (f : (b : B) → RegionConfig X (r b) → R) :
    ∑ w : ComplConfig X D, ∏ b, f b (complRestrict h.disjoint w b) =
      ∏ b, ∑ z : RegionConfig X (r b), f b z := by
  classical
  rw [Fintype.prod_sum]
  exact (complPartitionEquiv h).sum_comp fun F ↦ ∏ b, f b (F b)

/-- Two configurations outside `D` are equal exactly when they agree on every block, written
as a product of indicators. -/
theorem prod_ite_complPartition {R : Type*} [CommSemiring R] [Fintype B]
    [∀ b, DecidableEq (RegionConfig X (r b))] [DecidableEq (ComplConfig X D)]
    (h : IsComplPartition D r blk) (w w' : ComplConfig X D) :
    (∏ b, if complRestrict h.disjoint w b = complRestrict h.disjoint w' b then (1 : R) else 0) =
      if w = w' then 1 else 0 := by
  by_cases hw : w = w'
  · simp [hw]
  · simp only [hw, ↓reduceIte]
    have : complRestrict h.disjoint w ≠ complRestrict h.disjoint w' :=
      fun he ↦ hw ((complPartitionEquiv h).injective he)
    obtain ⟨b, hb⟩ := Function.ne_iff.mp this
    exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [hb])

end ManyBody

/-! ### Systems glued from two families -/

section SumElim

universe u
variable {A B : Type*} {F : A → Type u} {H : B → Type u}

/-- A system glued from two families of finite basis types has finite basis types. -/
instance ManyBody.instFintypeSumElim [∀ a, Fintype (F a)] [∀ b, Fintype (H b)] :
    ∀ s, Fintype (Sum.elim F H s)
  | .inl a => inferInstanceAs (Fintype (F a))
  | .inr b => inferInstanceAs (Fintype (H b))

/-- A system glued from two families of basis types with decidable equality has basis types
with decidable equality. -/
instance ManyBody.instDecidableEqSumElim [∀ a, DecidableEq (F a)] [∀ b, DecidableEq (H b)] :
    ∀ s, DecidableEq (Sum.elim F H s)
  | .inl a => inferInstanceAs (DecidableEq (F a))
  | .inr b => inferInstanceAs (DecidableEq (H b))

end SumElim
