/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Ring
import QICLean.Circuit.Protocol.Teleportation.Round

/-!
# Teleportation chains between distant sites

The tree-RG circuit of arXiv:2307.01696, eq. (16), applies isometries to registers that are far
apart on the chain. The paragraph "Tree-RG circuit with measurements" observes that these
registers "can be teleported at neighboring registers with a constant overhead". This file
provides the chains of hops that do so:

* for any valid lists of hops `there` and `back` and any unitary circuit `u`, the round
  teleporting along `there`, followed by the round applying `u` and teleporting along `back`,
  implements `P_back U P_there` (`QuantumCircuit.TeleportHop.isImplementationOn_round_comp_round`);
* on the ring of `N` sites, the forward chain of `L` hops from `a` to `a + 2L` and the backward
  chain from `a + 2L` to `a`, whose permutations of sites are inverse to each other
  (`QuantumCircuit.TeleportHop.sitePerm_backwardChain`); the forward chain leaves `|0⟩` at the
  sites `a, …, a + 2L - 1` when the sites `a + 1, …, a + 2L` carry `|0⟩`
  (`QuantumCircuit.TeleportHop.isZeroOn_sitePermOp_forwardChain`).

The gates between distant sites built from these chains are in
`QICLean.Circuit.Protocol.Teleportation.LongRangeGates`.

## Main definitions

* `QuantumCircuit.TeleportHop.chainHop`, `QuantumCircuit.TeleportHop.chainHopBack`,
  `QuantumCircuit.TeleportHop.forwardChain`, `QuantumCircuit.TeleportHop.backwardChain`.
* `QuantumCircuit.TeleportHop.After` — the relation between a hop and an earlier one.

## Main results

* `QuantumCircuit.TeleportHop.isImplementationOn_round_comp_round`.
* `QuantumCircuit.TeleportHop.valid_iff_pairwise`.
* `QuantumCircuit.TeleportHop.sitePerm_forwardChain`,
  `QuantumCircuit.TeleportHop.sitePerm_backwardChain`,
  `QuantumCircuit.TeleportHop.isZeroOn_sitePermOp_forwardChain`.

The declarations restate `TNLean/Circuit/Teleportation/Chains.lean` at commit `414a18fb88`
(Apache-2.0), with `allSites_backwardChain_subset` of
`TNLean/Circuit/Teleportation/LongRangeGates.lean`. The changes: the hops of the chains are hops
on `Geometry.ring N`, the cells `{k, k + 1}`; two rounds in sequence are `Circuit.comp`, and the
statement that every output is a multiple of `P_back U P_there v` is an implementation of the
composed circuit; the permutation matrices are `ManyBody.sitePermOp`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix ManyBody

namespace QuantumCircuit

namespace TeleportHop

section General

variable {S : Type} [DecidableEq S] {Γ : Geometry S}

/-- **Gates conjugated by teleportation.** Let `there` and `back` be valid lists of hops and `u`
a unitary circuit. The round teleporting along `there`, followed by the round applying `u` and
teleporting along `back`, implements `P_back U P_there` on the vectors `v` with `|0⟩` at the
sites `e`, `f` of `there` such that `U P_there v` has `|0⟩` at the sites `e`, `f` of `back`. The
rounds have depth at most `2` and `depth u + 2`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
theorem isImplementationOn_round_comp_round [Fintype S] {d : ℕ} [NeZero d]
    {there back : List (TeleportHop Γ)}
    (hthere : Valid there) (hback : Valid back) (u : UnitaryCircuit Γ (Qudits S d)) :
    ((round (UnitaryCircuit.id Γ _) there hthere).comp (round u back hback)).IsImplementationOn
      KrausGate.ev {v | IsZeroOn (pairSites there) v ∧
        IsZeroOn (pairSites back) (u.op *ᵥ (sitePermOp (sitePerm there) *ᵥ v))}
      (sitePermOp (sitePerm back) * u.op * sitePermOp (sitePerm there)) := by
  have h₁ := (isImplementationOn_round (UnitaryCircuit.id Γ (Qudits S d)) hthere).mono
    (E' := {v | IsZeroOn (pairSites there) v ∧
      IsZeroOn (pairSites back) (u.op *ᵥ (sitePermOp (sitePerm there) *ᵥ v))})
    fun v hv ↦ by simpa using hv.1
  have h := h₁.comp (isImplementationOn_round u hback) fun v hv ↦ by simpa using hv.2
  rwa [UnitaryCircuit.op_id, Matrix.mul_one] at h

/-- The hop `h` may follow the earlier hop `h'` in a valid list: the sites `e` and `f` of
`h` are not sites of `h'`, and the site `c` of `h` is not the site `c` or `e` of `h'`. -/
def After (h h' : TeleportHop Γ) : Prop :=
  h.e ∉ h'.sites ∧ h.f ∉ h'.sites ∧ h.c ≠ h'.c ∧ h.c ≠ h'.e

theorem valid_iff_pairwise {hs : List (TeleportHop Γ)} : Valid hs ↔ hs.Pairwise After := by
  induction hs with
  | nil => simp [Valid]
  | cons h hs ih =>
    rw [List.pairwise_cons, ← ih]
    constructor
    · rintro ⟨hv, he, hf, hc⟩
      exact ⟨fun h' hh' ↦ ⟨fun hi ↦ he (mem_allSites.mpr ⟨h', hh', hi⟩),
        fun hi ↦ hf (mem_allSites.mpr ⟨h', hh', hi⟩), (hc h' hh').1, (hc h' hh').2⟩, hv⟩
    · rintro ⟨hR, hv⟩
      refine ⟨hv, fun hi ↦ ?_, fun hi ↦ ?_, fun h' hh' ↦ ⟨(hR h' hh').2.2.1, (hR h' hh').2.2.2⟩⟩
      · obtain ⟨h', hh', hi⟩ := mem_allSites.mp hi; exact (hR h' hh').1 hi
      · obtain ⟨h', hh', hi⟩ := mem_allSites.mp hi; exact (hR h' hh').2.1 hi

theorem sitePerm_append (hs hs' : List (TeleportHop Γ)) :
    sitePerm (hs ++ hs') = sitePerm hs * sitePerm hs' := by
  induction hs with
  | nil => simp [sitePerm]
  | cons h hs ih => rw [List.cons_append, sitePerm, sitePerm, ih, mul_assoc]

theorem pairSites_append (hs hs' : List (TeleportHop Γ)) :
    pairSites (hs ++ hs') = pairSites hs ∪ pairSites hs' := by
  induction hs with
  | nil => simp [pairSites]
  | cons h hs ih => rw [List.cons_append, pairSites, pairSites, ih, Finset.union_assoc]

end General

end TeleportHop

variable {N : ℕ} [NeZero N]

/-! ### The sites `a + j` of the ring -/

section Offsets

open Fin.NatCast

theorem add_natCast_injective (a : Fin N) {j k : ℕ} (hj : j < N) (hk : k < N)
    (h : a + (j : Fin N) = a + (k : Fin N)) : j = k := by
  have := congrArg Fin.val (add_left_cancel h)
  rwa [Fin.val_cast_of_lt hj, Fin.val_cast_of_lt hk] at this

theorem add_natCast_succ (a : Fin N) (j : ℕ) :
    a + (j : Fin N) + 1 = a + ((j + 1 : ℕ) : Fin N) := by
  rw [add_assoc, Nat.cast_succ]

/-- The sites `a + j` and `a + k` differ when `j ≠ k`, both offsets below `N`. -/
theorem add_natCast_ne (a : Fin N) {j k : ℕ} (hj : j < N) (hk : k < N) (hjk : j ≠ k) :
    a + (j : Fin N) ≠ a + (k : Fin N) :=
  fun h ↦ hjk (add_natCast_injective a hj hk h)

end Offsets

namespace TeleportHop

/-! ### The chains between two distant sites of the ring -/

section Chains

open Fin.NatCast

/-- The forward hop from `a + j` to `a + j + 2` on the ring. -/
def chainHop (a : Fin N) (j : ℕ) (hj : j + 2 < N) : TeleportHop (Geometry.ring N) where
  c := a + (j : Fin N)
  e := a + ((j + 1 : ℕ) : Fin N)
  f := a + ((j + 2 : ℕ) : Fin N)
  b₁ := a + ((j + 1 : ℕ) : Fin N)
  b₂ := a + (j : Fin N)
  cell_b₁ := by rw [Geometry.ring_cell, add_natCast_succ]
  cell_b₂ := by rw [Geometry.ring_cell, add_natCast_succ]
  c_ne_e h := by have := add_natCast_injective a (by omega) (by omega) h; omega
  c_ne_f h := by have := add_natCast_injective a (by omega) (by omega) h; omega
  e_ne_f h := by have := add_natCast_injective a (by omega) (by omega) h; omega

/-- The backward hop from `a + j + 2` to `a + j` on the ring. -/
def chainHopBack (a : Fin N) (j : ℕ) (hj : j + 2 < N) : TeleportHop (Geometry.ring N) where
  c := a + ((j + 2 : ℕ) : Fin N)
  e := a + ((j + 1 : ℕ) : Fin N)
  f := a + (j : Fin N)
  b₁ := a + (j : Fin N)
  b₂ := a + ((j + 1 : ℕ) : Fin N)
  cell_b₁ := by rw [Geometry.ring_cell, add_natCast_succ, Finset.pair_comm]
  cell_b₂ := by rw [Geometry.ring_cell, add_natCast_succ, Finset.pair_comm]
  c_ne_e h := by have := add_natCast_injective a (by omega) (by omega) h; omega
  c_ne_f h := by have := add_natCast_injective a (by omega) (by omega) h; omega
  e_ne_f h := by have := add_natCast_injective a (by omega) (by omega) h; omega

/-- The forward chain of `L` hops from `a` to `a + 2L`, the most recent hop first. -/
def forwardChain (a : Fin N) : (L : ℕ) → 2 * L < N → List (TeleportHop (Geometry.ring N))
  | 0, _ => []
  | L + 1, hL => chainHop a (2 * L) (by omega) :: forwardChain a L (by omega)

/-- The backward chain of `L` hops from `a + 2L` to `a`, the most recent hop first. -/
def backwardChain (a : Fin N) : (L : ℕ) → 2 * L < N → List (TeleportHop (Geometry.ring N))
  | 0, _ => []
  | L + 1, hL => backwardChain a L (by omega) ++ [chainHopBack a (2 * L) (by omega)]

theorem mem_forwardChain {a : Fin N} {L : ℕ} {hL : 2 * L < N} {h : TeleportHop (Geometry.ring N)}
    (hh : h ∈ forwardChain a L hL) : ∃ i < L, ∃ hi, h = chainHop a (2 * i) hi := by
  induction L with
  | zero => simp [forwardChain] at hh
  | succ L ih =>
    rcases List.mem_cons.mp hh with rfl | hh
    · exact ⟨L, by omega, _, rfl⟩
    · obtain ⟨i, hi, hi', rfl⟩ := ih hh
      exact ⟨i, by omega, hi', rfl⟩

theorem mem_backwardChain {a : Fin N} {L : ℕ} {hL : 2 * L < N}
    {h : TeleportHop (Geometry.ring N)} (hh : h ∈ backwardChain a L hL) :
    ∃ i < L, ∃ hi, h = chainHopBack a (2 * i) hi := by
  induction L with
  | zero => simp [backwardChain] at hh
  | succ L ih =>
    rcases List.mem_append.mp hh with hh | hh
    · obtain ⟨i, hi, hi', rfl⟩ := ih hh
      exact ⟨i, by omega, hi', rfl⟩
    · rw [List.mem_singleton] at hh
      exact ⟨L, by omega, _, hh⟩

theorem valid_forwardChain (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    Valid (forwardChain a L hL) := by
  rw [valid_iff_pairwise]
  induction L with
  | zero => exact List.Pairwise.nil
  | succ L ih =>
    refine List.Pairwise.cons (fun h' hh' ↦ ?_) (ih (by omega))
    obtain ⟨i, hi, hi', rfl⟩ := mem_forwardChain hh'
    simp only [After, sites, chainHop, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      exact add_natCast_ne a (by omega) (by omega) (by omega)

theorem valid_backwardChain (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    Valid (backwardChain a L hL) := by
  rw [valid_iff_pairwise]
  induction L with
  | zero => exact List.Pairwise.nil
  | succ L ih =>
    refine List.pairwise_append.mpr ⟨ih (by omega), List.pairwise_singleton _ _,
      fun h' hh' h'' hh'' ↦ ?_⟩
    obtain ⟨i, hi, hi', rfl⟩ := mem_backwardChain hh'
    rw [List.mem_singleton] at hh''
    subst hh''
    simp only [After, sites, chainHopBack, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      exact add_natCast_ne a (by omega) (by omega) (by omega)

/-- The forward chain moves `a` to `a + 2L` and fixes the sites `a + j` with `2L < j < N`. -/
theorem sitePerm_forwardChain (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    sitePerm (forwardChain a L hL) a = a + ((2 * L : ℕ) : Fin N) ∧
      ∀ j, 2 * L < j → j < N → sitePerm (forwardChain a L hL) (a + (j : Fin N)) =
        a + (j : Fin N) := by
  induction L with
  | zero => simp [forwardChain, sitePerm]
  | succ L ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    simp only [forwardChain, sitePerm, chainHop, Equiv.Perm.mul_apply]
    refine ⟨?_, fun j hj hjN ↦ ?_⟩
    · rw [h1, Equiv.swap_apply_left]
      congr 2
    · rw [h2 j (by omega) hjN, Equiv.swap_apply_of_ne_of_ne
        (add_natCast_ne a hjN (by omega) (by omega)) (add_natCast_ne a hjN (by omega) (by omega))]

theorem sitePerm_backwardChain (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    sitePerm (backwardChain a L hL) = (sitePerm (forwardChain a L hL))⁻¹ := by
  induction L with
  | zero => simp [forwardChain, backwardChain, sitePerm]
  | succ L ih =>
    rw [backwardChain, sitePerm_append, ih (by omega), forwardChain]
    simp only [sitePerm, mul_one, _root_.mul_inv_rev, Equiv.swap_inv]
    congr 1
    exact Equiv.swap_comm _ _

/-- The sites `e` and `f` of the forward chain lie among the sites `a + j`, `1 ≤ j ≤ 2L`. -/
theorem pairSites_forwardChain_subset (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    pairSites (forwardChain a L hL) ⊆
      (Finset.Icc 1 (2 * L)).image fun j : ℕ ↦ a + (j : Fin N) := by
  induction L with
  | zero => simp [forwardChain, pairSites]
  | succ L ih =>
    intro i hi
    simp only [forwardChain, pairSites, chainHop, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hi
    simp only [Finset.mem_image, Finset.mem_Icc]
    rcases hi with (rfl | rfl) | hi
    · exact ⟨2 * L + 1, ⟨by omega, by omega⟩, rfl⟩
    · exact ⟨2 * L + 2, ⟨by omega, by omega⟩, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (ih (by omega) hi)
      rw [Finset.mem_Icc] at hj
      exact ⟨j, ⟨hj.1, by omega⟩, rfl⟩

/-- The sites `e` and `f` of the backward chain lie among the sites `a + j`, `j < 2L`. -/
theorem pairSites_backwardChain_subset (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    pairSites (backwardChain a L hL) ⊆
      (Finset.range (2 * L)).image fun j : ℕ ↦ a + (j : Fin N) := by
  induction L with
  | zero => simp [backwardChain, pairSites]
  | succ L ih =>
    rw [backwardChain, pairSites_append]
    intro i hi
    simp only [pairSites, chainHopBack, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.union_empty] at hi
    simp only [Finset.mem_image, Finset.mem_range]
    rcases hi with hi | rfl | rfl
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (ih (by omega) hi)
      exact ⟨j, by simp at hj; omega, rfl⟩
    · exact ⟨2 * L + 1, by omega, rfl⟩
    · exact ⟨2 * L, by omega, rfl⟩

/-- The sites of the forward chain lie among the sites `a + j`, `j ≤ 2L`. -/
theorem allSites_forwardChain_subset (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    allSites (forwardChain a L hL) ⊆
      (Finset.range (2 * L + 1)).image fun j : ℕ ↦ a + (j : Fin N) := by
  intro i hi
  obtain ⟨h, hh, hi⟩ := mem_allSites.mp hi
  obtain ⟨k, hk, hk', rfl⟩ := mem_forwardChain hh
  simp only [sites, chainHop, Finset.mem_insert, Finset.mem_singleton] at hi
  simp only [Finset.mem_image, Finset.mem_range]
  rcases hi with rfl | rfl | rfl
  · exact ⟨2 * k, by omega, rfl⟩
  · exact ⟨2 * k + 1, by omega, rfl⟩
  · exact ⟨2 * k + 2, by omega, rfl⟩

/-- The sites of the backward chain lie among the sites `a + j`, `j ≤ 2L`. -/
theorem allSites_backwardChain_subset (a : Fin N) (L : ℕ) (hL : 2 * L < N) :
    allSites (backwardChain a L hL) ⊆
      (Finset.range (2 * L + 1)).image fun j : ℕ ↦ a + (j : Fin N) := by
  intro i hi
  obtain ⟨h, hh, hi⟩ := mem_allSites.mp hi
  obtain ⟨k, hk, hk', rfl⟩ := mem_backwardChain hh
  simp only [sites, chainHopBack, Finset.mem_insert, Finset.mem_singleton] at hi
  simp only [Finset.mem_image, Finset.mem_range]
  rcases hi with rfl | rfl | rfl
  · exact ⟨2 * k + 2, by omega, rfl⟩
  · exact ⟨2 * k + 1, by omega, rfl⟩
  · exact ⟨2 * k, by omega, rfl⟩

/-- After the forward chain, a vector with `|0⟩` at the sites `a + j`, `1 ≤ j ≤ 2L`, has `|0⟩` at
the sites `a + j`, `j < 2L`. -/
theorem isZeroOn_sitePermOp_forwardChain {d : ℕ} [NeZero d] (a : Fin N) (L : ℕ)
    (hL : 2 * L < N) {v : Config (Qudits (Fin N) d) → ℂ}
    (hv : IsZeroOn ((Finset.Icc 1 (2 * L)).image fun j : ℕ ↦ a + (j : Fin N)) v) :
    IsZeroOn ((Finset.range (2 * L)).image fun j : ℕ ↦ a + (j : Fin N))
      (sitePermOp (sitePerm (forwardChain a L hL)) *ᵥ v) := by
  induction L generalizing v with
  | zero => intro y _ i hi; simp at hi
  | succ L ih =>
    have hv' : IsZeroOn ((Finset.Icc 1 (2 * L)).image fun j : ℕ ↦ a + (j : Fin N)) v :=
      hv.mono (Finset.image_subset_image (Finset.Icc_subset_Icc_right (by omega)))
    have hrest : IsZeroOn {a + ((2 * L + 1 : ℕ) : Fin N), a + ((2 * L + 2 : ℕ) : Fin N)} v := by
      refine hv.mono ?_
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Finset.mem_image, Finset.mem_Icc]
      rcases hi with rfl | rfl <;> exact ⟨_, ⟨by omega, by omega⟩, rfl⟩
    have hrest' := hrest.sitePermOp_sitePerm_mulVec (hs := forwardChain a L (by omega)) (by
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (allSites_forwardChain_subset a L (by omega) hi')
      rw [Finset.mem_range] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi <;> exact add_natCast_ne a (by omega) (by omega) (by omega) hi)
    have hall : IsZeroOn (((Finset.range (2 * L)).image fun j : ℕ ↦ a + (j : Fin N)) ∪
        {a + ((2 * L + 1 : ℕ) : Fin N), a + ((2 * L + 2 : ℕ) : Fin N)})
        (sitePermOp (sitePerm (forwardChain a L (by omega))) *ᵥ v) :=
      fun y hy i hi ↦ (Finset.mem_union.mp hi).elim (ih (by omega) hv' y hy i) (hrest' y hy i)
    rw [forwardChain, sitePerm, ← sitePermOp_mul, ← mulVec_mulVec]
    refine (hall.sitePermOp_mulVec_image _).mono ?_
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [Finset.mem_range] at hj
    simp only [chainHop, Finset.mem_image, Finset.mem_union, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    rcases Nat.lt_or_ge j (2 * L) with hj' | hj'
    · refine ⟨a + (j : Fin N), Or.inl ⟨j, hj', rfl⟩, ?_⟩
      exact Equiv.swap_apply_of_ne_of_ne (add_natCast_ne a (by omega) (by omega) (by omega))
        (add_natCast_ne a (by omega) (by omega) (by omega))
    · rcases (show j = 2 * L ∨ j = 2 * L + 1 by omega) with rfl | rfl
      · exact ⟨_, Or.inr (Or.inr rfl), Equiv.swap_apply_right _ _⟩
      · refine ⟨a + ((2 * L + 1 : ℕ) : Fin N), Or.inr (Or.inl rfl), ?_⟩
        exact Equiv.swap_apply_of_ne_of_ne (add_natCast_ne a (by omega) (by omega) (by omega))
          (add_natCast_ne a (by omega) (by omega) (by omega))

end Chains

end TeleportHop

end QuantumCircuit
