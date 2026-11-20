/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.LocalGate
import QICLean.Circuit.Model.Unitary

/-!
# Substituting products of gates for gates

The Kraus operator of a layer at an index is the product, over the cells in any order, of the
placements of the matrices of the gates at that index, times the product `⊗ₛ uₛ` of the
operators of the onsite families at the remaining sites (the identity at the sites of the
cells). For a unitary layer every factor is unitary.

This gives **gate substitution**: let `Γ` and `Γ'` be two geometries on the same sites. If every
unitary placed on a cell `b` of `Γ` is a product of gates on `Γ'` of cost at most `f b`, then
the operator of a unitary circuit on `Γ` is a product of gates on `Γ'` of cost at most the sum
of `f b` over the cells used. In particular, if `f b ≤ C · cost b`, a product of gates of cost
`K` on `Γ` is a product of gates of cost `C K` on `Γ'`. This is the statement behind placing a
circuit at arbitrary sites and replacing windows by neighbouring pairs, in the circuits of
arXiv:2307.01696, paragraph "The sequential-RG circuit" (gates "with constant support"
expressed through local gates, and inputs separated by `O(q)` sites, "which requires one to
implement SWAP gates"), and of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

A unitary on one site is a product operator `⊗ₛ uₛ`, hence an onsite family, and costs nothing
on every geometry.

There is no depth version: the circuits substituted for gates on disjoint cells of `Γ` may use
overlapping cells of `Γ'` (routing by swaps does), so they need not run in parallel.

The declarations restate the counting arguments of `IsPairProduct.embedOp_injective` of
`TNLean/Circuit/ArbitrarySiteGateEmbedding.lean`, `IsWindowProduct.isPairProduct_two` of
`TNLean/Circuit/WindowProduct.lean` and `IsPairProduct.list_prod` of
`TNLean/Circuit/PairProduct.lean` at commit `414a18fb88` (Apache-2.0). The changes: one
substitution theorem for any two geometries on any finite sites and bases, with per-cell
bounds, in place of separate list manipulations for each pair of gate classes.

## Main definitions

* `QuantumCircuit.Layer.onsiteOp` — the onsite operators of a layer at an index.

## Main results

* `QuantumCircuit.Layer.kraus_eq_prod_place_mul_prodOp` — the Kraus operator of a layer as a
  product of placed gates times a product operator.
* `QuantumCircuit.Layer.isGateProduct_kraus` — a unitary layer, gate by gate.
* `QuantumCircuit.UnitaryCircuit.isGateProduct_op` — a unitary circuit, gate by gate.
* `QuantumCircuit.IsGateProduct.substitute` — gate substitution with a uniform factor.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-! ### The Kraus operator of a layer -/

namespace Layer

variable {Γ : Geometry S} {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

omit [Fintype S] [∀ s, Fintype (X s)] in
/-- The onsite operators of a layer at the Kraus index `i`: the operator of the onsite family at
every site met by no cell, and the identity at the sites of the cells. -/
def onsiteOp (L : Layer Γ G X X) (i : L.Index) (s : S) : Matrix (X s) (X s) ℂ :=
  if h : s ∉ L.cells.biUnion Γ.cell then (L.onsite ⟨s, h⟩).op (i.2 ⟨s, h⟩) else 1

/-- **The Kraus operator of a layer.** At the index `i`, it is the product of the placements of
the matrices of the gates at `i`, in the order of any enumeration `l` of the cells, times the
product of the onsite operators at `i`. -/
theorem kraus_eq_prod_place_mul_prodOp (ev : Interpretation G) (L : Layer Γ G X X)
    (l : List L.cells) (hl : l.Nodup) (hall : ∀ c, c ∈ l) (i : L.Index) :
    L.kraus ev i =
      (l.map fun c : L.cells ↦ ManyBody.place (Γ.cell c) (ev (L.gate c) (i.1 c))).prod *
        prodOp (L.onsiteOp i) := by
  rw [← kraus_ofCells ev L.cells L.pairwiseDisjoint L.gate l hl hall (i.1, fun _ ↦ ())]
  set D := L.cells.biUnion Γ.cell
  ext y x
  rw [Matrix.mul_apply]
  let z : Config X := fun s ↦ if s ∈ D then x s else y s
  have hcell (b : L.cells) :
      (fun v : {v // v ∈ Γ.cell b} ↦ z v) = fun v : {v // v ∈ Γ.cell b} ↦ x v :=
    funext fun v ↦ show (if (v : S) ∈ D then x v else y v) = x v from
      ite_eq_left (show (v : S) ∈ D from Finset.mem_biUnion.mpr ⟨b, b.2, v.2⟩)
  have hfree (s : S) (hs : s ∉ D) : z s = y s := ite_eq_right hs
  have hD (s : S) (hs : ¬s ∉ D) : z s = x s := ite_eq_left (not_not.mp hs)
  have hu (s : S) (hs : ¬s ∉ D) : L.onsiteOp i s = 1 := dite_eq_right hs
  have hK (w : Config X) : (ofCells L.cells L.pairwiseDisjoint L.gate).kraus ev (i.1, fun _ ↦ ())
      y w = (∏ b : L.cells, ev (L.gate b) (i.1 b) (fun v ↦ y v) (fun v ↦ w v)) *
        ∏ s : L.Free, (1 : Matrix (X s) (X s) ℂ) (y s) (w s) :=
    rfl
  rw [Finset.sum_eq_single z]
  · rw [hK, prodOp_apply, kraus_apply, ← Fintype.prod_subtype_mul_prod_subtype (· ∉ D)]
    simp only [hcell]
    rw [Fintype.prod_eq_one (fun s : {s // ¬s ∉ D} ↦ L.onsiteOp i s (z s) (x s))
      fun s ↦ by rw [hu s s.2, hD s s.2, one_apply_eq],
      Fintype.prod_eq_one (fun s : L.Free ↦ (1 : Matrix (X s) (X s) ℂ) (y s) (z s))
        fun s ↦ by rw [hfree s s.2, one_apply_eq], mul_one, mul_one]
    refine congrArg _ (Fintype.prod_congr _ _ fun s ↦ ?_)
    rw [onsiteOp, dite_eq_left s.2, hfree s s.2]
  · intro w _ hw
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hw
    by_cases hsD : s ∉ D
    · rw [hK]
      refine mul_eq_zero_of_left (mul_eq_zero_of_right _ (Finset.prod_eq_zero
        (Finset.mem_univ (⟨s, hsD⟩ : L.Free)) ?_)) _
      exact one_apply_ne fun h : y s = w s ↦ hs (h.symm.trans (hfree s hsD).symm)
    · rw [prodOp_apply, Finset.prod_eq_zero (Finset.mem_univ s)
        (by rw [hu s hsD]; exact one_apply_ne fun h ↦ hs (h.trans (hD s hsD).symm)), mul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ z) h

omit [Fintype S] in
theorem onsiteOp_mem_unitaryGroup {L : Layer Γ KrausGate X X}
    (hL : L.Forall KrausGate.ev KrausFamily.IsUnitary) (i : L.Index) (s : S) :
    L.onsiteOp i s ∈ unitaryGroup (X s) ℂ := by
  by_cases h : s ∉ L.cells.biUnion Γ.cell
  · rw [onsiteOp, dite_eq_left h, mem_unitaryGroup_iff', star_eq_conjTranspose]
    exact ((hL.2 ⟨s, h⟩).2 _).1
  · rw [onsiteOp, dite_eq_right h]
    exact one_mem _

omit [Fintype S] in
/-- The matrix of a gate of a unitary layer at an index is unitary. -/
theorem ev_gate_mem_unitaryGroup {L : Layer Γ KrausGate X X}
    (hL : L.Forall KrausGate.ev KrausFamily.IsUnitary) (i : L.Index) (b : L.cells) :
    KrausGate.ev (L.gate b) (i.1 b) ∈ unitaryGroup _ ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
  exact ((hL.1 b).2 _).1

end Layer

/-! ### Gate substitution -/

variable {Γ Γ' : Geometry S}

/-- A unitary layer on `Γ` is a product of gates on `Γ'` of cost at most the sum of `f b` over
its cells, when every unitary placed on a cell `b` is a product of gates on `Γ'` of cost at
most `f b`. -/
theorem Layer.isGateProduct_kraus (f : Γ.Cell → ℕ)
    (h : ∀ (b : Γ.Cell) (V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ),
      V ∈ unitaryGroup _ ℂ → IsGateProduct Γ' (f b) (ManyBody.place (Γ.cell b) V))
    {L : Layer Γ KrausGate X X} (hL : L.Forall KrausGate.ev KrausFamily.IsUnitary)
    (i : L.Index) : IsGateProduct Γ' (∑ b ∈ L.cells, f b) (L.kraus KrausGate.ev i) := by
  rw [L.kraus_eq_prod_place_mul_prodOp KrausGate.ev Finset.univ.toList (Finset.nodup_toList _)
    (fun c ↦ Finset.mem_toList.mpr (Finset.mem_univ c)) i, ← Finset.sum_coe_sort L.cells f,
    ← Finset.sum_map_toList, ← Nat.add_zero (List.sum _)]
  exact (IsGateProduct.list_prod_map _
    (fun c : L.cells ↦ ManyBody.place (Γ.cell c) (KrausGate.ev (L.gate c) (i.1 c)))
    (fun c : L.cells ↦ f c) fun c _ ↦ h c _ (Layer.ev_gate_mem_unitaryGroup hL i c)).mul
    (IsGateProduct.prodOp (Layer.onsiteOp_mem_unitaryGroup hL i) 0)

/-- **Gate substitution, gate by gate.** If every unitary placed on a cell `b` of `Γ` is a
product of gates on `Γ'` of cost at most `f b`, the operator of a unitary circuit on `Γ` is a
product of gates on `Γ'` of cost at most the sum of `f b` over the cells of its layers. -/
theorem UnitaryCircuit.isGateProduct_op (f : Γ.Cell → ℕ)
    (h : ∀ (b : Γ.Cell) (V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ),
      V ∈ unitaryGroup _ ℂ → IsGateProduct Γ' (f b) (ManyBody.place (Γ.cell b) V))
    (c : UnitaryCircuit Γ X) :
    IsGateProduct Γ' (c.layers.map fun L ↦ ∑ b ∈ L.cells, f b).sum c.op := by
  obtain ⟨Ls, hLs⟩ := c
  induction Ls with
  | nil => exact IsGateProduct.one Γ' X 0
  | cons L Ls ih =>
    have hL := hLs L List.mem_cons_self
    have hLs' : ∀ L' ∈ Ls, L'.Forall KrausGate.ev KrausFamily.IsUnitary :=
      fun L' hL' ↦ hLs L' (List.mem_cons_of_mem L hL')
    obtain ⟨u⟩ := Layer.nonempty_unique_index_of_forall_isUnitary hL
    have hc : (⟨L :: Ls, hLs⟩ : UnitaryCircuit Γ X) =
        (UnitaryCircuit.ofLayer L hL).comp ⟨Ls, hLs'⟩ :=
      rfl
    simp only [List.map_cons, List.sum_cons]
    rw [hc, UnitaryCircuit.op_comp, UnitaryCircuit.op_ofLayer L hL u.default, Nat.add_comm]
    exact (ih hLs').mul (Layer.isGateProduct_kraus f h hL _)

/-- **Gate substitution.** Let `Γ` and `Γ'` be geometries on the same sites. If every unitary
placed on a cell `b` of `Γ` is a product of gates on `Γ'` of cost at most `C` times the cost of
`b`, every product of gates of cost `K` on `Γ` is a product of gates of cost `C K` on `Γ'`.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit" (gates with constant support
expressed through local gates), and Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex` (placing a circuit at arbitrary sites). -/
theorem IsGateProduct.substitute {C K : ℕ} {U : Matrix (Config X) (Config X) ℂ}
    (h : ∀ (b : Γ.Cell) (V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ),
      V ∈ unitaryGroup _ ℂ → IsGateProduct Γ' (C * Γ.cost b) (ManyBody.place (Γ.cell b) V))
    (hU : IsGateProduct Γ K U) : IsGateProduct Γ' (C * K) U := by
  obtain ⟨c, hc, rfl⟩ := hU
  refine (c.isGateProduct_op (fun b ↦ C * Γ.cost b) h).mono ?_
  have hL (L : Layer Γ KrausGate X X) : ∑ b ∈ L.cells, C * Γ.cost b = C * L.gateCount := by
    rw [Layer.gateCount_eq_sum, Finset.mul_sum]
  rw [List.map_congr_left fun L _ ↦ hL L, List.sum_map_mul_left,
    ← UnitaryCircuit.gateCount_eq_sum]
  exact Nat.mul_le_mul_left C hc

end QuantumCircuit
