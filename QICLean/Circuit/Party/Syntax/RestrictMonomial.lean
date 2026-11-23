/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.EffectCircuit
import QICLean.Circuit.Party.Syntax.Word
import QICLean.Circuit.Party.Syntax.OwnerMap

/-!
# Monomials and weighted gates acting inside a subset of their cell

A monomial of a gate on the cell `D` lives on the parties of `D`. When all its steps lie in a
subset `S ⊆ D` (`Monomial.UsesOnly`: its pair sources and effects join parties of `S`, its local
operations act at parties of `S`, its local operations at every party are the identity outside
`S`), it is read as a monomial on the parties of `S` (`Monomial.restrict`, by recursion on the
syntax): it changes no basis outside `S`, and its operator is the operator of the restricted
monomial placed on `S` (`Monomial.op_eq_placeBetween_restrict`). The restriction keeps
allowedness, the number of gates and of pair effects, and the pair sources.

A weighted gate on `D` all of whose monomials act inside `S` is read as a weighted gate on the
cell `S` (`WeightedGate.restrict`), with the same coefficients; its matrix is the matrix of the
restricted gate extended by the identity to the parties of `D` outside `S`
(`WeightedGate.ev_eq_subregionPlaceBetween_restrict`), so the gate on `D` and the restricted gate
on `S` have the same operator (`WeightedGate.op_gate_restrict`).

The predicate "uses only the parties of `R`" is the one of every gate family
(`PartyCircuit.UsesOnly`, `Syntax/UsesOnly`).

## Main definitions

* `QuantumCircuit.Party.subsetCell`, `subsetConfigEquiv` — cells and configurations of the
  parties of `D` read on the parties of `S ⊆ D`.
* `QuantumCircuit.Party.SourceGate.restrictSubset`, `PairEffectGate.restrictSubset`,
  `ChainGate.restrictSubset` — a pair source or effect of a monomial on `D`, read on `S ⊆ D`.
* `QuantumCircuit.Party.Monomial.UsesOnly`, `QuantumCircuit.Party.Monomial.restrict`.
* `QuantumCircuit.Party.WeightedGate.restrict`.

## Main results

* `QuantumCircuit.Party.Monomial.op_eq_placeBetween_restrict` — the factorization.
* `QuantumCircuit.Party.Monomial.isAllowed_restrict`, `numGates_restrict`,
  `effectCount_restrict`, `sourceCount_restrict`, `sources_restrict`.
* `QuantumCircuit.Party.WeightedGate.length_terms_restrict`, `map_fst_terms_restrict`,
  `exists_mem_terms_of_mem_restrict`, `isAllowed_restrict`, `ev_eq_subregionPlaceBetween_restrict`,
  `op_gate_restrict`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 23–27
  (spectators) and 32–35 (allowed monomials).
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Cells and configurations inside a subset of a cell -/

section Subset

variable {D S : Finset P} (hSD : S ⊆ D)

/-- The cell, among the parties of `S ⊆ D`, of a cell `E` of the parties of `D`. -/
def subsetCell (E : Finset ↥D) : Finset ↥S :=
  Finset.univ.filter fun s ↦ (⟨s.1, hSD s.2⟩ : ↥D) ∈ E

/-- A party of `S` lies in the cell read on `S` exactly when it lies in the cell. -/
@[simp] theorem mem_subsetCell {E : Finset ↥D} {s : ↥S} :
    s ∈ subsetCell hSD E ↔ (⟨s.1, hSD s.2⟩ : ↥D) ∈ E := by
  simp [subsetCell]

/-- The configurations of a cell `E'` of the parties of `S`, in the system read on `S`, are those of
the corresponding cell `E` of the parties of `D`. -/
def subsetCellConfigEquiv (A : ↥D → Type) {E : Finset ↥D} {E' : Finset ↥S}
    (hE : ∀ v ∈ E, v.1 ∈ S) (hE' : ∀ s, s ∈ E' ↔ (⟨s.1, hSD s.2⟩ : ↥D) ∈ E) :
    RegionConfig (fun s : ↥S ↦ A ⟨s.1, hSD s.2⟩) E' ≃ RegionConfig A E where
  toFun a v := a ⟨⟨v.1.1, hE _ v.2⟩, (hE' _).mpr v.2⟩
  invFun b w := b ⟨⟨w.1.1, hSD w.1.2⟩, (hE' _).mp w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The configurations of the system read on `S` are the configurations of the region `S.subtype (·
∈ D)` of the parties of `D` (for a system read off parties of `P`, this is
`ManyBody.subregionConfigEquiv`). -/
def subsetConfigEquiv (A : ↥D → Type) :
    Config (fun s : ↥S ↦ A ⟨s.1, hSD s.2⟩) ≃ RegionConfig A (S.subtype (· ∈ D)) where
  toFun a w := a ⟨w.1.1, Finset.mem_subtype.mp w.2⟩
  invFun b v := b ⟨⟨v.1, hSD v.2⟩, Finset.mem_subtype.mpr v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {A B : ↥D → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Fintype (B s)]
  [∀ s, DecidableEq (B s)]

omit [∀ s, Fintype (A s)] [∀ s, Fintype (B s)] [∀ s, DecidableEq (B s)] in
/-- **A placement on a cell inside `S`, read on the parties of `S`.** A matrix placed on a cell `E`
of the parties of `D` lying inside `S` is the same matrix placed on the corresponding cell `E'` of
the parties of `S`, that placement then placed on the region of `S`. -/
theorem placeBetween_eq_placeBetween_subsetCell {E : Finset ↥D} {E' : Finset ↥S}
    (hE : ∀ v ∈ E, v.1 ∈ S) (hE' : ∀ s, s ∈ E' ↔ (⟨s.1, hSD s.2⟩ : ↥D) ∈ E)
    (hY : ∀ v ∉ E, B v = A v) (K : Matrix (RegionConfig B E) (RegionConfig A E) ℂ) :
    placeBetween E hY K =
      placeBetween (S.subtype (· ∈ D))
        (fun v hv ↦ hY v fun hvE ↦ hv (Finset.mem_subtype.mpr (hE v hvE)))
        (reindex (subsetConfigEquiv hSD B) (subsetConfigEquiv hSD A)
          (placeBetween E' (fun s hs ↦ hY _ fun h ↦ hs ((hE' s).mpr h))
            (reindex (subsetCellConfigEquiv hSD B hE hE').symm
              (subsetCellConfigEquiv hSD A hE hE').symm K))) := by
  ext y x
  rw [placeBetween_apply, placeBetween_apply]
  simp only [reindex_apply, submatrix_apply]
  rw [placeBetween_apply]
  have key : (∀ v (hv : v ∉ E), cast (hY v hv) (y v) = x v) ↔
      (∀ v (hv : v ∉ S.subtype (· ∈ D)), cast (hY v fun hvE ↦
        hv (Finset.mem_subtype.mpr (hE v hvE))) (y v) = x v) ∧
      (∀ s (hs : s ∉ E'), cast (hY _ fun h ↦ hs ((hE' s).mpr h)) (y ⟨s.1, hSD s.2⟩) =
        x ⟨s.1, hSD s.2⟩) := by
    refine ⟨fun h ↦ ⟨fun v hv ↦ h v fun hvE ↦ hv (Finset.mem_subtype.mpr (hE v hvE)),
      fun s hs ↦ h _ fun h' ↦ hs ((hE' s).mpr h')⟩, fun h v hv ↦ ?_⟩
    by_cases hvS : v ∈ S.subtype (· ∈ D)
    · exact h.2 ⟨v.1, Finset.mem_subtype.mp hvS⟩ fun hs ↦ hv ((hE' _).mp hs)
    · exact h.1 v hvS
  by_cases hc : ∀ v (hv : v ∉ E), cast (hY v hv) (y v) = x v
  · rw [ite_eq_left hc, ite_eq_left (key.mp hc).1]
    exact (ite_eq_left (key.mp hc).2).symm
  · rw [ite_eq_right hc]
    refine (ite_eq_right_iff.mpr fun h1 ↦ ite_eq_right_iff.mpr fun h2 ↦ ?_).symm
    exact absurd (key.mpr ⟨h1, h2⟩) hc

end Subset

/-! ### Pair sources and pair effects of a monomial, read on a subset of its cell -/

namespace SourceGate

variable {D S : Finset P} (hSD : S ⊆ D) {E : Finset ↥D} {A B : ↥D → Type}

/-- A pair source of a monomial on `D`, on a cell inside `S ⊆ D`, read on the parties of `S`: the
same pair data, the cell read on `S`. -/
def restrictSubset (g : SourceGate E A B) (hE : ∀ v ∈ E, v.1 ∈ S) :
    SourceGate (subsetCell hSD E) (fun s ↦ A ⟨s.1, hSD s.2⟩) (fun s ↦ B ⟨s.1, hSD s.2⟩) where
  left := ⟨g.left.1, hE _ g.left_mem⟩
  right := ⟨g.right.1, hE _ g.right_mem⟩
  distinct h := g.distinct (Subtype.ext (congrArg (fun s : ↥S ↦ s.1) h))
  leftBasis := g.leftBasis
  rightBasis := g.rightBasis
  vector := g.vector
  cell_eq := by
    ext s
    rw [mem_subsetCell, Finset.ext_iff.mp g.cell_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
  leftEquiv := g.leftEquiv
  rightEquiv := g.rightEquiv
  outside s hs := g.outside _ fun h ↦ hs ((mem_subsetCell hSD).mpr h)

end SourceGate

namespace PairEffectGate

variable {D S : Finset P} (hSD : S ⊆ D) {E : Finset ↥D} {A B : ↥D → Type}

/-- A pair effect of a monomial on `D`, on a cell inside `S ⊆ D`, read on the parties of `S`: the
same pair data, the cell read on `S`. -/
def restrictSubset (g : PairEffectGate E A B) (hE : ∀ v ∈ E, v.1 ∈ S) :
    PairEffectGate (subsetCell hSD E) (fun s ↦ A ⟨s.1, hSD s.2⟩) (fun s ↦ B ⟨s.1, hSD s.2⟩) where
  left := ⟨g.left.1, hE _ g.left_mem⟩
  right := ⟨g.right.1, hE _ g.right_mem⟩
  distinct h := g.distinct (Subtype.ext (congrArg (fun s : ↥S ↦ s.1) h))
  leftBasis := g.leftBasis
  rightBasis := g.rightBasis
  vector := g.vector
  cell_eq := by
    ext s
    rw [mem_subsetCell, Finset.ext_iff.mp g.cell_eq]
    simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff]
  leftEquiv := g.leftEquiv
  rightEquiv := g.rightEquiv
  outside s hs := g.outside _ fun h ↦ hs ((mem_subsetCell hSD).mpr h)

end PairEffectGate

namespace ChainGate

variable {D S : Finset P} (hSD : S ⊆ D) {E : Finset ↥D} {A B : ↥D → Type}

/-- A pair source or effect of a monomial on `D`, on a cell inside `S ⊆ D`, read on the parties of
`S`. -/
def restrictSubset : ChainGate E A B → (∀ v ∈ E, v.1 ∈ S) →
    ChainGate (subsetCell hSD E) (fun s ↦ A ⟨s.1, hSD s.2⟩) (fun s ↦ B ⟨s.1, hSD s.2⟩)
  | .inl g, hE => .inl (g.restrictSubset hSD hE)
  | .inr g, hE => .inr (g.restrictSubset hSD hE)

/-- The matrix of a restricted pair source or effect is its matrix, read on the cell inside `S`. -/
theorem chainEv_restrictSubset [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
    [∀ s, Fintype (B s)] [∀ s, DecidableEq (B s)] (g : ChainGate E A B)
    (hE : ∀ v ∈ E, v.1 ∈ S) :
    chainEv (g.restrictSubset hSD hE) (GateFamily.UniqueOutcome.outcome _) =
      reindex (subsetCellConfigEquiv hSD B hE fun _ ↦ mem_subsetCell hSD).symm
        (subsetCellConfigEquiv hSD A hE fun _ ↦ mem_subsetCell hSD).symm
          (chainEv g (GateFamily.UniqueOutcome.outcome _)) := by
  rcases g with g | g <;> rfl

/-- Restriction keeps the normalization of the vector. -/
theorem isAllowed_restrictSubset [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
    [∀ s, Fintype (B s)] [∀ s, DecidableEq (B s)] {g : ChainGate E A B}
    (hE : ∀ v ∈ E, v.1 ∈ S) (hg : ChainGate.IsAllowed g) :
    ChainGate.IsAllowed (g.restrictSubset hSD hE) := by
  rcases g with g | g <;> exact hg

end ChainGate

/-! ### Monomials acting inside a subset of their cell -/

namespace Monomial

variable {D : Finset P} (S : Finset P) (hSD : S ⊆ D)

/-- A monomial on the parties of `D` uses only the parties of `S`. -/
abbrev UsesOnly {A B : ↥D → Type} (M : Monomial D A B) : Prop :=
  PartyCircuit.UsesOnly {v : ↥D | v.1 ∈ S} M

/-- The monomial on the parties of `D`, all of whose steps lie in `S ⊆ D`, read on the parties of
`S`. Source: `04-compression.tex`, lines 32–35. -/
def restrict : {A B : ↥D → Type} → (M : Monomial D A B) → M.UsesOnly S →
    Monomial S (fun s ↦ A ⟨s.1, hSD s.2⟩) (fun s ↦ B ⟨s.1, hSD s.2⟩)
  | _, _, .done _, _ => .done _
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ E hY g, h =>
    .gate (subsetCell hSD E) (fun _ hs ↦ hY _ fun h' ↦ hs ((mem_subsetCell hSD).mpr h'))
      (g.restrictSubset hSD fun _ hv ↦ h hv)
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY a, h =>
    .localOp ⟨p.1, h⟩
      (fun _ hs ↦ hY _ fun e ↦ hs (Subtype.ext (congrArg (fun v : ↥D ↦ v.1) e))) a
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ a, _ => .localOps fun s ↦ a ⟨s.1, hSD s.2⟩
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ M M', h =>
    .comp (restrict M h.1) (restrict M' h.2)

/-- The restriction keeps the number of gates. -/
@[simp] theorem numGates_restrict : {A B : ↥D → Type} → (M : Monomial D A B) →
    (h : M.UsesOnly S) → (M.restrict S hSD h).numGates = M.numGates
  | _, _, .done _, _ => rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ M M', h =>
    congrArg₂ (· + ·) (numGates_restrict M h.1) (numGates_restrict M' h.2)

/-- The restriction keeps the number of pair effects along the gates. -/
private theorem length_filterMap_chainEffect?_restrict : {A B : ↥D → Type} →
    (M : Monomial D A B) → (h : M.UsesOnly S) →
      ((restrict S hSD M h).gates.filterMap chainEffect?).length =
        (M.gates.filterMap chainEffect?).length
  | _, _, .done _, _ => rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inl _), _ => rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr _), _ => rfl
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ M M', h => by
    change (((restrict S hSD M h.1).gates ++ (restrict S hSD M' h.2).gates).filterMap
        chainEffect?).length = ((M.gates ++ M'.gates).filterMap chainEffect?).length
    rw [List.filterMap_append, List.filterMap_append, List.length_append, List.length_append,
      length_filterMap_chainEffect?_restrict M h.1, length_filterMap_chainEffect?_restrict M' h.2]

/-- The restriction keeps the number of pair sources along the gates. -/
private theorem length_filterMap_chainSource?_restrict : {A B : ↥D → Type} →
    (M : Monomial D A B) → (h : M.UsesOnly S) →
      ((restrict S hSD M h).gates.filterMap chainSource?).length =
        (M.gates.filterMap chainSource?).length
  | _, _, .done _, _ => rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inl _), _ => rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr _), _ => rfl
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ M M', h => by
    change (((restrict S hSD M h.1).gates ++ (restrict S hSD M' h.2).gates).filterMap
        chainSource?).length = ((M.gates ++ M'.gates).filterMap chainSource?).length
    rw [List.filterMap_append, List.filterMap_append, List.length_append, List.length_append,
      length_filterMap_chainSource?_restrict M h.1, length_filterMap_chainSource?_restrict M' h.2]

/-- The pair sources of the restriction, their endpoints read in `D`, are those of the monomial,
along the gates. -/
private theorem mapOwner_filterMap_chainSource?_restrict : {A B : ↥D → Type} →
    (M : Monomial D A B) → (h : M.UsesOnly S) →
      SourceInventory.mapOwner (fun s ↦ (⟨s.1, hSD s.2⟩ : ↥D))
          ((restrict S hSD M h).gates.filterMap chainSource?) = M.gates.filterMap chainSource?
  | _, _, .done _, _ => rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inl g), _ => by
    change SourceInventory.mapOwner _ [(g.restrictSubset hSD _).toPairSource] = [g.toPairSource]
    rw [SourceInventory.mapOwner_cons, SourceInventory.mapOwner_nil, PairSource.mapOwner]
    split_ifs with hd
    · exact absurd hd g.distinct
    · rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr _), _ => rfl
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ M M', h => by
    change SourceInventory.mapOwner _ (((restrict S hSD M h.1).gates ++
        (restrict S hSD M' h.2).gates).filterMap chainSource?) =
          (M.gates ++ M'.gates).filterMap chainSource?
    rw [List.filterMap_append, List.filterMap_append, SourceInventory.mapOwner_append,
      mapOwner_filterMap_chainSource?_restrict M h.1,
      mapOwner_filterMap_chainSource?_restrict M' h.2]

variable {A B : ↥D → Type}

/-- The restriction keeps the number of pair effects. -/
@[simp] theorem effectCount_restrict (M : Monomial D A B) (h : M.UsesOnly S) :
    (restrict S hSD M h).effectCount = M.effectCount :=
  length_filterMap_chainEffect?_restrict S hSD M h

/-- **The pair sources of the restriction** are those of the monomial, their endpoints read on the
parties of `S`. -/
theorem sources_restrict (M : Monomial D A B) (h : M.UsesOnly S) :
    SourceInventory.mapOwner (fun s ↦ (⟨s.1, hSD s.2⟩ : ↥D)) (restrict S hSD M h).sources =
      M.sources := by
  change SourceInventory.mapOwner _ ((restrict S hSD M h).gates.filterMap chainSource?).reverse =
    (M.gates.filterMap chainSource?).reverse
  rw [SourceInventory.mapOwner, List.filterMap_reverse]
  exact congrArg List.reverse (mapOwner_filterMap_chainSource?_restrict S hSD M h)

/-- The restriction keeps the number of pair sources. -/
@[simp] theorem sourceCount_restrict (M : Monomial D A B) (h : M.UsesOnly S) :
    (restrict S hSD M h).sourceCount = M.sourceCount := by
  change ((restrict S hSD M h).gates.filterMap chainSource?).reverse.length =
    (M.gates.filterMap chainSource?).reverse.length
  rw [List.length_reverse, List.length_reverse]
  exact length_filterMap_chainSource?_restrict S hSD M h

/-- The restriction of an allowed monomial is allowed. -/
theorem isAllowed_restrict : {A B : ↥D → Type} → [∀ s, Fintype (A s)] →
    [∀ s, DecidableEq (A s)] → {M : Monomial D A B} → (h : M.UsesOnly S) →
      M.IsAllowed chainEv ChainGate.IsAllowed →
        (restrict S hSD M h).IsAllowed chainEv ChainGate.IsAllowed
  | _, _, _, _, .done _, _, _ => trivial
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g, h, hw =>
    ⟨(congrArg norm (g.chainEv_restrictSubset hSD fun _ hv ↦ h hv)).trans_le
      ((l2_opNorm_reindex_le _ _ _).trans hw.1), g.isAllowed_restrictSubset hSD _ hw.2⟩
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, hw => hw
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, hw => fun _ ↦ hw _
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ _ _, h, hw =>
    ⟨isAllowed_restrict h.1 hw.1, isAllowed_restrict h.2 hw.2⟩

/-- A product of party operations, read on the region `S.subtype (· ∈ D)`, is the product of the
operations at the parties of that region. -/
private theorem reindex_subsetConfigEquiv_piKronecker (a : ∀ s, Matrix (B s) (A s) ℂ) :
    reindex (subsetConfigEquiv hSD B) (subsetConfigEquiv hSD A)
        (piKronecker fun s : ↥S ↦ a ⟨s.1, hSD s.2⟩) =
      piKronecker fun w : {w // w ∈ S.subtype (· ∈ D)} ↦ a w := by
  ext y x
  simp only [reindex_apply, submatrix_apply, piKronecker_apply]
  exact Fintype.prod_equiv
    ⟨fun s ↦ ⟨⟨s.1, hSD s.2⟩, Finset.mem_subtype.mpr s.2⟩,
      fun w ↦ ⟨w.1.1, Finset.mem_subtype.mp w.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩ _ _ fun _ ↦ rfl

/-- **A monomial acting inside `S` is its restriction placed on `S`**: the registers of the parties
of `D` outside `S` are untouched. Source: `04-compression.tex`, lines 25–27. -/
theorem op_eq_placeBetween_restrict : {A B : ↥D → Type} → [∀ s, Fintype (A s)] →
    [∀ s, DecidableEq (A s)] → (M : Monomial D A B) → (h : M.UsesOnly S) →
      M.op chainEv = placeBetween (S.subtype (· ∈ D))
        (fun v hv ↦ h.eq_of_notMem v fun hv' ↦ hv (Finset.mem_subtype.mpr hv'))
        (reindex (subsetConfigEquiv hSD B) (subsetConfigEquiv hSD A)
          ((restrict S hSD M h).op chainEv))
  | _, _, _, _, .done _, _ => by
    rw [PartyCircuit.op_done]
    change _ = placeBetween _ _ (reindex _ _ (1 : Matrix _ _ ℂ))
    rw [reindex_apply, submatrix_one_equiv, placeBetween_eq_place, place_one]
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ E hY g, h => by
    rw [restrict, PartyCircuit.op_gate, PartyCircuit.op_gate, ChainGate.chainEv_restrictSubset]
    exact placeBetween_eq_placeBetween_subsetCell hSD _ (fun _ ↦ mem_subsetCell hSD) hY _
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY a, h => by
    rw [restrict, PartyCircuit.op_localOp, PartyCircuit.op_localOp]
    refine (placeBetween_eq_placeBetween_subsetCell hSD (E' := {(⟨p.1, h⟩ : ↥S)})
      (fun v hv ↦ (Finset.mem_singleton.mp hv) ▸ h) (fun s ↦ ?_) _ _).trans rfl
    simp only [Finset.mem_singleton, Subtype.ext_iff]
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ a, h => by
    rw [restrict, PartyCircuit.op_localOps, PartyCircuit.op_localOps,
      reindex_subsetConfigEquiv_piKronecker, placeBetween_piKronecker]
    refine congrArg piKronecker (funext fun v ↦ ?_)
    by_cases hv : v ∈ S.subtype (· ∈ D)
    · simp only [hv, ↓reduceDIte]
    · simp only [hv, ↓reduceDIte]
      obtain ⟨he, ha⟩ := h v fun hv' ↦ hv (Finset.mem_subtype.mpr hv')
      ext y x
      rw [ha, PEquiv.toMatrix_apply]
      simp [Equiv.toPEquiv_apply, Equiv.cast_apply]
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ M M', h => by
    rw [PartyCircuit.op_comp, op_eq_placeBetween_restrict M h.1,
      op_eq_placeBetween_restrict M' h.2, placeBetween_mul]
    congr 1
    simp only [restrict, PartyCircuit.op_comp, reindex_apply, submatrix_mul_equiv]

end Monomial

/-! ### Weighted gates acting inside a subset of their cell -/

namespace WeightedGate

variable {D : Finset P} {X Y : P → Type} (S : Finset P) (hSD : S ⊆ D)

/-- The weighted gate on the cell `D`, all of whose monomials act inside `S ⊆ D`, read on the cell
`S`: the same coefficients, each monomial restricted to the parties of `S`. Source:
`04-compression.tex`, lines 32–35. -/
def restrict (g : WeightedGate D X Y) (h : ∀ t ∈ g.terms, t.2.UsesOnly S) : WeightedGate S X Y :=
  ⟨g.terms.attach.map fun t ↦ (t.1.1, t.1.2.restrict S hSD (h t.1 t.2))⟩

/-- The restricted gate has one monomial for each monomial of the gate. -/
@[simp] theorem length_terms_restrict (g : WeightedGate D X Y)
    (h : ∀ t ∈ g.terms, t.2.UsesOnly S) : (g.restrict S hSD h).terms.length = g.terms.length := by
  simp [restrict]

/-- The restricted gate has the coefficients of the gate. -/
@[simp] theorem map_fst_terms_restrict (g : WeightedGate D X Y)
    (h : ∀ t ∈ g.terms, t.2.UsesOnly S) :
    (g.restrict S hSD h).terms.map Prod.fst = g.terms.map Prod.fst := by
  simp only [restrict, List.map_map]
  conv_rhs => rw [← List.attach_map_subtype_val g.terms, List.map_map]
  rfl

/-- A term of the restricted gate is the restriction of a term of the gate. -/
theorem exists_mem_terms_of_mem_restrict {g : WeightedGate D X Y}
    {h : ∀ t ∈ g.terms, t.2.UsesOnly S} {t} (ht : t ∈ (g.restrict S hSD h).terms) :
    ∃ t' : ℂ × Monomial D (fun s ↦ X s) (fun s ↦ Y s), ∃ ht' : t' ∈ g.terms,
      t = (t'.1, t'.2.restrict S hSD (h t' ht')) := by
  obtain ⟨⟨t', ht'⟩, -, rfl⟩ := List.mem_map.mp ht
  exact ⟨t', ht', rfl⟩

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

/-- The restriction of an allowed weighted gate is allowed. -/
theorem isAllowed_restrict {g : WeightedGate D X Y} (h : ∀ t ∈ g.terms, t.2.UsesOnly S)
    (hg : WeightedGate.IsAllowed g) : WeightedGate.IsAllowed (g.restrict S hSD h) := by
  intro t ht
  obtain ⟨t', ht', rfl⟩ := exists_mem_terms_of_mem_restrict S hSD ht
  exact Monomial.isAllowed_restrict S hSD (h t' ht') (hg t' ht')

/-- The extension from the cell `S` to the cell `D ⊇ S`, as a linear map. -/
private noncomputable def subregionPlaceBetweenₗ (hY : ∀ v ∉ S, Y v = X v) :
    Matrix (RegionConfig Y S) (RegionConfig X S) ℂ →ₗ[ℂ]
      Matrix (RegionConfig Y D) (RegionConfig X D) ℂ where
  toFun := subregionPlaceBetween hSD hY
  map_add' := subregionPlaceBetween_add hSD hY
  map_smul' := subregionPlaceBetween_smul hSD hY

/-- **The matrix of a weighted gate acting inside `S`** is the matrix of the restricted gate,
extended by the identity to the parties of `D` outside `S`. Source: `04-compression.tex`, lines
25–27. -/
theorem ev_eq_subregionPlaceBetween_restrict (g : WeightedGate D X Y)
    (h : ∀ t ∈ g.terms, t.2.UsesOnly S) (hY : ∀ v ∉ S, Y v = X v) :
    WeightedGate.ev g () =
      subregionPlaceBetween hSD hY (WeightedGate.ev (g.restrict S hSD h) ()) := by
  change _ = subregionPlaceBetweenₗ S hSD hY _
  simp only [WeightedGate.ev, restrict, List.map_map, map_list_sum]
  conv_lhs => rw [← List.attach_map_subtype_val g.terms, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t _ ↦ ?_)
  simp only [Function.comp_apply, map_smul]
  exact congrArg (t.1.1 • ·) (Monomial.op_eq_placeBetween_restrict S hSD t.1.2 (h t.1 t.2))

/-- **A weighted gate acting inside `S` is the restricted gate on the cell `S`**: the two gates have
the same operator. -/
theorem op_gate_restrict [Fintype P] (g : WeightedGate D X Y) (h : ∀ t ∈ g.terms, t.2.UsesOnly S)
    (hYD : ∀ v ∉ D, Y v = X v) (hY : ∀ v ∉ S, Y v = X v) :
    (PartyCircuit.gate D hYD g).op WeightedGate.ev =
      (PartyCircuit.gate S hY (g.restrict S hSD h)).op WeightedGate.ev := by
  rw [PartyCircuit.op_gate, PartyCircuit.op_gate]
  exact (congrArg (placeBetween D hYD) (ev_eq_subregionPlaceBetween_restrict S hSD g h hY)).trans
    (placeBetween_subregionPlaceBetween hSD hY hYD _)

end WeightedGate

end QuantumCircuit.Party
