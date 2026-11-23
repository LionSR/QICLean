/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Coarsen

/-!
# Words acting inside a set of parties

A word all of whose steps lie in a set `S` of parties (`Word.UsesOnly S`: its pair sources join
parties of `S`, its local operations act at parties of `S`, and its local operations at every
party are the identity outside `S`) restricts to a word on the parties of `S`, the system read on
the sites `↥S` (`Word.restrict`, by recursion on the syntax). Such a word changes no basis outside
`S` (`Word.UsesOnly.eq_of_notMem`), and its operator is the operator of the restricted word placed
on `S` (`Word.op_eq_placeBetween_restrict`): the registers outside `S` are untouched. The
restriction keeps allowedness and the sources.

## Main definitions

* `QuantumCircuit.Party.SourceGate.restrict`, `QuantumCircuit.Party.Word.restrict`.

## Main results

* `QuantumCircuit.Party.Word.UsesOnly.eq_of_notMem`.
* `QuantumCircuit.Party.Word.op_eq_placeBetween_restrict` — the factorization.
* `QuantumCircuit.Party.Word.isAllowed_restrict`, `QuantumCircuit.Party.Word.sources_restrict`,
  `QuantumCircuit.Party.Word.numGates_restrict`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35 (words
  using a set of parties).
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P] (S : Finset P)

namespace SourceGate

variable {D : Finset P} {X Y : P → Type}

/-- A pair source on a cell inside `S`, read on the parties of `S`. -/
def restrict (g : SourceGate D X Y) (hD : D ⊆ S) :
    SourceGate (D.subtype (· ∈ S)) (fun s : ↥S ↦ X s) (fun s : ↥S ↦ Y s) where
  left := ⟨g.left, hD g.left_mem⟩
  right := ⟨g.right, hD g.right_mem⟩
  distinct h := g.distinct (congrArg Subtype.val h)
  leftBasis := g.leftBasis
  rightBasis := g.rightBasis
  vector := g.vector
  cell_eq := by
    ext v
    rw [Finset.mem_subtype, Finset.ext_iff.mp g.cell_eq v.1]
    simp [Subtype.ext_iff]
  leftEquiv := g.leftEquiv
  rightEquiv := g.rightEquiv
  outside s hs := g.outside s.1 fun h ↦ hs (Finset.mem_subtype.mpr h)

/-- The matrix of the restricted source is the matrix of the source, read on the cell inside
`S`. -/
theorem regionMatrix_restrict [∀ s, DecidableEq (X s)] (g : SourceGate D X Y) (hD : D ⊆ S) :
    (g.restrict S hD).regionMatrix =
      reindex (subregionConfigEquiv hD) (subregionConfigEquiv hD) g.regionMatrix :=
  rfl

end SourceGate

namespace Word

variable {X Y : P → Type}

/-- A word using only the parties of `R` changes no basis outside `R`. -/
theorem UsesOnly.eq_of_notMem {R : Set P} : {X Y : P → Type} → {w : Word X Y} →
    w.UsesOnly R → ∀ s ∉ R, Y s = X s
  | _, _, .done _, _ => fun _ _ ↦ rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ hY _, h => fun s hs ↦ hY s fun hD ↦ hs (h hD)
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ hY _, h => fun s hs ↦ hY s fun e ↦ hs (e ▸ h)
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, h => fun s hs ↦ (h s hs).1
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ _ _, h => fun s hs ↦
    (h.2.eq_of_notMem s hs).trans (h.1.eq_of_notMem s hs)

/-- The word, all of whose steps lie in `S`, read on the parties of `S`. -/
def restrict : {X Y : P → Type} → (w : Word X Y) → w.UsesOnly ↑S →
    Word (fun s : ↥S ↦ X s) (fun s : ↥S ↦ Y s)
  | _, _, .done _, _ => .done _
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g, h =>
    .gate _ (g.restrict S (Finset.coe_subset.mp h)).outside (g.restrict S (Finset.coe_subset.mp h))
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A, h =>
    .localOp ⟨p, h⟩ (fun s hs ↦ hY s.1 fun e ↦ hs (Subtype.ext e)) A
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ A, _ => .localOps fun s ↦ A s.1
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w', h => .comp (restrict w h.1) (restrict w' h.2)

/-- The restriction keeps the number of gates. -/
@[simp] theorem numGates_restrict : {X Y : P → Type} → (w : Word X Y) → (h : w.UsesOnly ↑S) →
    (restrict S w h).numGates = w.numGates
  | _, _, .done _, _ => rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w', h =>
    congrArg₂ (· + ·) (numGates_restrict w h.1) (numGates_restrict w' h.2)

/-- **The sources of the restriction** are those of the word, read on the parties of `S`. -/
theorem sources_restrict : {X Y : P → Type} → (w : Word X Y) → (h : w.UsesOnly ↑S) →
    (restrict S w h).sources.mapOwner Subtype.val = w.sources
  | _, _, .done _, _ => rfl
  | _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g, _ => by
    simp [restrict, sources, SourceInventory.mapOwner, PairSource.mapOwner, SourceGate.restrict,
      g.distinct]
  | _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _ => rfl
  | _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w', h => by
    rw [restrict, sources_comp, sources_comp, SourceInventory.mapOwner_append,
      sources_restrict w h.1, sources_restrict w' h.2]

/-- The restriction of an allowed word is allowed. -/
theorem isAllowed_restrict : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → {w : Word X Y} → (h : w.UsesOnly ↑S) → w.IsAllowed →
      (restrict S w h).IsAllowed
  | _, _, _, _, .done _, _, _ => trivial
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g, h, hw =>
    ⟨(congrArg norm (g.regionMatrix_restrict S (Finset.coe_subset.mp h))).trans_le
      ((l2_opNorm_reindex_le _ _ _).trans hw.1), hw.2⟩
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, hw => hw
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, hw => fun s ↦ hw s.1
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ _ _, h, hw =>
    ⟨isAllowed_restrict h.1 hw.1, isAllowed_restrict h.2 hw.2⟩

/-- **A word acting inside `S` is its restriction placed on `S`**: the registers outside `S` are
untouched. -/
theorem op_eq_placeBetween_restrict [Fintype P] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → (h : w.UsesOnly ↑S) →
      w.op = placeBetween S h.eq_of_notMem (restrict S w h).op
  | _, _, _, _, .done _, _ => by
    unfold Word.op
    rw [restrict, PartyCircuit.op_done, PartyCircuit.op_done, ← piKronecker_one,
      ← piKronecker_one, placeBetween_piKronecker]
    congr 1
    funext v
    split_ifs <;> simp
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, h => by
    unfold Word.op
    rw [PartyCircuit.op_gate, restrict, PartyCircuit.op_gate]
    exact (placeBetween_subregionPlaceBetween (Finset.coe_subset.mp h) hY _ _).symm
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A, h => by
    unfold Word.op
    rw [PartyCircuit.op_localOp_eq_piKronecker, restrict, PartyCircuit.op_localOp_eq_piKronecker,
      placeBetween_piKronecker]
    congr 1
    funext v
    by_cases hv : v ∈ S
    · rw [dite_eq_left hv]
      by_cases hvp : v = p
      · subst hvp
        simp [PartyCircuit.localOpFamily]
      · rw [PartyCircuit.localOpFamily_of_ne _ _ _ hvp,
          PartyCircuit.localOpFamily_of_ne _ _ _ fun e ↦ hvp (congrArg Subtype.val e)]
    · rw [dite_eq_right hv,
        PartyCircuit.localOpFamily_of_ne _ _ _ fun (e : v = p) ↦ hv (e ▸ h)]
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A, h => by
    unfold Word.op
    rw [PartyCircuit.op_localOps, restrict, PartyCircuit.op_localOps, placeBetween_piKronecker]
    congr 1
    funext v
    by_cases hv : v ∈ S
    · rw [dite_eq_left hv]
    · rw [dite_eq_right hv]
      obtain ⟨e, he⟩ := h v hv
      ext y x
      simp [he, PEquiv.toMatrix_apply, eq_comm]
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ w w', h => by
    rw [op_comp, op_eq_placeBetween_restrict w h.1, op_eq_placeBetween_restrict w' h.2,
      placeBetween_mul, restrict, op_comp]

end Word

end QuantumCircuit.Party
