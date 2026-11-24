/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.CoarsenLocal

/-!
# Words that split into two local contractions across two sides

A function `f : Q → Bool` sorts the parties into two sides. A word `W` is *tensor partitioned*
by `f` when, after grouping the parties by their side (`Word.coarsen f`), its operator is the
tensor product of the operators of two allowed source-free words, one on the side `true` and one
on the side `false`, read across the cut of the side `true` (`ManyBody.cutEquiv`). This holds
when every pair source of `W` joins two parties of the same side: the grouped word then has no
pair source, so it is the tensor product of its operations at the two sides.

## Main definitions

* `QuantumCircuit.Party.Word.IsTensorPartitioned`.

## Main results

* `QuantumCircuit.Party.Word.isTensorPartitioned_of_sources_internal`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 409–434.
-/

noncomputable section

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.Word

variable {Q : Type} [Fintype Q] [DecidableEq Q] {X Y : Q → Type} [∀ q, Fintype (X q)]
  [∀ q, DecidableEq (X q)] [∀ q, Fintype (Y q)]

/-- The operator of the word `W`, read on the two sides of `f`, is the tensor product of two
allowed source-free contractions, a word on the side `true` and a word on the side `false`, the
identity holding on all inputs. Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
def IsTensorPartitioned (f : Q → Bool) (W : Word X Y) : Prop :=
  ∃ c : Word (P := {b : Bool // b ∈ ({true} : Finset Bool)}) (fun b ↦ blockSystem f X b)
      (fun b ↦ blockSystem f Y b),
    ∃ d : Word (P := {b : Bool // b ∉ ({true} : Finset Bool)}) (fun b ↦ blockSystem f X b)
        (fun b ↦ blockSystem f Y b),
      c.IsAllowed ∧ d.IsAllowed ∧ c.sources = [] ∧ d.sources = [] ∧
      ‖c.op‖ ≤ 1 ∧ ‖d.op‖ ≤ 1 ∧
      (W.coarsen f).op = reindex (cutEquiv (blockSystem f Y) {true}).symm
        (cutEquiv (blockSystem f X) {true}).symm (c.op ⊗ₖ d.op)

/-- **Internal sources split a word across two sides.** If every pair source of an allowed word
joins two parties of the same side, the word is tensor partitioned: the two factors are the
operations of the grouped word at the two sides. Source: Theorem 5.2, `04-compression.tex`,
lines 409–427. -/
theorem isTensorPartitioned_of_sources_internal (f : Q → Bool) (w : Word X Y)
    (hw : w.IsAllowed) (hS : ∀ s ∈ w.sources, f s.left = f s.right) :
    w.IsTensorPartitioned f := by
  classical
  have hl : PartyCircuit.IsLocal (w.coarsen f) := by
    rw [isLocal_iff_sources_eq_nil, sources_coarsen, SourceInventory.mapOwner_eq_nil_iff]
    exact hS
  have ha := isAllowed_coarsen f hw
  have hn := PartyCircuit.norm_partyOp_le_one (G := SourceGate (P := Bool)) SourceGate.ev ha
  let c : Word (P := {b : Bool // b ∈ ({true} : Finset Bool)}) (fun b ↦ blockSystem f X b)
      (fun b ↦ blockSystem f Y b) :=
    PartyCircuit.localOps fun b ↦ (w.coarsen f).partyOp b
  let d : Word (P := {b : Bool // b ∉ ({true} : Finset Bool)}) (fun b ↦ blockSystem f X b)
      (fun b ↦ blockSystem f Y b) :=
    PartyCircuit.localOps fun b ↦ (w.coarsen f).partyOp b
  have hc : c.IsAllowed := isAllowed_localOps _ fun b ↦ hn b
  have hd : d.IsAllowed := isAllowed_localOps _ fun b ↦ hn b
  refine ⟨c, d, hc, hd, rfl, rfl, PartyCircuit.norm_op_le_one (G := SourceGate) _ hc,
    PartyCircuit.norm_op_le_one (G := SourceGate) _ hd, ?_⟩
  unfold Word.op
  rw [PartyCircuit.op_eq_reindex_kronecker_regionOp SourceGate.ev (w.coarsen f) hl {true},
    PartyCircuit.op_localOps, PartyCircuit.op_localOps]
  rfl

end QuantumCircuit.Party.Word
