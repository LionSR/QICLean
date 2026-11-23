/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Coarsen
import QICLean.Circuit.Party.Syntax.Frame

/-!
# Words on the parties of a cell, run inside all parties

A word on the parties of a cell `D` (on the sites `↥D`, the system read there) runs inside all
parties as the identity outside `D` (`Word.onCell`). It is the word read on the blocks of the
inclusion `↥D → P` (one site in the block of a party of `D`, none in the block of any other
party), run beside the spectator factor `p ∉ D → X p` of every party, between two relabellings of
the bases (`cellEquiv`). Its operator is the operator of the word placed on `D`
(`Word.op_onCell`); it keeps allowedness and the sources (`Word.isAllowed_onCell`,
`Word.sources_onCell`).

## Main definitions

* `QuantumCircuit.Party.cellEquiv`, `QuantumCircuit.Party.Word.onCell`.

## Main results

* `QuantumCircuit.Party.Word.op_onCell`, `QuantumCircuit.Party.Word.isAllowed_onCell`,
  `QuantumCircuit.Party.Word.sources_onCell`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 21–36 (an
  operation on the parties of a cell acts as the identity on the other parties).
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P] (D : Finset P)

omit [Fintype P] in
/-- A site of the block of `p` along the inclusion of `D` is the site `p`. -/
private theorem val_eq_of_mem_block {p : P}
    (w : {w // w ∈ blockPreimage (Subtype.val : ↥D → P) {p}}) : w.1.1 = p :=
  Finset.mem_singleton.mp (Finset.mem_filter.mp w.2).2

omit [Fintype P] in
/-- The site `p ∈ D` lies in its own block along the inclusion of `D`. -/
private theorem mem_block {p : P} (h : p ∈ D) :
    (⟨p, h⟩ : ↥D) ∈ blockPreimage (Subtype.val : ↥D → P) {p} := by
  simp

/-- The basis of a party read as a spectator factor, present only outside `D` and read in a
system `X` agreeing with `Y` there, and its block along the inclusion of `D`. -/
def cellEquiv (X Y : P → Type) (hY : ∀ s ∉ D, Y s = X s) (p : P) :
    Y p ≃ (p ∉ D → X p) × blockSystem (Subtype.val : ↥D → P) (fun s ↦ Y s) p where
  toFun y := (fun h ↦ cast (hY p h) y,
    fun w ↦ cast (congrArg Y (val_eq_of_mem_block D w).symm) y)
  invFun z := if h : p ∈ D then z.2 ⟨⟨p, h⟩, mem_block D h⟩ else cast (hY p h).symm (z.1 h)
  left_inv y := by
    by_cases h : p ∈ D <;> simp [h]
  right_inv z := by
    obtain ⟨f, g⟩ := z
    by_cases h : p ∈ D
    · refine Prod.ext (funext fun h' ↦ absurd h h') (funext fun w ↦ ?_)
      obtain ⟨⟨q, hq⟩, hw⟩ := w
      obtain rfl : q = p := val_eq_of_mem_block D ⟨⟨q, hq⟩, hw⟩
      simp [h]
    · refine Prod.ext (funext fun h' ↦ by simp [h]) (funext fun w ↦ ?_)
      exact absurd (val_eq_of_mem_block D w ▸ w.1.2) h

namespace Word

variable {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

/-- A word on the parties of the cell `D`, run inside all parties, the identity outside `D`: the
word read on the blocks of the inclusion of `D`, beside the spectator factors, between two
relabellings. -/
noncomputable def onCell (hY : ∀ s ∉ D, Y s = X s)
    (w : Word (fun s : ↥D ↦ X s) (fun s : ↥D ↦ Y s)) : Word X Y :=
  ((PartyCircuit.relabel fun p ↦ (cellEquiv D X X (fun _ _ ↦ rfl) p).symm).comp
      ((coarsen Subtype.val w).frame fun p ↦ p ∉ D → X p)).comp
    (PartyCircuit.relabel (cellEquiv D X Y hY))

omit [Fintype P] in
/-- A word run on its cell keeps its sources, their endpoints read in `P`. -/
theorem sources_onCell (hY : ∀ s ∉ D, Y s = X s)
    (w : Word (fun s : ↥D ↦ X s) (fun s : ↥D ↦ Y s)) :
    (onCell D hY w).sources = w.sources.mapOwner Subtype.val := by
  simp [onCell, sources_coarsen]

omit [Fintype P] in
/-- A word run on its cell is allowed when the word is. -/
theorem isAllowed_onCell (hY : ∀ s ∉ D, Y s = X s)
    {w : Word (fun s : ↥D ↦ X s) (fun s : ↥D ↦ Y s)} (hw : w.IsAllowed) :
    (onCell D hY w).IsAllowed :=
  ⟨⟨isAllowed_relabel _, isAllowed_frame _ (isAllowed_coarsen _ hw)⟩, isAllowed_relabel _⟩

/-- **The operator of a word run on its cell is its operator placed on the cell.** -/
theorem op_onCell (hY : ∀ s ∉ D, Y s = X s)
    (w : Word (fun s : ↥D ↦ X s) (fun s : ↥D ↦ Y s)) :
    (onCell D hY w).op = placeBetween D hY w.op := by
  rw [onCell, op_comp, op_comp, op_frame, op_coarsen]
  unfold Word.op
  rw [PartyCircuit.op_relabel_mul, PartyCircuit.op_relabel, PEquiv.mul_toMatrix_toPEquiv]
  ext y x
  simp only [submatrix_apply, reindex_apply, Equiv.symm_symm, id, kroneckerMap_apply,
    one_apply, placeBetween_apply]
  have hy : (blockConfigEquiv Subtype.val fun s : ↥D ↦ Y s)
      ((Equiv.arrowProdEquivProdArrow P (fun p ↦ p ∉ D → X p)
        (blockSystem Subtype.val fun s : ↥D ↦ Y s))
          ((Equiv.piCongrRight (cellEquiv D X Y hY)) y)).2 = fun v : ↥D ↦ y v := by
    funext v
    simp [cellEquiv]
  have hx : (blockConfigEquiv Subtype.val fun s : ↥D ↦ X s)
      ((Equiv.arrowProdEquivProdArrow P (fun p ↦ p ∉ D → X p)
        (blockSystem Subtype.val fun s : ↥D ↦ X s))
          ((Equiv.piCongrRight fun p ↦ (cellEquiv D X X (fun _ _ ↦ rfl) p).symm).symm x)).2 =
        fun v : ↥D ↦ x v := by
    funext v
    simp [cellEquiv]
  rw [hy, hx]
  by_cases hc : ∀ (v : P) (hv : v ∉ D), cast (hY v hv) (y v) = x v
  · rw [ite_eq_left hc, ite_eq_left, one_mul]
    funext p h
    simpa [cellEquiv] using hc p h
  · rw [ite_eq_right hc, ite_eq_right, zero_mul]
    intro he
    refine hc fun v hv ↦ ?_
    simpa [cellEquiv] using congrFun (congrFun he v) hv

end Word

end QuantumCircuit.Party
