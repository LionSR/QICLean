/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.PreparedSourceGate

/-!
# Chronological compositions of source-prepared gates

A *source circuit* (`SourceCircuit`) is a party circuit of prepared gates. Since every prepared
gate carries its bound, a source circuit has no side condition: its constructors, `match` and
`induction` are those of a party circuit.

A partial expansion along affected parties `A` chooses branch labels only at the gates meeting
`A` (`SourceCircuit.Choices`); its branch (`SourceCircuit.partialWord`) is a word on the
affected parties and one exterior party, in which every untouched gate is one local operation
of the exterior party, and its weight is `SourceCircuit.coefficient`. These are structural
recursions on the party circuit: a choice of a composition is a pair of choices, a choice at a
touched gate is a label of the gate, and there is one choice elsewhere. Their computation rules
on `done`, `gate`, `localOp`, `localOps` and `comp` hold by `rfl`. A framed source circuit has
the choices and coefficients of the circuit, and its branches are `1 ⊗` the branches
(`SourceCircuit.op_partialWord_frame`). The branches weighted by their coefficients sum to the
operator of the circuit read on the blocks (`SourceCircuit.sum_coefficient_smul_op_partialWord`):
at a touched gate the sum over the labels is the weighted sum of the branches of the prepared
gate, at an untouched gate there is one branch, the whole gate, and a composition multiplies the
two sums.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit` — party circuits of prepared gates.
* `QuantumCircuit.Party.SourceCircuit.Choices`, `QuantumCircuit.Party.SourceCircuit.coefficient`,
  `QuantumCircuit.Party.SourceCircuit.partialWord` — partial expansions.
* `QuantumCircuit.Party.SourceCircuit.frame` — a source circuit beside spectator factors.

## Main results

* `QuantumCircuit.Party.SourceCircuit.norm_op_le_one` — a source circuit with contractive local
  operations is a contraction.
* `QuantumCircuit.Party.SourceCircuit.op_partialWord_gate_of_isTouched`,
  `QuantumCircuit.Party.SourceCircuit.op_partialWord_gate_of_not_isTouched` — the branch at a
  gate.
* `QuantumCircuit.Party.SourceCircuit.sum_coefficient_smul_op_partialWord` — the partial expansion
  sums to the circuit.
* `QuantumCircuit.Party.SourceCircuit.op_frame`,
  `QuantumCircuit.Party.SourceCircuit.coefficient_frame`,
  `QuantumCircuit.Party.SourceCircuit.op_partialWord_frame` — framing.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 21–36, 133–151, 233–267 and 351–417 (equation `eq:compression-choice-cost`).
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Source circuits -/

/-- A chronological composition of source-prepared gates and arbitrary local operations; every gate
carries its contraction bound. Source: Theorem 5.2, `04-compression.tex`, lines 21–36, 133–151 and
233–267. -/
abbrev SourceCircuit (X Y : P → Type) := PartyCircuit (PreparedGate (P := P)) X Y

namespace SourceCircuit

/-- The operator of a source circuit. -/
noncomputable abbrev op [Fintype P] {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] (w : SourceCircuit X Y) : Matrix (Config Y) (Config X) ℂ :=
  PartyCircuit.op PreparedGate.ev w

/-- The operator of one prepared gate: its weighted branch sum on the cell, the identity
outside. Source: `04-compression.tex`, lines 21–36 and 233–267. -/
@[simp] theorem op_gate [Fintype P] {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (D : Finset P)
    (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y) :
    SourceCircuit.op (PartyCircuit.gate D hY g : SourceCircuit X Y) =
      placeBetween D hY g.gate.eval :=
  PartyCircuit.op_gate _ D hY g

/-- A source circuit whose local operations are contractions is allowed, with no condition on its
gates: every prepared gate is a contraction. -/
theorem isAllowed_of_isLocalContractive : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → {w : SourceCircuit X Y} → w.IsLocalContractive →
      w.IsAllowed PreparedGate.ev fun _ _ _ _ _ _ _ _ ↦ True
  | _, _, _, _, PartyCircuit.done _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ g, _ => ⟨PreparedGate.norm_ev_le_one g _, trivial⟩
  | _, _, _, _, PartyCircuit.localOp _ _ _, h => h
  | _, _, _, _, PartyCircuit.localOps _, h => h
  | _, _, _, _, PartyCircuit.comp _ _, h =>
    ⟨isAllowed_of_isLocalContractive h.1, isAllowed_of_isLocalContractive h.2⟩

/-- **A source circuit whose local operations are contractions is a contraction**, every
prepared gate carrying its bound. Source: `04-compression.tex`, line 28 and lines 215–216. -/
theorem norm_op_le_one [Fintype P] {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] {w : SourceCircuit X Y}
    (hw : w.IsLocalContractive) : ‖w.op‖ ≤ 1 :=
  PartyCircuit.norm_op_le_one _ (isAllowed_of_isLocalContractive hw)

/-! ### Partial expansions along affected parties -/

/-- Monomial choices occur exactly at gates touching the affected parties.
Source: Theorem 5.2, `04-compression.tex`, lines 351–381. -/
def Choices (A : P → Bool) : {X Y : P → Type} → SourceCircuit X Y → Type
  | _, _, PartyCircuit.done _ => Unit
  | _, _, PartyCircuit.gate D _ g => if PreparedGate.IsTouched A D then g.ι else Unit
  | _, _, PartyCircuit.localOp _ _ _ => Unit
  | _, _, PartyCircuit.localOps _ => Unit
  | _, _, PartyCircuit.comp c c' => Choices A c × Choices A c'

/-- A partial expansion has finitely many monomial choices. -/
instance choicesFintype (A : P → Bool) : {X Y : P → Type} → (c : SourceCircuit X Y) →
    Fintype (Choices A c)
  | _, _, PartyCircuit.done _ => inferInstanceAs (Fintype Unit)
  | _, _, PartyCircuit.gate D _ g => by
    dsimp only [Choices]
    split <;> infer_instance
  | _, _, PartyCircuit.localOp _ _ _ => inferInstanceAs (Fintype Unit)
  | _, _, PartyCircuit.localOps _ => inferInstanceAs (Fintype Unit)
  | _, _, PartyCircuit.comp c c' =>
    letI := choicesFintype A c
    letI := choicesFintype A c'
    inferInstanceAs (Fintype (Choices A c × Choices A c'))

/-- The label chosen at a touched gate. -/
def choiceLabel (A : P → Bool) {X Y : P → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    {D : Finset P} (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y)
    (h : PreparedGate.IsTouched A D)
    (ξ : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y)) : g.ι :=
  cast (ite_eq_left h) ξ

/-- Scalar weights are charged only at gates whose labels are expanded.
Source: Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex`, lines 351–381. -/
noncomputable def coefficient (A : P → Bool) : {X Y : P → Type} → (c : SourceCircuit X Y) →
    Choices A c → ℂ
  | _, _, PartyCircuit.done _, _ => 1
  | _, _, PartyCircuit.gate D hY g, ξ =>
    if h : PreparedGate.IsTouched A D then g.coeff (choiceLabel A hY g h ξ) else 1
  | _, _, PartyCircuit.localOp _ _ _, _ => 1
  | _, _, PartyCircuit.localOps _, _ => 1
  | _, _, PartyCircuit.comp c c', ξ => coefficient A c ξ.1 * coefficient A c' ξ.2

omit [DecidableEq P] in
/-- The parties of an untouched cell all go to the exterior party. -/
theorem affectedOwner_eq_none_of_not_isTouched {A : P → Bool} {D : Finset P}
    (h : ¬ PreparedGate.IsTouched A D) : ∀ s ∈ D, affectedOwner A s = none := by
  intro s hs
  simp only [PreparedGate.IsTouched, not_exists, not_and, Bool.not_eq_true] at h
  exact (affectedOwner_eq_none A s).mpr (h s hs)

/-- An untouched cell lies in the exterior block. -/
theorem subset_blockPreimage_of_not_isTouched [Fintype P] {A : P → Bool} {D : Finset P}
    (h : ¬ PreparedGate.IsTouched A D) : D ⊆ blockPreimage (affectedOwner A) {none} :=
  fun s hs ↦ by simpa using affectedOwner_eq_none_of_not_isTouched h s hs

/-- Outside the exterior block an untouched gate changes nothing. -/
theorem eq_of_notMem_blockPreimage_of_not_isTouched [Fintype P] {A : P → Bool}
    {D : Finset P} {X Y : P → Type} (h : ¬ PreparedGate.IsTouched A D)
    (hY : ∀ s ∉ D, Y s = X s) : ∀ v ∉ blockPreimage (affectedOwner A) {none}, Y v = X v :=
  fun v hv ↦ hY v fun hvD ↦ hv (subset_blockPreimage_of_not_isTouched h hvD)

/-- Outside the exterior block an untouched gate changes nothing, read on the blocks. -/
theorem blockSystem_eq_of_not_isTouched [Fintype P] {A : P → Bool} {D : Finset P}
    {X Y : P → Type} (h : ¬ PreparedGate.IsTouched A D) (hY : ∀ s ∉ D, Y s = X s) :
    ∀ q ≠ none, blockSystem (affectedOwner A) Y q = blockSystem (affectedOwner A) X q :=
  fun q hq ↦ blockSystem_eq_of_notMem (affectedOwner A) (D' := {none})
    (eq_of_notMem_blockPreimage_of_not_isTouched h hY) q (by simpa using hq)

/-- The actual branch of a partial expansion, on the affected parties and one exterior party:
the chosen branch at a touched gate, run on its cell and read on the blocks; at an untouched gate
the whole gate as one local operation of the exterior party, its matrix extended to the exterior
block by the identity (`subregionPlaceBetween`), as `Word.coarsen` treats a source inside one
block; the local operations read on the blocks. Source:
Theorem 5.2, `04-compression.tex`, lines 351–417. -/
noncomputable def partialWord [Fintype P] (A : P → Bool) : {X Y : P → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    (c : SourceCircuit X Y) → Choices A c →
      Word (blockSystem (affectedOwner A) X) (blockSystem (affectedOwner A) Y)
  | _, _, _, _, PartyCircuit.done _, _ => PartyCircuit.done _
  | _, _, _, _, PartyCircuit.gate D hY g, ξ =>
    if h : PreparedGate.IsTouched A D then
      Word.coarsen (affectedOwner A)
        (Word.onCell D hY (g.gate.branchWord (choiceLabel A hY g h ξ)))
    else
      PartyCircuit.localOp none (blockSystem_eq_of_not_isTouched h hY)
        (subregionPlaceBetween (subset_blockPreimage_of_not_isTouched h) hY g.gate.eval)
  | _, _, _, _, PartyCircuit.localOp p hY U, _ =>
    Word.coarsen (affectedOwner A) (PartyCircuit.localOp p hY U : Word _ _)
  | _, _, _, _, PartyCircuit.localOps U, _ =>
    Word.coarsen (affectedOwner A) (PartyCircuit.localOps U : Word _ _)
  | _, _, _, _, PartyCircuit.comp c c', ξ =>
    PartyCircuit.comp (partialWord A c ξ.1) (partialWord A c' ξ.2)

/-! #### Computation rules -/

variable (A : P → Bool) {X Y Z : P → Type} [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The empty circuit has one choice. -/
@[simp] theorem choices_done : Choices A (PartyCircuit.done X : SourceCircuit X X) = Unit :=
  rfl

/-- A choice of a composition is a choice of each part. -/
@[simp] theorem choices_comp (w : SourceCircuit X Y) (w' : SourceCircuit Y Z) :
    Choices A (PartyCircuit.comp w w') = (Choices A w × Choices A w') :=
  rfl

/-- A local operation has one choice. -/
@[simp] theorem choices_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s) (U : Matrix (Y p) (X p) ℂ) :
    Choices A (PartyCircuit.localOp p hY U : SourceCircuit X Y) = Unit :=
  rfl

/-- Local operations at every party have one choice. -/
@[simp] theorem choices_localOps (U : ∀ p, Matrix (Y p) (X p) ℂ) :
    Choices A (PartyCircuit.localOps U : SourceCircuit X Y) = Unit :=
  rfl

/-- The choices at one gate: its labels when the gate is touched, one choice otherwise. -/
@[simp] theorem choices_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y) :
    Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y) =
      if PreparedGate.IsTouched A D then g.ι else Unit :=
  rfl

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The coefficient of the empty circuit is `1`. -/
@[simp] theorem coefficient_done (ξ : Choices A (PartyCircuit.done X : SourceCircuit X X)) :
    coefficient A (PartyCircuit.done X : SourceCircuit X X) ξ = 1 :=
  rfl

/-- The coefficient of a composition is the product of the coefficients of its parts. -/
@[simp] theorem coefficient_comp (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (ξ : Choices A (PartyCircuit.comp w w')) :
    coefficient A (PartyCircuit.comp w w') ξ = coefficient A w ξ.1 * coefficient A w' ξ.2 :=
  rfl

/-- The coefficient of a local operation is `1`. -/
@[simp] theorem coefficient_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (U : Matrix (Y p) (X p) ℂ) (ξ : Choices A (PartyCircuit.localOp p hY U : SourceCircuit X Y)) :
    coefficient A (PartyCircuit.localOp p hY U : SourceCircuit X Y) ξ = 1 :=
  rfl

/-- The coefficient of local operations at every party is `1`. -/
@[simp] theorem coefficient_localOps (U : ∀ p, Matrix (Y p) (X p) ℂ)
    (ξ : Choices A (PartyCircuit.localOps U : SourceCircuit X Y)) :
    coefficient A (PartyCircuit.localOps U : SourceCircuit X Y) ξ = 1 :=
  rfl

/-- The coefficient at a gate: the coefficient of the chosen label when the gate is touched. -/
theorem coefficient_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y)
    (ξ : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    coefficient A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ =
      if h : PreparedGate.IsTouched A D then g.coeff (choiceLabel A hY g h ξ) else 1 :=
  rfl

section PartialWord

variable [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The branch of the empty circuit is the empty word. -/
@[simp] theorem partialWord_done (ξ : Choices A (PartyCircuit.done X : SourceCircuit X X)) :
    partialWord A (PartyCircuit.done X : SourceCircuit X X) ξ = PartyCircuit.done _ :=
  rfl

/-- The branch of a composition is the composition of the branches of its parts. -/
@[simp] theorem partialWord_comp (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (ξ : Choices A (PartyCircuit.comp w w')) :
    partialWord A (PartyCircuit.comp w w') ξ =
      PartyCircuit.comp (partialWord A w ξ.1) (partialWord A w' ξ.2) :=
  rfl

/-- The branch of a local operation is the local operation read on the blocks. -/
@[simp] theorem partialWord_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (U : Matrix (Y p) (X p) ℂ) (ξ : Choices A (PartyCircuit.localOp p hY U : SourceCircuit X Y)) :
    partialWord A (PartyCircuit.localOp p hY U : SourceCircuit X Y) ξ =
      Word.coarsen (affectedOwner A) (PartyCircuit.localOp p hY U : Word X Y) :=
  rfl

/-- The branch of local operations at every party is those operations read on the blocks. -/
@[simp] theorem partialWord_localOps (U : ∀ p, Matrix (Y p) (X p) ℂ)
    (ξ : Choices A (PartyCircuit.localOps U : SourceCircuit X Y)) :
    partialWord A (PartyCircuit.localOps U : SourceCircuit X Y) ξ =
      Word.coarsen (affectedOwner A) (PartyCircuit.localOps U : Word X Y) :=
  rfl

/-- The branch at a touched gate: the chosen branch word run on its cell, read on the blocks. -/
theorem partialWord_gate_of_isTouched (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (h : PreparedGate.IsTouched A D)
    (ξ : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    partialWord A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ =
      Word.coarsen (affectedOwner A)
        (Word.onCell D hY (g.gate.branchWord (choiceLabel A hY g h ξ))) :=
  dite_eq_left h

/-- The branch at an untouched gate: the whole gate as one local operation of the exterior
party, its matrix extended to the exterior block by the identity. -/
theorem partialWord_gate_of_not_isTouched (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (h : ¬ PreparedGate.IsTouched A D)
    (ξ : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    partialWord A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ =
      PartyCircuit.localOp none (blockSystem_eq_of_not_isTouched h hY)
        (subregionPlaceBetween (subset_blockPreimage_of_not_isTouched h) hY g.gate.eval) :=
  dite_eq_right h

/-- The operator of the branch at a touched gate: the chosen branch placed on the cell, read on
the blocks. -/
theorem op_partialWord_gate_of_isTouched (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (h : PreparedGate.IsTouched A D)
    (ξ : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    Word.op (partialWord A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ) =
      reindex (blockConfigEquiv (affectedOwner A) Y).symm
        (blockConfigEquiv (affectedOwner A) X).symm
        (placeBetween D hY (g.gate.branchWord (choiceLabel A hY g h ξ)).op) := by
  rw [partialWord_gate_of_isTouched A D hY g h ξ, Word.op_coarsen, Word.op_onCell]

/-- The operator of the branch at an untouched gate: the whole gate placed on its cell, read on
the blocks. -/
theorem op_partialWord_gate_of_not_isTouched (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (h : ¬ PreparedGate.IsTouched A D)
    (ξ : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    Word.op (partialWord A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ) =
      reindex (blockConfigEquiv (affectedOwner A) Y).symm
        (blockConfigEquiv (affectedOwner A) X).symm (placeBetween D hY g.gate.eval) := by
  rw [partialWord_gate_of_not_isTouched A D hY g h ξ,
    ← placeBetween_subregionPlaceBetween (subset_blockPreimage_of_not_isTouched h) hY
      (eq_of_notMem_blockPreimage_of_not_isTouched h hY),
    ← reindex_blockConfigEquiv_placeBetween_singleton (affectedOwner A) none
      (eq_of_notMem_blockPreimage_of_not_isTouched h hY)]
  unfold Word.op
  rw [PartyCircuit.op_localOp, reindex_apply, reindex_apply, submatrix_submatrix,
    Equiv.symm_symm, Equiv.symm_symm, Equiv.symm_comp_self, Equiv.symm_comp_self,
    submatrix_id_id]

end PartialWord

/-! #### Source circuits beside spectator factors -/

section Frame

variable (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- A source circuit beside the spectator factors `W`: every prepared gate
framed by the factors of its cell, every local operation `A` replaced by `1 ⊗ A`. -/
abbrev frame [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (w : SourceCircuit X Y) :
    SourceCircuit (fun p ↦ W p × X p) (fun p ↦ W p × Y p) :=
  PartyCircuit.frame W w

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **The operator of a framed source circuit is `1 ⊗ op`**. -/
theorem op_frame [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (w : SourceCircuit X Y) :
    (w.frame W).op =
      reindex (Equiv.arrowProdEquivProdArrow P W Y).symm
        (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ w.op) :=
  PartyCircuit.op_frame W _ PreparedGate.isCompatible_frame w

/-- The choices of a framed circuit are those of the circuit. -/
def choicesFrameEquiv : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (w : SourceCircuit X Y) → Choices A (w.frame W) ≃ Choices A w
  | _, _, _, _, PartyCircuit.done _ => Equiv.refl _
  | _, _, _, _, PartyCircuit.gate _ _ _ => Equiv.refl _
  | _, _, _, _, PartyCircuit.localOp _ _ _ => Equiv.refl _
  | _, _, _, _, PartyCircuit.localOps _ => Equiv.refl _
  | _, _, _, _, PartyCircuit.comp c c' =>
    (choicesFrameEquiv c).prodCongr (choicesFrameEquiv c')

/-- The coefficient of a choice of a framed circuit is the coefficient of the choice. -/
theorem coefficient_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) → (ξ : Choices A (w.frame W)) →
      coefficient A (w.frame W) ξ = coefficient A w (choicesFrameEquiv A W w ξ)
  | _, _, _, _, PartyCircuit.done _, _ => rfl
  | _, _, _, _, PartyCircuit.gate _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOps _, _ => rfl
  | _, _, _, _, PartyCircuit.comp c c', ξ =>
    congrArg₂ (· * ·) (coefficient_frame c ξ.1) (coefficient_frame c' ξ.2)

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- A framed word read on the blocks of `f` is `1 ⊗` the word read on the blocks. -/
theorem op_coarsen_frame [Fintype P] {Q : Type} [Fintype Q] [DecidableEq Q] (f : P → Q)
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (v : Word X Y) :
    Word.op (Word.coarsen f (v.frame W)) =
      reindex (blockConfigProdEquiv f W Y).symm (blockConfigProdEquiv f W X).symm
        ((1 : Matrix (Config (blockSystem f W)) (Config (blockSystem f W)) ℂ) ⊗ₖ
          Word.op (Word.coarsen f v)) := by
  rw [Word.op_coarsen, Word.op_frame, Word.op_coarsen, reindex_blockConfigEquiv_one_kronecker]

/-- The branch of a partial expansion of a framed circuit is `1 ⊗` the branch of the circuit,
read on the blocks. -/
theorem op_partialWord_frame [Fintype P] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) → (ξ : Choices A (w.frame W)) →
      Word.op (partialWord A (w.frame W) ξ) =
        reindex (blockConfigProdEquiv (affectedOwner A) W Y).symm
          (blockConfigProdEquiv (affectedOwner A) W X).symm
          ((1 : Matrix (Config (blockSystem (affectedOwner A) W))
            (Config (blockSystem (affectedOwner A) W)) ℂ) ⊗ₖ
            Word.op (partialWord A w (choicesFrameEquiv A W w ξ)))
  | _, _, _, _, PartyCircuit.done X, _ =>
    op_coarsen_frame W (affectedOwner A) (PartyCircuit.done X : Word X X)
  | _, _, _, _, PartyCircuit.localOp p hY U, _ =>
    op_coarsen_frame W (affectedOwner A) (PartyCircuit.localOp p hY U : Word _ _)
  | _, _, _, _, PartyCircuit.localOps U, _ =>
    op_coarsen_frame W (affectedOwner A) (PartyCircuit.localOps U : Word _ _)
  | _, _, _, _, PartyCircuit.gate D hY g, ξ => by
    by_cases h : PreparedGate.IsTouched A D
    · refine (op_partialWord_gate_of_isTouched A D (fun s hs ↦ congrArg (W s × ·) (hY s hs))
        (GateFrame.frame W g) h ξ).trans ?_
      rw [op_partialWord_gate_of_isTouched A D hY g h]
      refine (congrArg (reindex _ _) ((congrArg (placeBetween D _)
        (g.gate.op_branchWord_frame (fun s : ↥D ↦ W s) _)).trans
        (placeBetween_reindex_one_kronecker hY _ _))).trans ?_
      exact reindex_blockConfigEquiv_one_kronecker _ _
    · refine (op_partialWord_gate_of_not_isTouched A D
        (fun s hs ↦ congrArg (W s × ·) (hY s hs)) (GateFrame.frame W g) h ξ).trans ?_
      rw [op_partialWord_gate_of_not_isTouched A D hY g h]
      refine (congrArg (reindex _ _) ((congrArg (placeBetween D _)
        (g.gate.eval_frame (fun s : ↥D ↦ W s))).trans
        (placeBetween_reindex_one_kronecker hY _ _))).trans ?_
      exact reindex_blockConfigEquiv_one_kronecker _ _
  | _, _, _, _, PartyCircuit.comp c c', ξ => by
    refine (Word.op_comp _ _).trans (((congrArg₂ (· * ·) (op_partialWord_frame c' ξ.2)
      (op_partialWord_frame c ξ.1)).trans ?_).trans
      (congrArg (reindex _ _) (congrArg (kroneckerMap (· * ·) 1) (Word.op_comp _ _).symm)))
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul,
      Matrix.one_mul]
    rfl

end Frame

end SourceCircuit

/-! ### The sum of a partial expansion -/

namespace SourceCircuit

/-- **The partial expansion sums to the circuit.** The weighted sum, over the choices of branch
labels at the gates meeting the affected parties `A`, of the branches of the partial expansion is
the operator of the source circuit, read on the affected parties and the exterior party along
`blockConfigEquiv`. Source: Theorem 5.2, `04-compression.tex`, lines 353–361 and 415–417. -/
theorem sum_coefficient_smul_op_partialWord [Fintype P] (A : P → Bool) :
    {X Y : P → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    (w : SourceCircuit X Y) →
      ∑ ξ, coefficient A w ξ • Word.op (partialWord A w ξ) =
        reindex (blockConfigEquiv (affectedOwner A) Y).symm
          (blockConfigEquiv (affectedOwner A) X).symm w.op
  | _, _, _, _, PartyCircuit.done X => by
    change ∑ _ξ : Unit, (1 : ℂ) • Word.op (PartyCircuit.done _) = _
    rw [Fintype.sum_unique, one_smul, Word.op, PartyCircuit.op_done, SourceCircuit.op,
      PartyCircuit.op_done]
    ext
    simp [one_apply]
  | _, _, _, _, PartyCircuit.gate D hY g => by
    rw [SourceCircuit.op_gate]
    by_cases h : PreparedGate.IsTouched A D
    · let e : Choices A (PartyCircuit.gate D hY g : SourceCircuit _ _) ≃ g.ι :=
        Equiv.cast (ite_eq_left h)
      simp only [coefficient_gate, dite_eq_left h, op_partialWord_gate_of_isTouched A D hY g h]
      refine (Fintype.sum_equiv e _
        (fun i ↦ g.coeff i • reindex (blockConfigEquiv (affectedOwner A) _).symm
          (blockConfigEquiv (affectedOwner A) _).symm
          (placeBetween D hY (g.gate.branchWord i).op)) fun _ ↦ rfl).trans ?_
      rw [show g.gate.eval = ∑ i, g.coeff i • (g.gate.branchWord i).op from rfl,
        placeBetween_sum]
      simp only [placeBetween_smul, reindex_apply, submatrix_sum, submatrix_smul, Pi.smul_apply]
    · let e : Choices A (PartyCircuit.gate D hY g : SourceCircuit _ _) ≃ Unit :=
        Equiv.cast (ite_eq_right h)
      refine (Fintype.sum_equiv e _
        (fun _ ↦ reindex (blockConfigEquiv (affectedOwner A) _).symm
          (blockConfigEquiv (affectedOwner A) _).symm (placeBetween D hY g.gate.eval))
        fun ξ ↦ by
          rw [coefficient_gate, dite_eq_right h, one_smul,
            op_partialWord_gate_of_not_isTouched A D hY g h]).trans ?_
      exact Fintype.sum_unique _
  | _, _, _, _, PartyCircuit.localOp p hY U => by
    change ∑ _ξ : Unit, (1 : ℂ) • Word.op (Word.coarsen (affectedOwner A)
      (PartyCircuit.localOp p hY U : Word _ _)) = _
    rw [Fintype.sum_unique, one_smul, Word.op_coarsen, Word.op, PartyCircuit.op_localOp,
      SourceCircuit.op, PartyCircuit.op_localOp]
  | _, _, _, _, PartyCircuit.localOps U => by
    change ∑ _ξ : Unit, (1 : ℂ) • Word.op (Word.coarsen (affectedOwner A)
      (PartyCircuit.localOps U : Word _ _)) = _
    rw [Fintype.sum_unique, one_smul, Word.op_coarsen, Word.op, PartyCircuit.op_localOps,
      SourceCircuit.op, PartyCircuit.op_localOps]
  | _, _, _, _, PartyCircuit.comp c c' => by
    have key : ∑ ξ, coefficient A (PartyCircuit.comp c c') ξ •
          Word.op (partialWord A (PartyCircuit.comp c c') ξ) =
        (∑ ξ', coefficient A c' ξ' • Word.op (partialWord A c' ξ')) *
          ∑ ξ, coefficient A c ξ • Word.op (partialWord A c ξ) := by
      simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
        Finset.smul_sum, smul_smul]
      refine (Fintype.sum_prod_type _).trans
        (Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ξ' _ ↦ ?_)
      exact congrArg ((coefficient A c ξ * coefficient A c' ξ') • ·) (Word.op_comp _ _)
    rw [key, sum_coefficient_smul_op_partialWord A c, sum_coefficient_smul_op_partialWord A c',
      reindex_apply, reindex_apply, submatrix_mul_equiv, reindex_apply]
    simp only [SourceCircuit.op, PartyCircuit.op_comp]

end SourceCircuit

end QuantumCircuit.Party
