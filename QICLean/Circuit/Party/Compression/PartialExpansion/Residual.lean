/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Sources
import QICLean.Circuit.Party.Monomial.Stack

/-!
# The residual of a partial expansion in the common slots

The local part of a word, which acts after the preparation of all its sources, is read in the
system of a slot inventory through a configuration equivalence (`Word.residualInSlots`); with the
identification given by an inventory equation, preparing the slots and then applying it gives
the word back (`Word.op_residualInSlots_mul_prepareSlots`). For a branch of a partial expansion,
the slots are the common slots and the residual is `SourceCircuit.partialResidual`: one word on a
system that does not depend on the labels.

When every party is affected, the private preparation of a product input
(`SourceCircuit.sourcePrivatePreparation`) prepares the product vector beside the fresh factors of
the slots (`PartyCircuit.liftSlots`) and leaves them unchanged; followed by the residual it is the
prepared source word `SourceCircuit.partialSourceWord`, whose input is the system of the slots
alone (`SourceCircuit.allSourceSystem`).

## Main definitions

* `QuantumCircuit.Party.SourceInventory.slotSystemEquiv` — the identification of the slot
  system with the system of an equal inventory.
* `QuantumCircuit.Party.SourceInventory.slotFresh`,
  `QuantumCircuit.Party.SourceInventory.slotConfigEquiv`,
  `QuantumCircuit.Party.PartyCircuit.liftSlots` — circuits beside the fresh factors of slots.
* `QuantumCircuit.Party.Word.residualInSlots`,
  `QuantumCircuit.Party.SourceCircuit.partialResidual` — residuals.
* `QuantumCircuit.Party.SourceCircuit.allSourceSystem`,
  `QuantumCircuit.Party.SourceCircuit.sourcePrivatePreparation`,
  `QuantumCircuit.Party.SourceCircuit.partialSourceWord` — the prepared source word.

## Main results

* `QuantumCircuit.Party.Word.op_residualInSlots_mul_prepareSlots`,
  `QuantumCircuit.Party.SourceCircuit.op_partialResidual_mul_prepareSlots`.
* `QuantumCircuit.Party.PartyCircuit.op_liftSlots`,
  `QuantumCircuit.Party.SourceCircuit.op_sourcePrivatePreparation`,
  `QuantumCircuit.Party.SourceCircuit.op_partialSourceWord`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 137–139, 246–267 and 409–434.

Adapted from TNLean, `TNLean/Lattice/Compression/SourceResidualCoordinates.lean`,
`TNLean/Lattice/Compression/ActualSourceRegisters.lean`,
`TNLean/Lattice/Compression/SourcePrivatePreparation.lean`,
`TNLean/Lattice/Compression/SourcePrivatePreparationEvaluation.lean` and
`TNLean/Lattice/Compression/PartialSourceWordEvaluation.lean` at commit `a05f5d6d0a`
(Apache-2.0). Changes: the identification of register lists is a configuration equivalence; the
spectator source registers are fresh factors of the slot system.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Slot systems -/

namespace SourceInventory

/-- The identification of the slot system with the system of an inventory equal to the slots
with some vectors. Source: Theorem 5.2, `04-compression.tex`, lines 253–267. -/
def slotSystemEquiv (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (S : SourceInventory P)
    (h : ofSlots R B η = S) (Z : P → Type) (p : P) : slotSystem R B Z p ≃ S.system Z p :=
  Equiv.cast (congrFun ((system_ofSlots R B η Z).symm.trans (congrArg (system · Z) h)) p)

/-- The identification carries the slot preparation to the preparation of the inventory.
Source: Theorem 5.2, `04-compression.tex`, lines 253–267. -/
theorem op_relabel_slotSystemEquiv_mul_prepareSlots [Fintype P] {Z : P → Type}
    [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] (R : SourceInventory P)
    (B : SlotBases R.length) (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (S : SourceInventory P) (h : ofSlots R B η = S) :
    Word.op (PartyCircuit.relabel (G := SourceGate)
        fun p ↦ (slotSystemEquiv R B η S h Z p).symm) * (prepareSlots R B η Z).op =
      (S.prepare Z).op := by
  subst h
  exact op_relabel_cast_mul_of_heq (system_ofSlots R B η Z).symm (prepareSlots_heq R B η)

/-- The configurations of the fresh factors of slots: one pair of basis elements per slot, the
first slot first. -/
def slotFresh : (R : SourceInventory P) → SlotBases R.length → Type
  | [], _ => Unit
  | _ :: R, B => (B.left 0 × B.right 0) × slotFresh R B.tail

/-- The fresh configurations of slots are finite. -/
@[instance_reducible] def slotFreshFintype : (R : SourceInventory P) →
    (B : SlotBases R.length) → Fintype (slotFresh R B)
  | [], _ => inferInstanceAs (Fintype Unit)
  | _ :: R, B =>
    letI := slotFreshFintype R B.tail
    inferInstanceAs (Fintype ((B.left 0 × B.right 0) × slotFresh R B.tail))

/-- The fresh configurations of slots have decidable equality. -/
@[instance_reducible] def slotFreshDecidableEq : (R : SourceInventory P) →
    (B : SlotBases R.length) → DecidableEq (slotFresh R B)
  | [], _ => inferInstanceAs (DecidableEq Unit)
  | _ :: R, B =>
    letI := slotFreshDecidableEq R B.tail
    inferInstanceAs (DecidableEq ((B.left 0 × B.right 0) × slotFresh R B.tail))

/-- The fresh configurations of slots are finite. -/
instance (R : SourceInventory P) (B : SlotBases R.length) : Fintype (slotFresh R B) :=
  slotFreshFintype R B

/-- The fresh configurations of slots have decidable equality. -/
instance (R : SourceInventory P) (B : SlotBases R.length) : DecidableEq (slotFresh R B) :=
  slotFreshDecidableEq R B

/-- A configuration of the slot system is a fresh configuration and one of the underlying
system. -/
def slotConfigEquiv : (R : SourceInventory P) → (B : SlotBases R.length) → (Z : P → Type) →
    Config (slotSystem R B Z) ≃ slotFresh R B × Config Z
  | [], _, _ => (Equiv.punitProd _).symm
  | r :: R, B, Z =>
    (addPairConfigEquiv (X := slotSystem R B.tail Z) r.distinct (B.left 0) (B.right 0)).trans
      (((Equiv.refl _).prodCongr (slotConfigEquiv R B.tail Z)).trans
        (Equiv.prodAssoc _ _ _).symm)

end SourceInventory

/-- Two identity factors in front, read along two products of equivalences, are one identity
factor on the product. -/
private theorem reindex_one_kronecker_reindex_one {α β m m' m'' n n' n'' : Type}
    [DecidableEq α] [DecidableEq β] (eT : m ≃ α × m') (eS : n ≃ α × n') (fT : m' ≃ β × m'')
    (fS : n' ≃ β × n'') (M : Matrix m'' n'' ℂ) :
    reindex eT.symm eS.symm
        ((1 : Matrix α α ℂ) ⊗ₖ reindex fT.symm fS.symm ((1 : Matrix β β ℂ) ⊗ₖ M)) =
      reindex (eT.trans (((Equiv.refl α).prodCongr fT).trans (Equiv.prodAssoc α β m'').symm)).symm
        (eS.trans (((Equiv.refl α).prodCongr fS).trans (Equiv.prodAssoc α β n'').symm)).symm
        ((1 : Matrix (α × β) (α × β) ℂ) ⊗ₖ M) := by
  ext y x
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.prodAssoc_symm_apply, kroneckerMap_apply,
    one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

namespace PartyCircuit

variable [Fintype P] {G : Finset P → (P → Type) → (P → Type) → Type 1} [GateFamily G]
  [GateFrame G]

/-- A circuit beside the fresh factors of slots: lifted past one slot after another. -/
def liftSlots : (R : SourceInventory P) → (B : SourceInventory.SlotBases R.length) →
    {S T : P → Type} → [∀ s, Fintype (S s)] → [∀ s, DecidableEq (S s)] →
    [∀ s, Fintype (T s)] → [∀ s, DecidableEq (T s)] → PartyCircuit G S T →
      PartyCircuit G (SourceInventory.slotSystem R B S) (SourceInventory.slotSystem R B T)
  | [], _, _, _, _, _, _, _, c => c
  | r :: R, B, _, _, _, _, _, _, c =>
    (liftSlots R B.tail c).liftPair r.distinct (B.left 0) (B.right 0)

/-- **A circuit beside the fresh factors of slots acts as `1 ⊗ op`**, read along
`SourceInventory.slotConfigEquiv`. -/
theorem op_liftSlots [GateFamily.UniqueOutcome G] (ev : Interpretation G)
    (hev : GateFrame.IsCompatible G ev) : (R : SourceInventory P) →
    (B : SourceInventory.SlotBases R.length) → {S T : P → Type} → [∀ s, Fintype (S s)] →
    [∀ s, DecidableEq (S s)] → [∀ s, Fintype (T s)] → [∀ s, DecidableEq (T s)] →
    (c : PartyCircuit G S T) →
      (liftSlots R B c).op ev =
        reindex (SourceInventory.slotConfigEquiv R B T).symm
          (SourceInventory.slotConfigEquiv R B S).symm
          ((1 : Matrix (SourceInventory.slotFresh R B) (SourceInventory.slotFresh R B) ℂ) ⊗ₖ
            c.op ev)
  | [], _, _, _, _, _, _, _, c => by
    ext y x
    simp only [SourceInventory.slotConfigEquiv, reindex_apply, submatrix_apply,
      kroneckerMap_apply]
    exact (one_mul _).symm
  | r :: R, B, _, _, _, _, _, _, c => by
    refine (op_liftPair r.distinct (B.left 0) (B.right 0) ev hev (liftSlots R B.tail c)).trans ?_
    rw [op_liftSlots ev hev R B.tail c]
    exact reindex_one_kronecker_reindex_one _ _ _ _ _

end PartyCircuit

/-- A word without sources stays without sources beside the fresh factors of slots. -/
theorem Word.sources_liftSlots : (R : SourceInventory P) →
    (B : SourceInventory.SlotBases R.length) → {S T : P → Type} → [∀ s, Fintype (S s)] →
    [∀ s, DecidableEq (S s)] → [∀ s, Fintype (T s)] → [∀ s, DecidableEq (T s)] →
    (c : Word S T) → c.sources = [] → Word.sources (PartyCircuit.liftSlots R B c) = []
  | [], _, _, _, _, _, _, _, _, hc => hc
  | r :: R, B, _, _, _, _, _, _, c, hc => by
    change Word.sources (PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0)
      (PartyCircuit.liftSlots R B.tail c)) = []
    rw [PartyCircuit.liftPair, Word.sources_comp, Word.sources_comp,
      Word.sources_frame, Word.sources_liftSlots R B.tail c hc]
    rfl

/-! ### Residuals in slot systems -/

namespace Word

variable {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

/-- The local part of a word read in the system of a slot inventory, through a configuration
equivalence of the slot system with the system of the sources of the word. Source: Theorem 5.2,
`04-compression.tex`, lines 246–267. -/
def residualInSlots (w : Word X Y) (R : SourceInventory P) (B : SourceInventory.SlotBases R.length)
    (e : ∀ p, SourceInventory.slotSystem R B X p ≃ w.sources.system X p) :
    Word (SourceInventory.slotSystem R B X) Y :=
  (PartyCircuit.relabel fun p ↦ (e p).symm).comp w.localPart

/-- The residual contains no pair sources. Source: Theorem 5.2, `04-compression.tex`,
lines 246–251. -/
@[simp] theorem sources_residualInSlots (w : Word X Y) (R : SourceInventory P)
    (B : SourceInventory.SlotBases R.length)
    (e : ∀ p, SourceInventory.slotSystem R B X p ≃ w.sources.system X p) :
    (w.residualInSlots R B e).sources = [] :=
  rfl

/-- The residual of an allowed word is allowed. Source: Theorem 5.2, `04-compression.tex`,
lines 409–434. -/
theorem isAllowed_residualInSlots (w : Word X Y) (hw : w.IsAllowed) (R : SourceInventory P)
    (B : SourceInventory.SlotBases R.length)
    (e : ∀ p, SourceInventory.slotSystem R B X p ≃ w.sources.system X p) :
    (w.residualInSlots R B e).IsAllowed :=
  ⟨Word.isAllowed_relabel _, isAllowed_localPart hw⟩

/-- **Preparing a representation of the sources in the slots and then applying the residual
gives the word back.** Source: Theorem 5.2, `04-compression.tex`, lines 246–267. -/
theorem op_residualInSlots_mul_prepareSlots [Fintype P] (w : Word X Y) (R : SourceInventory P)
    (B : SourceInventory.SlotBases R.length) (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (hη : SourceInventory.ofSlots R B η = w.sources) :
    (w.residualInSlots R B (SourceInventory.slotSystemEquiv R B η w.sources hη X)).op *
        (SourceInventory.prepareSlots R B η X).op = w.op := by
  rw [residualInSlots, Word.op_comp, Matrix.mul_assoc,
    SourceInventory.op_relabel_slotSystemEquiv_mul_prepareSlots, op_localPart_mul_prepare]

end Word

/-! ### The residual of a branch -/

namespace SourceCircuit

variable (A : P → Bool) {X Y : P → Type} [Fintype P] [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The local part of a branch in the common slots. Source: Theorem 5.2, `04-compression.tex`,
lines 409–434. -/
noncomputable def partialResidual (w : SourceCircuit X Y) (ξ : Choices A w) :
    Word (SourceInventory.slotSystem (partialSlots A w) (partialSlotBases A w)
      (blockSystem (affectedOwner A) X)) (blockSystem (affectedOwner A) Y) :=
  (partialWord A w ξ).residualInSlots (partialSlots A w) (partialSlotBases A w)
    (SourceInventory.slotSystemEquiv _ _ _ _ (ofSlots_partialSlotVector A w ξ) _)

/-- The residual of a branch contains no pair sources. Source: Theorem 5.2,
`04-compression.tex`, lines 409–417. -/
@[simp] theorem sources_partialResidual (w : SourceCircuit X Y) (ξ : Choices A w) :
    (partialResidual A w ξ).sources = [] :=
  rfl

/-- The residual of a branch is allowed when the local operations of the circuit are
contractions. Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem isAllowed_partialResidual (w : SourceCircuit X Y) (hw : w.IsLocalContractive)
    (ξ : Choices A w) : (partialResidual A w ξ).IsAllowed :=
  Word.isAllowed_residualInSlots _ (isAllowed_partialWord A w hw ξ) _ _ _

/-- **The vectors of the chosen labels prepared in the slots, followed by the residual, give the
branch.** Source: Theorem 5.2, `04-compression.tex`, lines 342–417. -/
theorem op_partialResidual_mul_prepareSlots (w : SourceCircuit X Y) (ξ : Choices A w) :
    (partialResidual A w ξ).op *
        (SourceInventory.prepareSlots (partialSlots A w) (partialSlotBases A w)
          (partialSlotVector A w ξ) (blockSystem (affectedOwner A) X)).op =
      Word.op (partialWord A w ξ) :=
  Word.op_residualInSlots_mul_prepareSlots _ _ _ _ _

/-! ### The prepared source word -/

/-- The system of the slots of the expansion along all parties, over the system with one basis
vector at every block. Source: Theorem 5.2, `04-compression.tex`, lines 253–267 and 409–434. -/
abbrev allSourceSystem (w : SourceCircuit X Y) : Option {_p : P // true = true} → Type :=
  SourceInventory.slotSystem (partialSlots (fun _ ↦ true) w) (partialSlotBases (fun _ ↦ true) w)
    (blockSystem (affectedOwner fun _ ↦ true) fun _ ↦ Unit)

/-- The preparation of the product input `⊗_p φ_p` beside the fresh factors of the slots, which
it leaves unchanged. Source: Theorem 5.2, `04-compression.tex`, lines 137–139 and 253–267. -/
noncomputable def sourcePrivatePreparation (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) :
    Word (allSourceSystem w)
      (SourceInventory.slotSystem (partialSlots (fun _ ↦ true) w)
        (partialSlotBases (fun _ ↦ true) w) (blockSystem (affectedOwner fun _ ↦ true) X)) :=
  PartyCircuit.liftSlots _ _ (Word.coarsen (affectedOwner fun _ ↦ true) (Word.prepareProduct φ))

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The private preparation prepares no pair source. Source: Theorem 5.2,
`04-compression.tex`, lines 137–139. -/
@[simp] theorem sources_sourcePrivatePreparation (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) : (sourcePrivatePreparation w φ).sources = [] :=
  Word.sources_liftSlots _ _ _ (by rw [Word.sources_coarsen, Word.sources_prepareProduct]; rfl)

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **The private preparation inserts the product vector and leaves the fresh factors of the
slots unchanged.** Source: Theorem 5.2, `04-compression.tex`, lines 137–139 and 246–267. -/
theorem op_sourcePrivatePreparation (w : SourceCircuit X Y) (φ : ∀ p, EuclideanSpace ℂ (X p)) :
    (sourcePrivatePreparation w φ).op =
      reindex (SourceInventory.slotConfigEquiv _ _ _).symm
        (SourceInventory.slotConfigEquiv _ _ _).symm
        ((1 : Matrix (SourceInventory.slotFresh (partialSlots (fun _ ↦ true) w)
            (partialSlotBases (fun _ ↦ true) w))
          (SourceInventory.slotFresh (partialSlots (fun _ ↦ true) w)
            (partialSlotBases (fun _ ↦ true) w)) ℂ) ⊗ₖ
          Word.op (Word.coarsen (affectedOwner fun _ ↦ true) (Word.prepareProduct φ))) :=
  PartyCircuit.op_liftSlots _ SourceGate.isCompatible_frame _ _ _

/-- The prepared source word: the private preparation of the product input, then the residual
of the branch, from the fresh factors of the slots alone. Source: Theorem 5.2,
`04-compression.tex`, lines 137–139, 246–251 and 351–381. -/
noncomputable def partialSourceWord (w : SourceCircuit X Y) (φ : ∀ p, EuclideanSpace ℂ (X p))
    (ξ : Choices (fun _ ↦ true) w) :
    Word (allSourceSystem w) (blockSystem (affectedOwner fun _ ↦ true) Y) :=
  (sourcePrivatePreparation w φ).comp (partialResidual (fun _ ↦ true) w ξ)

/-- The prepared source word contains no pair source. Source: Theorem 5.2,
`04-compression.tex`, lines 246–251. -/
@[simp] theorem sources_partialSourceWord (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ : Choices (fun _ ↦ true) w) :
    (partialSourceWord w φ ξ).sources = [] := by
  rw [partialSourceWord, Word.sources_comp, sources_partialResidual,
    sources_sourcePrivatePreparation]
  rfl

/-- **The prepared source word applies the residual after inserting the product vector.**
Source: Theorem 5.2, `04-compression.tex`, lines 137–139 and 246–267. -/
theorem op_partialSourceWord (w : SourceCircuit X Y) (φ : ∀ p, EuclideanSpace ℂ (X p))
    (ξ : Choices (fun _ ↦ true) w) :
    (partialSourceWord w φ ξ).op = (partialResidual (fun _ ↦ true) w ξ).op *
      reindex (SourceInventory.slotConfigEquiv _ _ _).symm
        (SourceInventory.slotConfigEquiv _ _ _).symm
        ((1 : Matrix (SourceInventory.slotFresh (partialSlots (fun _ ↦ true) w)
            (partialSlotBases (fun _ ↦ true) w))
          (SourceInventory.slotFresh (partialSlots (fun _ ↦ true) w)
            (partialSlotBases (fun _ ↦ true) w)) ℂ) ⊗ₖ
          Word.op (Word.coarsen (affectedOwner fun _ ↦ true) (Word.prepareProduct φ))) := by
  rw [partialSourceWord, Word.op_comp, op_sourcePrivatePreparation]

end SourceCircuit

end QuantumCircuit.Party
