/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Monomial.Stack

/-!
# The stacks of a list of pair effects

In the replacement of Lemma 5.1 the stack of an effect occurrence on `(p, q)` consists of `m`
pair registers, the `ℂ^α` halves owned by `p` and the `ℂ^β` halves by `q`: on basis types, the
fresh factors `Fin m → α` at `p` and `Fin m → β` at `q` (`QICLean.Circuit.Party.Monomial.Stack`).
The stacks of a list of effects in front of a system are `stackApp`; their configurations are
those of the system and the stack configurations (`stackAppEquiv`). Their ideal content
`η^{⊗ m}`, one copy per effect, is prepared by pair sources (`op_prepStack`), and a word on the
other registers passes all stacks (`op_frameStack`). The stacks are owned by the endpoint
parties of the effects (`stackApp_of_forall_ne`, `card_stackApp`).

## Main definitions

* `QuantumCircuit.Party.stackApp`, `stackIdx`, `stackAppEquiv`, `stackIdxVector` — the stacks
  of a list of effects.
* `QuantumCircuit.Party.prepStack`, `frameStack` — their preparation, and a word beside them.

## Main results

* `QuantumCircuit.Party.op_prepStack`, `QuantumCircuit.Party.op_frameStack` — the operators.
* `QuantumCircuit.Party.stackApp_of_forall_ne`, `QuantumCircuit.Party.card_stackApp` —
  ownership and dimensions of the stacks.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 67–68 and 100–106.
-/

noncomputable section

open Matrix ManyBody EuclideanSpace CyclicInsertion
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ### The stacks of a list of effects -/

section Stacks

variable (m : ℕ)

/-- The stacks of all effect occurrences of the list `es`, in front of the system `T`: for an
effect on `(p, q)` with pair basis `α × β`, the fresh factors `Fin m → α` at `p` and
`Fin m → β` at `q`, the first effect outermost. Source: `04-compression.tex`, lines 100–103
(each occurrence has its own output stack of `m` pair registers, with the dimensions and
endpoint parties of its vector `η`). -/
@[reducible] def stackApp : List (PairSource P) → (P → Type) → (P → Type)
  | [], T => T
  | e :: es, T => stackSys e.distinct e.leftBasis e.rightBasis m (stackApp es T)

/-- The stacked systems are finite. -/
instance instFintypeStackApp : (es : List (PairSource P)) → (T : P → Type) →
    [∀ s, Fintype (T s)] → (s : P) → Fintype (stackApp m es T s)
  | [], _, h, s => h s
  | e :: es, T, _, s =>
      haveI := instFintypeStackApp es T
      inferInstanceAs
        (Fintype (addPair (stackApp m es T) e.distinct (Fin m → e.leftBasis)
          (Fin m → e.rightBasis) s))

/-- The stacked systems have decidable equality. -/
instance instDecidableEqStackApp : (es : List (PairSource P)) → (T : P → Type) →
    [∀ s, DecidableEq (T s)] → (s : P) → DecidableEq (stackApp m es T s)
  | [], _, h, s => h s
  | e :: es, T, _, s =>
      haveI := instDecidableEqStackApp es T
      inferInstanceAs
        (DecidableEq (addPair (stackApp m es T) e.distinct (Fin m → e.leftBasis)
          (Fin m → e.rightBasis) s))

/-- The stack configurations of a list of effects: one configuration `Fin m → α × β` of the
stack of each effect, in the order of the list, as in `EffectChain.stackIndex`. -/
@[reducible] def stackIdx : List (PairSource P) → Type
  | [] => Unit
  | e :: es => (Fin m → e.leftBasis × e.rightBasis) × stackIdx es

/-- The stack configurations form a finite type. -/
instance instFintypeStackIdx : (es : List (PairSource P)) → Fintype (stackIdx m es)
  | [] => inferInstanceAs (Fintype Unit)
  | e :: es =>
      haveI := instFintypeStackIdx es
      inferInstanceAs (Fintype ((Fin m → e.leftBasis × e.rightBasis) × stackIdx m es))

/-- The stack configurations have decidable equality. -/
instance instDecidableEqStackIdx : (es : List (PairSource P)) → DecidableEq (stackIdx m es)
  | [] => inferInstanceAs (DecidableEq Unit)
  | e :: es =>
      haveI := instDecidableEqStackIdx es
      inferInstanceAs (DecidableEq ((Fin m → e.leftBasis × e.rightBasis) × stackIdx m es))

/-- The configurations of the stacked system: a configuration of `T` and the stack
configurations. -/
def stackAppEquiv : (es : List (PairSource P)) → (T : P → Type) →
    Config (stackApp m es T) ≃ Config T × stackIdx m es
  | [], T => (Equiv.prodPUnit (Config T)).symm
  | e :: es, T =>
      (stackConfigEquiv e.distinct e.leftBasis e.rightBasis m (stackApp m es T)).trans
        (((Equiv.refl _).prodCongr (stackAppEquiv es T)).trans (Equiv.prodLeftComm _ _ _))

/-- The ideal content of the stacks: `η^{⊗ m}` in the stack of each effect. -/
def stackIdxVector : (es : List (PairSource P)) → EuclideanSpace ℂ (stackIdx m es)
  | [] => EuclideanSpace.single () 1
  | e :: es => vecKron (tensorPower (Fin m) e.vector) (stackIdxVector es)

omit [Fintype P] [DecidableEq P] in
/-- The ideal content of the stacks of normalized effects is a unit vector. -/
theorem norm_stackIdxVector : (es : List (PairSource P)) → (∀ e ∈ es, ‖e.vector‖ = 1) →
    ‖stackIdxVector m es‖ = 1
  | [], _ => by simp [stackIdxVector]
  | e :: es, h => by
      simp only [stackIdxVector]
      rw [norm_vecKron, norm_tensorPower (h e List.mem_cons_self),
        norm_stackIdxVector es fun e' he' ↦ h e' (List.mem_cons_of_mem _ he'), one_mul]

/-- Preparation of the ideal content of every stack by pair sources: `m` copies of the vector
of each effect on its endpoints. -/
def prepStack : (es : List (PairSource P)) → (T : P → Type) → [∀ s, Fintype (T s)] →
    [∀ s, DecidableEq (T s)] → Word T (stackApp m es T)
  | [], T, _, _ => PartyCircuit.done T
  | e :: es, T, _, _ =>
      (prepStack es T).comp (Word.prepWord e.distinct e.vector m (stackApp m es T))

/-- A word beside the stacks of all effects of the list. -/
def frameStack : (es : List (PairSource P)) → {S T : P → Type} → [∀ s, Fintype (S s)] →
    [∀ s, DecidableEq (S s)] → [∀ s, Fintype (T s)] → [∀ s, DecidableEq (T s)] →
    Word S T → Word (stackApp m es S) (stackApp m es T)
  | [], _, _, _, _, _, _, w => w
  | e :: es, _, _, _, _, _, _, w =>
      Word.framePairs e.distinct e.leftBasis e.rightBasis m (frameStack es w)

variable (es : List (PairSource P)) (T : P → Type) [∀ s, Fintype (T s)] [∀ s, DecidableEq (T s)]

omit [Fintype P] in
/-- The stack preparation of normalized effects is allowed. -/
theorem isAllowed_prepStack (h : ∀ e ∈ es, ‖e.vector‖ = 1) : (prepStack m es T).IsAllowed := by
  induction es generalizing T with
  | nil => exact Word.isAllowed_done
  | cons e es ih =>
      exact Word.IsAllowed.comp (ih T fun e' he' ↦ h e' (List.mem_cons_of_mem _ he'))
        (Word.isAllowed_prepWord _ _ _ (h e List.mem_cons_self) m)

omit [Fintype P] in
/-- The sources of the stack preparation: `m` copies of every effect vector, the latest
first. -/
theorem sources_prepStack :
    (prepStack m es T).sources =
      es.flatMap fun e ↦ List.replicate m (pairSourceOf e.distinct e.vector) := by
  induction es generalizing T with
  | nil => rfl
  | cons e es ih =>
      rw [List.flatMap_cons, ← ih T,
        ← Word.sources_prepWord e.distinct e.vector (stackApp m es T) m]
      rfl

/-- **The stacks are prepared by pair sources**: read along `stackAppEquiv`, `prepStack`
prepares the ideal content `stackIdxVector` of the stacks behind the input. -/
theorem op_prepStack :
    (prepStack m es T).op =
      reindex (stackAppEquiv m es T).symm (Equiv.refl _)
        (prepMatrix (Equiv.prodComm (Config T) _) (stackIdxVector m es)) := by
  induction es generalizing T with
  | nil =>
    ext y x
    change (1 : Matrix (Config T) (Config T) ℂ) y x = _
    simp only [one_apply]
    simp [stackAppEquiv, stackIdxVector]
  | cons e es ih =>
    change Word.op ((prepStack m es T).comp
      (Word.prepWord e.distinct e.vector m (stackApp m es T))) = _
    rw [Word.op_comp, Word.op_prepWord, ih]
    ext y x
    simp only [prepMatrix_mul_apply, reindex_apply, submatrix_apply, Equiv.symm_symm,
      Equiv.refl_symm, Equiv.coe_refl, id, prepMatrix_apply, Equiv.prodComm_apply, Prod.fst_swap,
      Prod.snd_swap, stackAppEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
      Equiv.refl_apply, Equiv.prodLeftComm_apply, stackIdxVector, vecKron]
    split_ifs with h <;> simp [h]

variable {S : P → Type} [∀ s, Fintype (S s)] [∀ s, DecidableEq (S s)]

omit [Fintype P] in
/-- A word beside all stacks is allowed when the word is. -/
theorem isAllowed_frameStack {w : Word S T} (hw : w.IsAllowed) :
    (frameStack m es w).IsAllowed := by
  induction es with
  | nil => exact hw
  | cons e es ih => exact Word.isAllowed_framePairs _ _ _ m ih

omit [Fintype P] in
/-- A word beside all stacks has the sources of the word. -/
@[simp] theorem sources_frameStack (w : Word S T) : (frameStack m es w).sources = w.sources := by
  induction es with
  | nil => rfl
  | cons e es ih => exact (Word.sources_framePairs _ _ _ m _).trans ih

/-- **The stacks pass words on the other registers**: read along `stackAppEquiv`, a word beside
the stacks acts as the operator of the word tensored with the identity on the stacks. -/
theorem op_frameStack (w : Word S T) :
    (frameStack m es w).op =
      reindex (stackAppEquiv m es T).symm (stackAppEquiv m es S).symm
        (w.op ⊗ₖ (1 : Matrix (stackIdx m es) (stackIdx m es) ℂ)) := by
  induction es with
  | nil =>
    ext y x
    change w.op y x = _
    simp [stackAppEquiv, kroneckerMap_apply]
  | cons e es ih =>
    change (Word.framePairs e.distinct e.leftBasis e.rightBasis m (frameStack m es w)).op = _
    rw [Word.op_framePairs, ih]
    ext y x
    simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
      stackAppEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      Equiv.prodLeftComm_apply, one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all

omit [Fintype P] [∀ s, Fintype (T s)] [∀ s, DecidableEq (T s)] in
/-- **Ownership of the stacks**: at a party that is no endpoint of an effect of `es`, the
stacked system has the basis of `T`. Source: Lemma 5.1, `04-compression.tex`, lines 67–68 and
100–103. -/
theorem stackApp_of_forall_ne {s : P} (h : ∀ e ∈ es, s ≠ e.left ∧ s ≠ e.right) :
    stackApp m es T s = T s := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      obtain ⟨h1, h2⟩ := h e List.mem_cons_self
      exact (stackSys_of_ne e.distinct _ _ _ _ h1 h2).trans
        (ih fun e' he' ↦ h e' (List.mem_cons_of_mem _ he'))

omit [Fintype P] [∀ s, DecidableEq (T s)] in
/-- **Dimensions of the stacks**: the dimension at a party `s` is multiplied by `|α|^m` for
every effect with first endpoint `s` and by `|β|^m` for every effect with second endpoint `s`.
Source: Lemma 5.1, `04-compression.tex`, lines 100–103. -/
theorem card_stackApp (s : P) :
    Fintype.card (stackApp m es T s) = Fintype.card (T s) *
      (es.map fun e ↦ (if s = e.left then Fintype.card e.leftBasis ^ m else 1) *
        (if s = e.right then Fintype.card e.rightBasis ^ m else 1)).prod := by
  induction es with
  | nil => simp [stackApp]
  | cons e es ih =>
    change Fintype.card (addPair (stackApp m es T) e.distinct (Fin m → e.leftBasis)
      (Fin m → e.rightBasis) s) = _
    rw [card_addPair, card_pairFactor, ih, List.map_cons, List.prod_cons]
    simp only [Fintype.card_fun, Fintype.card_fin]
    ring

end Stacks

end QuantumCircuit.Party
