/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Frame
import QICLean.Analysis.TensorProduct.CyclicInsertionMatrix
import QICLean.Algebra.Combinatorics.TupleEquiv

/-!
# Stacks of pair registers and the insertion words

In the elimination of normalized pair effects (Lemma 5.1 `lem:effects`), each effect occurrence
on the parties `p ≠ q` with pair basis `α × β` receives a stack of `m` pair registers: `m`
registers `ℂ^α` of `p` and `m` registers `ℂ^β` of `q`. On basis types the stack of `p` is the
single fresh factor `Fin m → α` in front of the basis of `p`, and that of `q` is `Fin m → β` in
front of the basis of `q`: the system `stackSys hpq α β m T = addPair T hpq (Fin m → α)
(Fin m → β)`. Its configurations are a stack configuration `Fin m → α × β` and a configuration
of `T` (`stackConfigEquiv`), read through `Equiv.arrowProdEquivProdArrow`.

* `Word.prepWord hpq η n T` prepares `n` copies of the pair vector `η` by `n` pair sources; its
  operator prepares `η^{⊗ n}` (`Word.op_prepWord`).
* `Word.insWord g m k`, for a pair effect `g` with vector `η`, keeps the pair register removed by
  `g` as position `k` of a stack of `m` registers and prepares `η` in the other `m - 1`
  positions; its operator is the insertion `I_k` (`Word.op_insWord`). Following the source, each
  term of the permutation average is a normalized source preparation followed by a permutation
  of the pair registers; the permutation is one relabelling of the bases of `p` and `q`
  (`PartyCircuit.relabel`), a local operation.
* `PartyCircuit.liftPair` runs a circuit beside fresh front factors at two parties, through
  `PartyCircuit.frame`; `Word.framePairs` runs a word beside a stack (`Word.op_framePairs`).

The operators of one pair source and of one pair effect are the preparation `Matrix.prepMatrix`
and the effect `Matrix.effectMatrix` of their vectors (`SourceGate.op_gate`,
`PairEffectGate.op_gate_eq_effectMatrix`); an insertion is a preparation followed by a
relabelling (`CyclicInsertion.insertAtMatrix_eq_insertNth`).

## Main definitions

* `QuantumCircuit.Party.stackSys`, `QuantumCircuit.Party.stackConfigEquiv` — a stack of pair
  registers.
* `QuantumCircuit.Party.PartyCircuit.liftPair`, `QuantumCircuit.Party.Word.framePairs` — beside
  a stack.
* `QuantumCircuit.Party.Word.prepWord`, `QuantumCircuit.Party.Word.insWord`.

## Main results

* `QuantumCircuit.Party.Word.op_prepWord` — the prepared stack is `η^{⊗ n}`.
* `QuantumCircuit.Party.Word.op_insWord` — the insertion word is the insertion `I_k`.
* `QuantumCircuit.Party.Word.op_framePairs` — a stack passes words on the other registers.
* `QuantumCircuit.Party.Word.op_liftPair_mul_op_sourceAt` — a fresh pair source passes a word
  run beside its factors.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 75–79 and 96–106 (stacks and insertions); lines 17–19 and 23–24
  (finite-dimensional registers, memory a tensor product of the parties' spaces).
-/

noncomputable section

open Matrix ManyBody EuclideanSpace CyclicInsertion
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ### Party circuits beside fresh front factors at two parties -/

namespace PartyCircuit

variable {G : Finset P → (P → Type) → (P → Type) → Type 1} [GateFamily G] [GateFrame G]

/-- The circuit `c` beside the fresh front factors `A` at `p` and `B` at `q`: the bases of
`addPair S` read as products with the factors `pairFactor`, the circuit framed by these factors,
and the bases read back. -/
def liftPair {p q : P} (hpq : p ≠ q) (A B : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] {S T : P → Type} [∀ s, Fintype (S s)] [∀ s, DecidableEq (S s)]
    [∀ s, Fintype (T s)] [∀ s, DecidableEq (T s)] (c : PartyCircuit G S T) :
    PartyCircuit G (addPair S hpq A B) (addPair T hpq A B) :=
  (relabel fun s ↦ (addPairSiteEquiv hpq A B S s).symm).comp
    ((c.frame (pairFactor hpq A B)).comp (relabel (addPairSiteEquiv hpq A B T)))

section Lift

variable {p q : P} (hpq : p ≠ q) (A B : Type) [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {S T : P → Type} [∀ s, Fintype (S s)] [∀ s, DecidableEq (S s)]
  [∀ s, Fintype (T s)] [∀ s, DecidableEq (T s)]

/-- **A lifted circuit acts as `1 ⊗ op`**: read along `addPairConfigEquiv`, the operator of
`c` beside the fresh factors is the identity on the fresh factors tensored with the operator
of `c`. -/
theorem op_liftPair [GateFamily.UniqueOutcome G] (ev : Interpretation G)
    (hev : GateFrame.IsCompatible G ev) (c : PartyCircuit G S T) :
    (c.liftPair hpq A B).op ev =
      reindex (addPairConfigEquiv (X := T) hpq A B).symm
        (addPairConfigEquiv (X := S) hpq A B).symm
        ((1 : Matrix (A × B) (A × B) ℂ) ⊗ₖ c.op ev) := by
  rw [liftPair, op_comp, op_comp, op_relabel_mul, op_relabel, PEquiv.mul_toMatrix_toPEquiv,
    op_frame _ ev hev, addPairConfigEquiv_eq_siteEquiv, addPairConfigEquiv_eq_siteEquiv]
  ext y x
  simp [kroneckerMap_apply, one_apply]

omit [Fintype P] in
/-- The circuit beside fresh factors of an allowed circuit is allowed when the condition on
gates passes to framed gates. -/
theorem isAllowed_liftPair [GateFamily.UniqueOutcome G] (ev : Interpretation G)
    (hev : GateFrame.IsCompatible G ev)
    {Ad : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)], G D X Y → Prop}
    (hA : ∀ ⦃D : Finset P⦄ ⦃X Y : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (W : P → Type) [∀ p, Fintype (W p)]
      [∀ p, DecidableEq (W p)] (g : G D X Y), Ad g → Ad (GateFrame.frame W g))
    {c : PartyCircuit G S T} (hc : c.IsAllowed ev Ad) :
    (c.liftPair hpq A B).IsAllowed ev Ad :=
  ⟨isAllowed_relabel ev _, isAllowed_frame _ ev hev
    (fun _ _ _ _ _ _ _ g hg ↦ hA (pairFactor hpq A B) g hg) hc,
    isAllowed_relabel ev _⟩

omit [Fintype P] in
/-- Running a circuit beside fresh factors keeps the cells of its gates. -/
@[simp] theorem gateCells_liftPair (c : PartyCircuit G S T) :
    (c.liftPair hpq A B).gateCells = c.gateCells := by
  simp [liftPair, gateCells]

omit [Fintype P] in
/-- Running a circuit beside fresh factors keeps its gate count. -/
@[simp] theorem gateCount_liftPair (c : PartyCircuit G S T) :
    (c.liftPair hpq A B).gateCount = c.gateCount := by
  simp [liftPair, gateCount]

end Lift

end PartyCircuit

/-! ### Stacks of pair registers -/

section Stack

variable {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

/-- The system `T` with a stack of `n` pair registers on the parties `p` and `q`: the fresh
factor `Fin n → α` in front of the basis of `p` and `Fin n → β` in front of that of `q`.
Source: `04-compression.tex`, lines 75–79 and 100–103. -/
abbrev stackSys (n : ℕ) (T : P → Type) : P → Type :=
  addPair T hpq (Fin n → α) (Fin n → β)

omit [Fintype P] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- **Ownership of a stack**: outside its two endpoints a stack changes no basis. -/
theorem stackSys_of_ne (n : ℕ) (T : P → Type) {s : P} (hp : s ≠ p) (hq : s ≠ q) :
    stackSys hpq α β n T s = T s :=
  addPair_of_ne hpq _ _ hp hq

omit [Fintype P] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- The configurations of a stacked system: a stack configuration `Fin n → α × β` and a
configuration of `T`. -/
def stackConfigEquiv (n : ℕ) (T : P → Type) :
    Config (stackSys hpq α β n T) ≃ (Fin n → α × β) × Config T :=
  (addPairConfigEquiv (X := T) hpq (Fin n → α) (Fin n → β)).trans
    ((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ α) (fun _ ↦ β)).symm.prodCongr
      (Equiv.refl _))

variable {α β}

/-- The pair-source occurrence with endpoints `p` and `q`, fresh factors `α` and `β`, and
vector `η`. -/
def pairSourceOf (η : EuclideanSpace ℂ (α × β)) : PairSource P where
  left := p
  right := q
  distinct := hpq
  leftBasis := α
  rightBasis := β
  vector := η

omit [Fintype P] in
/-- The pair source preparing one more copy of `η` at position `0` of a stack of `n` pair
registers. -/
def stackSource (η : EuclideanSpace ℂ (α × β)) (n : ℕ) (T : P → Type) :
    SourceGate {p, q} (stackSys hpq α β n T) (stackSys hpq α β (n + 1) T) where
  toPairSource := pairSourceOf hpq η
  cell_eq := rfl
  leftEquiv := (addPairLeft hpq _ _).trans
    (((Fin.consEquiv fun _ : Fin (n + 1) ↦ α).symm.prodCongr (Equiv.refl _)).trans
      ((Equiv.prodAssoc _ _ _).trans ((Equiv.refl α).prodCongr (addPairLeft hpq _ _).symm)))
  rightEquiv := (addPairRight hpq _ _).trans
    (((Fin.consEquiv fun _ : Fin (n + 1) ↦ β).symm.prodCongr (Equiv.refl _)).trans
      ((Equiv.prodAssoc _ _ _).trans ((Equiv.refl β).prodCongr (addPairRight hpq _ _).symm)))
  outside s hs := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    rw [stackSys_of_ne hpq α β _ T hs.1 hs.2, stackSys_of_ne hpq α β _ T hs.1 hs.2]

omit [Fintype P] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- At every party, the basis of the system with the empty stack is the basis of the system
itself. -/
def stackZeroEquiv (T : P → Type) (s : P) : stackSys hpq α β 0 T s ≃ T s :=
  letI := pairFactor.unique hpq (Fin 0 → α) (Fin 0 → β) s
  (addPairSiteEquiv hpq _ _ T s).trans (Equiv.uniqueProd (T s) _)

end Stack

namespace Word

section Stack

variable {p q : P} (hpq : p ≠ q) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] (η : EuclideanSpace ℂ (α × β))

/-- Preparation of `n` copies of the pair vector `η` as `n` pair sources on `p` and `q`, the
latest at position `0`; the empty stack is a relabelling. Source: `04-compression.tex`,
lines 75–76 and 105–106. -/
def prepWord : (n : ℕ) → (T : P → Type) → [∀ s, Fintype (T s)] → [∀ s, DecidableEq (T s)] →
    Word T (stackSys hpq α β n T)
  | 0, T, _, _ => PartyCircuit.relabel (stackZeroEquiv hpq T)
  | n + 1, T, _, _ => (prepWord n T).comp (source (stackSource hpq η n T))

variable (T : P → Type) [∀ s, Fintype (T s)] [∀ s, DecidableEq (T s)]

omit [Fintype P] in
/-- The preparation of copies of a normalized pair vector is allowed. -/
theorem isAllowed_prepWord (hη : ‖η‖ = 1) : (n : ℕ) → (prepWord hpq η n T).IsAllowed
  | 0 => PartyCircuit.isAllowed_relabel _ _
  | n + 1 => IsAllowed.comp (isAllowed_prepWord hη n) (isAllowed_source _ hη)

omit [Fintype P] in
/-- The sources of `prepWord` are `n` copies of `(p, q, η)`. -/
theorem sources_prepWord (n : ℕ) :
    (prepWord hpq η n T).sources = List.replicate n (pairSourceOf hpq η) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [prepWord, sources_comp, sources_source, ih, List.replicate_succ]
      rfl

omit [Fintype P] in
/-- The preparation of `n` copies has `n` sources. -/
theorem sourceCount_prepWord (n : ℕ) : (prepWord hpq η n T).sourceCount = n := by
  rw [sourceCount, sources_prepWord, List.length_replicate]

omit [Fintype P] in
/-- The preparation of a stack on `(p, q)` uses only `p` and `q`. -/
theorem usesOnly_prepWord (n : ℕ) : (prepWord hpq η n T).UsesOnly {p, q} := by
  induction n with
  | zero =>
    refine usesOnly_relabel _ fun s hs ↦ ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
    refine ⟨stackSys_of_ne hpq α β 0 T hs.1 hs.2, fun y ↦ ?_⟩
    simp [stackZeroEquiv, addPairSiteEquiv, hs.1, hs.2]
  | succ n ih =>
    refine ⟨ih, fun x hx ↦ ?_⟩
    simpa using hx

/-- **The prepared stack is `η^{⊗ n}`**: read along `stackConfigEquiv`, `prepWord` prepares
`η^{⊗ n}` in front of the input. -/
theorem op_prepWord (n : ℕ) :
    (prepWord hpq η n T).op =
      prepMatrix (stackConfigEquiv hpq α β n T) (tensorPower (Fin n) η) := by
  induction n with
  | zero =>
    have h : ∀ y, (stackConfigEquiv hpq α β 0 T y).2 =
        Equiv.piCongrRight (stackZeroEquiv hpq T) y := fun y ↦ by
      funext s
      simp [stackConfigEquiv, addPairConfigEquiv_eq_siteEquiv, stackZeroEquiv]
    change (PartyCircuit.relabel (G := SourceGate) (stackZeroEquiv hpq T)).op SourceGate.ev = _
    rw [PartyCircuit.op_relabel]
    ext y x
    simp [PEquiv.toMatrix_apply, h, tensorPower]
  | succ n ih =>
    change Word.op ((prepWord hpq η n T).comp (source (stackSource hpq η n T))) = _
    rw [Word.op_comp, op_source, ih]
    ext y x
    set g := stackSource hpq η n T
    have h1 : (g.configEquiv y).1 =
        ((addPairLeft hpq _ _ (y p)).1 0, (addPairRight hpq _ _ (y q)).1 0) :=
      SourceGate.configEquiv_apply_fst g y
    have h2 : (g.configEquiv y).2 p = (addPairLeft hpq _ _).symm
        (Fin.tail (addPairLeft hpq _ _ (y p)).1, (addPairLeft hpq _ _ (y p)).2) :=
      SourceGate.configEquiv_apply_snd_left g y
    have h3 : (g.configEquiv y).2 q = (addPairRight hpq _ _).symm
        (Fin.tail (addPairRight hpq _ _ (y q)).1, (addPairRight hpq _ _ (y q)).2) :=
      SourceGate.configEquiv_apply_snd_right g y
    have h4 : ∀ s (hs : s ∉ ({p, q} : Finset P)), (g.configEquiv y).2 s =
        cast (g.outside s hs) (y s) := fun s hs ↦
      SourceGate.configEquiv_apply_snd_of_notMem g y hs
    have h5 : (addPairConfigEquiv hpq (Fin n → α) (Fin n → β) (g.configEquiv y).2).2 =
        (addPairConfigEquiv hpq (Fin (n + 1) → α) (Fin (n + 1) → β) y).2 := by
      funext s
      by_cases hp : s = p
      · subst hp
        rw [addPairConfigEquiv_apply_snd_left, addPairConfigEquiv_apply_snd_left, h2,
          Equiv.apply_symm_apply]
      by_cases hq : s = q
      · subst hq
        rw [addPairConfigEquiv_apply_snd_right, addPairConfigEquiv_apply_snd_right, h3,
          Equiv.apply_symm_apply]
      rw [addPairConfigEquiv_apply_snd_of_ne _ _ _ _ hp hq,
        addPairConfigEquiv_apply_snd_of_ne _ _ _ _ hp hq, h4 s (by simp [hp, hq]), cast_cast]
    rw [prepMatrix_mul_apply, prepMatrix_apply, prepMatrix_apply]
    change η (g.configEquiv y).1 * (if (addPairConfigEquiv hpq _ _ (g.configEquiv y).2).2 = x
      then _ else 0) = if (addPairConfigEquiv hpq _ _ y).2 = x then _ else 0
    rw [h5, h1]
    split_ifs
    · simp only [stackConfigEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
        addPairConfigEquiv_apply_fst, tensorPower, piTensor_apply, Fin.prod_univ_succ, h2, h3,
        Equiv.apply_symm_apply]
      rfl
    · rw [mul_zero]

end Stack

section Insertion

variable {D : Finset P} {Z Y : P → Type} [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

omit [Fintype P] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
/-- The relabelling of the insertion: the pair removed by `g` goes to position `k` of the
stack, the `n` prepared copies to the other positions in order (`Fin.insertNthEquiv`). -/
def insEquiv (g : PairEffectGate D Z Y) (n : ℕ) (k : Fin (n + 1)) (s : P) :
    stackSys g.distinct g.leftBasis g.rightBasis (n + 1) Y s ≃
      stackSys g.distinct g.leftBasis g.rightBasis n Z s :=
  if hl : s = g.left then
    (Equiv.cast (by rw [hl])).trans <|
      (addPairLeft g.distinct _ _).trans <|
      ((Fin.insertNthEquiv (fun _ ↦ g.leftBasis) k).symm.prodCongr (Equiv.refl _)).trans <|
      (Equiv.prodAssoc _ _ _).trans <| (Equiv.prodLeftComm _ _ _).symm.trans <|
      ((Equiv.refl _).prodCongr g.leftEquiv.symm).trans <|
      (addPairLeft g.distinct _ _).symm.trans (Equiv.cast (by rw [hl]))
  else if hr : s = g.right then
    (Equiv.cast (by rw [hr])).trans <|
      (addPairRight g.distinct _ _).trans <|
      ((Fin.insertNthEquiv (fun _ ↦ g.rightBasis) k).symm.prodCongr (Equiv.refl _)).trans <|
      (Equiv.prodAssoc _ _ _).trans <| (Equiv.prodLeftComm _ _ _).symm.trans <|
      ((Equiv.refl _).prodCongr g.rightEquiv.symm).trans <|
      (addPairRight g.distinct _ _).symm.trans (Equiv.cast (by rw [hr]))
  else
    Equiv.cast (by
      rw [stackSys_of_ne _ _ _ _ _ hl hr, stackSys_of_ne _ _ _ _ _ hl hr,
        g.outside s (by rw [g.cell_eq]; simp [hl, hr])])

/-- **The insertion word**: the pair register removed by the pair effect `g`
becomes position `k` of a stack of `m` pair registers, the other `m - 1` positions holding pair
sources of the vector `η` of `g`. Source: `04-compression.tex`, lines 75–79 and 96–98 (each term
of the permutation average is a normalized source preparation followed by a permutation of the
pair registers). -/
def insWord (g : PairEffectGate D Z Y) :
    (m : ℕ) → Fin m → Word Z (stackSys g.distinct g.leftBasis g.rightBasis m Y)
  | 0, k => k.elim0
  | n + 1, k => (prepWord g.distinct g.vector n Z).comp (PartyCircuit.relabel (insEquiv g n k))

omit [Fintype P] in
/-- The insertion word of a normalized pair effect is allowed. -/
theorem isAllowed_insWord (g : PairEffectGate D Z Y) (hη : ‖g.vector‖ = 1) :
    (m : ℕ) → (k : Fin m) → (insWord g m k).IsAllowed
  | 0, k => k.elim0
  | n + 1, _ => IsAllowed.comp (isAllowed_prepWord _ _ _ hη n)
      (PartyCircuit.isAllowed_relabel _ _)

omit [Fintype P] in
/-- The insertion word has `m - 1` sources of the vector of `g`. -/
theorem sources_insWord (g : PairEffectGate D Z Y) :
    (m : ℕ) → (k : Fin m) →
      (insWord g m k).sources = List.replicate (m - 1) (pairSourceOf g.distinct g.vector)
  | 0, k => k.elim0
  | n + 1, _ => by
    rw [insWord, sources_comp, sources_relabel, sources_prepWord, List.nil_append]
    rfl

omit [Fintype P] in
/-- The insertion word of `g` uses only the endpoints of `g`. -/
theorem usesOnly_insWord (g : PairEffectGate D Z Y) (m : ℕ) (k : Fin m) :
    (insWord g m k).UsesOnly {g.left, g.right} := by
  cases m with
  | zero => exact k.elim0
  | succ n =>
    refine ⟨usesOnly_prepWord _ _ _ n, usesOnly_relabel _ fun s hs ↦ ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
    have hD : s ∉ D := by rw [g.cell_eq]; simp [hs.1, hs.2]
    refine ⟨by rw [stackSys_of_ne _ _ _ _ _ hs.1 hs.2, stackSys_of_ne _ _ _ _ _ hs.1 hs.2,
      g.outside s hD], fun y ↦ ?_⟩
    simp [insEquiv, hs.1, hs.2]

/-- **The insertion map as a source-only word**: read along the configuration equivalences of
the pair effect and of the stack, `insWord g m k` is the insertion `I_k ⊗ 1` of the vector of
`g` at position `k`. Source: `04-compression.tex`, lines 75–98. -/
theorem op_insWord (g : PairEffectGate D Z Y) (m : ℕ) (k : Fin m) :
    (insWord g m k).op =
      reindex (stackConfigEquiv g.distinct g.leftBasis g.rightBasis m Y).symm g.configEquiv.symm
        (insertAtMatrix g.vector k ⊗ₖ (1 : Matrix (Config Y) (Config Y) ℂ)) := by
  cases m with
  | zero => exact k.elim0
  | succ n =>
    change Word.op ((prepWord g.distinct g.vector n Z).comp
      (PartyCircuit.relabel (insEquiv g n k))) = _
    rw [Word.op_comp]
    change (PartyCircuit.relabel (G := SourceGate) (insEquiv g n k)).op SourceGate.ev *
      (prepWord g.distinct g.vector n Z).op = _
    rw [PartyCircuit.op_relabel_mul, op_prepWord, insertAtMatrix_eq_insertNth]
    ext y x
    set a := addPairLeft g.distinct (Fin (n + 1) → g.leftBasis) (Fin (n + 1) → g.rightBasis)
      (y g.left)
    set b := addPairRight g.distinct (Fin (n + 1) → g.leftBasis) (Fin (n + 1) → g.rightBasis)
      (y g.right)
    set y' := Equiv.piCongrRight (insEquiv g n k) y with hy'
    have hl : addPairLeft g.distinct (Fin n → g.leftBasis) (Fin n → g.rightBasis) (y' g.left) =
          (Fin.removeNth k a.1, g.leftEquiv.symm (a.1 k, a.2)) := by
      simp [y', insEquiv, a, Fin.insertNthEquiv]
    have hr : addPairRight g.distinct (Fin n → g.leftBasis) (Fin n → g.rightBasis)
        (y' g.right) =
          (Fin.removeNth k b.1, g.rightEquiv.symm (b.1 k, b.2)) := by
      simp [y', insEquiv, b, Fin.insertNthEquiv, g.distinct.symm]
    have ho : ∀ s (h₁ : s ≠ g.left) (h₂ : s ≠ g.right) (hs : s ∉ D),
        insEquiv g n k s (y s) = cast (by
          rw [stackSys_of_ne _ _ _ _ _ h₁ h₂, stackSys_of_ne _ _ _ _ _ h₁ h₂, g.outside s hs])
          (y s) := fun s h₁ h₂ _ ↦ by
      simp [insEquiv, h₁, h₂]
    have h1 : (stackConfigEquiv g.distinct _ _ n Z y').1 =
        Fin.removeNth k (stackConfigEquiv g.distinct _ _ (n + 1) Y y).1 := by
      funext j
      simp [stackConfigEquiv, hl, hr, Fin.removeNth, a, b]
    have h2 : g.configEquiv (stackConfigEquiv g.distinct _ _ n Z y').2 =
        ((stackConfigEquiv g.distinct _ _ (n + 1) Y y).1 k,
          (stackConfigEquiv g.distinct _ _ (n + 1) Y y).2) := by
      change g.toSourceGate.configEquiv _ = _
      refine Prod.ext ?_ (funext fun s ↦ ?_)
      · rw [SourceGate.configEquiv_apply_fst]
        simp only [stackConfigEquiv, PairEffectGate.toSourceGate,
          Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
          addPairConfigEquiv_apply_snd_left, addPairConfigEquiv_apply_snd_right, hl, hr]
        erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        rfl
      · by_cases hsl : s = g.left
        · subst hsl
          erw [SourceGate.configEquiv_apply_snd_left]
          change (g.leftEquiv ((addPairConfigEquiv g.distinct _ _ y').2 g.left)).2 = _
          rw [addPairConfigEquiv_apply_snd_left, hl]
          erw [Equiv.apply_symm_apply]
          exact (addPairConfigEquiv_apply_snd_left _ _ _ y).symm
        by_cases hsr : s = g.right
        · subst hsr
          erw [SourceGate.configEquiv_apply_snd_right]
          change (g.rightEquiv ((addPairConfigEquiv g.distinct _ _ y').2 g.right)).2 = _
          rw [addPairConfigEquiv_apply_snd_right, hr]
          erw [Equiv.apply_symm_apply]
          exact (addPairConfigEquiv_apply_snd_right _ _ _ y).symm
        have hs : s ∉ D := by rw [g.cell_eq]; simp [hsl, hsr]
        erw [SourceGate.configEquiv_apply_snd_of_notMem _ _ hs]
        simp only [stackConfigEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
          Equiv.refl_apply, addPairConfigEquiv_apply_snd_of_ne _ _ _ _ hsl hsr]
        rw [show y' s = _ from ho s hsl hsr hs, cast_cast, cast_cast]
    have key : (stackConfigEquiv g.distinct _ _ n Z y').2 = x ↔
        (stackConfigEquiv g.distinct _ _ (n + 1) Y y).1 k = (g.configEquiv x).1 ∧
          (stackConfigEquiv g.distinct _ _ (n + 1) Y y).2 = (g.configEquiv x).2 := by
      rw [← g.configEquiv.apply_eq_iff_eq, h2, Prod.ext_iff]
    simp only [submatrix_apply, prepMatrix_apply, reindex_apply, Equiv.symm_symm,
      kroneckerMap_apply, one_apply, id, Equiv.refl_symm, Equiv.coe_refl, Equiv.prodComm_apply,
      Prod.fst_swap, Prod.snd_swap, Fin.insertNthEquiv, Equiv.coe_fn_symm_mk]
    rw [← hy']
    by_cases hc : (stackConfigEquiv g.distinct _ _ n Z y').2 = x
    · obtain ⟨hc1, hc2⟩ := key.mp hc
      rw [ite_eq_left hc, h1]
      simp [hc1, hc2]
    · simp only [hc, ite_false]
      by_cases hc1 : (stackConfigEquiv g.distinct _ _ (n + 1) Y y).1 k = (g.configEquiv x).1
      · have hc2 : ¬ (stackConfigEquiv g.distinct _ _ (n + 1) Y y).2 = (g.configEquiv x).2 :=
          fun hc2 ↦ hc (key.mpr ⟨hc1, hc2⟩)
        simp [hc2]
      · simp [hc1]

end Insertion

section Frame

variable {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] {S T : P → Type} [∀ s, Fintype (S s)] [∀ s, DecidableEq (S s)]
  [∀ s, Fintype (T s)] [∀ s, DecidableEq (T s)]

/-- A word beside a stack of `n` pair registers on `p` and `q`. -/
def framePairs (n : ℕ) (w : Word S T) : Word (stackSys hpq α β n S) (stackSys hpq α β n T) :=
  w.liftPair hpq (Fin n → α) (Fin n → β)

omit [Fintype P] in
/-- A word beside a stack is allowed when the word is. -/
theorem isAllowed_framePairs (n : ℕ) {w : Word S T} (hw : w.IsAllowed) :
    (framePairs hpq α β n w).IsAllowed :=
  PartyCircuit.isAllowed_liftPair _ _ _ _ SourceGate.isCompatible_frame
    (fun _ _ _ _ _ _ _ _ _ _ _ hg ↦ hg) hw

omit [Fintype P] in
/-- A word beside a stack has the sources of the word. -/
@[simp] theorem sources_framePairs (n : ℕ) (w : Word S T) :
    (framePairs hpq α β n w).sources = w.sources := by
  rw [framePairs, PartyCircuit.liftPair, sources_comp, sources_comp, sources_relabel,
    sources_relabel, sources_frame, List.nil_append, List.append_nil]

omit [Fintype P] in
/-- A word beside a stack has the gate count of the word. -/
@[simp] theorem gateCount_framePairs (n : ℕ) (w : Word S T) :
    (framePairs hpq α β n w).gateCount = w.gateCount :=
  PartyCircuit.gateCount_liftPair _ _ _ w

/-- **A stack passes words on the other registers**: read along `stackConfigEquiv`, a word
beside a stack acts as the identity on the stack tensored with the operator of the word. -/
theorem op_framePairs (n : ℕ) (w : Word S T) :
    (framePairs hpq α β n w).op =
      reindex (stackConfigEquiv hpq α β n T).symm (stackConfigEquiv hpq α β n S).symm
        ((1 : Matrix (Fin n → α × β) (Fin n → α × β) ℂ) ⊗ₖ w.op) := by
  change (w.liftPair hpq (Fin n → α) (Fin n → β)).op SourceGate.ev = _
  rw [PartyCircuit.op_liftPair hpq _ _ SourceGate.ev SourceGate.isCompatible_frame]
  ext y x
  simp [stackConfigEquiv, kroneckerMap_apply, one_apply]

/-- **A fresh pair source commutes with a word beside the fresh factors**: the word `c` followed
by the source of `η` is the source followed by `c` run beside the fresh factors. Source:
`04-compression.tex`, lines 245–251. -/
theorem op_liftPair_mul_op_sourceAt {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (η : EuclideanSpace ℂ (α × β)) {S T : P → Type}
    [∀ s, Fintype (S s)] [∀ s, DecidableEq (S s)] [∀ s, Fintype (T s)] [∀ s, DecidableEq (T s)]
    (c : Word S T) :
    Word.op (PartyCircuit.liftPair hpq α β c) * (sourceAt hpq α β η S).op =
      (sourceAt hpq α β η T).op * c.op := by
  unfold Word.op
  rw [PartyCircuit.op_liftPair hpq α β _ SourceGate.isCompatible_frame]
  change _ * Word.op (sourceAt hpq α β η S) = Word.op (sourceAt hpq α β η T) * _
  rw [op_sourceAt, op_sourceAt]
  ext y x
  rw [prepMatrix_mul_apply]
  simp only [reindex_apply, Equiv.symm_symm, Matrix.mul_apply, submatrix_apply,
    kroneckerMap_apply, prepMatrix_apply, mul_ite, mul_zero, one_apply, ite_mul, one_mul,
    zero_mul]
  rw [← (addPairConfigEquiv hpq α β (X := S)).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact mul_comm _ _

end Frame

end Word

end QuantumCircuit.Party
