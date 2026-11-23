/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Gates
import QICLean.Circuit.Party.Syntax.Relabel
import QICLean.ManyBody.Sites.ProductVector

/-!
# Source-only words

A *word* is a party circuit whose gates are pair sources: local operations of single parties
and preparations of pair vectors on fresh factors of two distinct parties. An allowed word has
contractive local operations and normalized pair sources; an operator is *source-only* when it is
the operator of an allowed word. The *source list* of a word records its pair sources, those of
the later part first, and the parties a word uses are those of its sources and of its nontrivial
local operations.

The canonical pair source on `p ≠ q` prepares `η` on fresh factors in front of the bases of `p`
and `q`; read through `addPairConfigEquiv`, its operator is the preparation of `η` in front of
every configuration (`Word.op_sourceAt`), and any pair source is the canonical one followed by a
relabelling of the output (`Word.op_source_eq_op_relabel_mul`). The product vector `⊗_p φ_p` is
prepared from the system with one basis vector at every party by one local operation at every
party (`Word.prepareProduct`). A word is a monomial with no pair effect (`Word.toChain`).

The sources of the monomials of a gate (`Monomial.sources`) and their pair effects
(`Monomial.effects`) are read off their gates in the same way.

## Main definitions

* `QuantumCircuit.Party.Word`, `QuantumCircuit.Party.Word.IsAllowed`,
  `QuantumCircuit.Party.IsSourceOnly`.
* `QuantumCircuit.Party.Word.source`, `QuantumCircuit.Party.Word.sourceAt`,
  `QuantumCircuit.Party.Word.localPrepare`, `QuantumCircuit.Party.Word.prepareProduct`.
* `QuantumCircuit.Party.Word.sources`, `QuantumCircuit.Party.Word.sourceCount`,
  `QuantumCircuit.Party.Word.UsesOnly`, `QuantumCircuit.Party.Word.toChain`.
* `QuantumCircuit.Party.Monomial.sources`, `QuantumCircuit.Party.Monomial.effects`,
  `QuantumCircuit.Party.Monomial.effectParties`, `QuantumCircuit.Party.Monomial.effectCount`,
  `QuantumCircuit.Party.Monomial.sourceCount`.

## Main results

* `QuantumCircuit.Party.Word.op_source`, `QuantumCircuit.Party.Word.op_sourceAt`,
  `QuantumCircuit.Party.Word.op_localPrepare`,
  `QuantumCircuit.Party.Word.op_prepareProduct_mulVec` — operators.
* `QuantumCircuit.Party.Word.gateCount_eq_sourceCount`,
  `QuantumCircuit.Party.Word.isNormalized_sources` — source lists.
* `QuantumCircuit.Party.Word.UsesOnly.mem_sources` — a word using a set of parties has its
  sources there.
* `QuantumCircuit.Party.Word.op_toChain` — a word read as a monomial.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35 (allowed
  monomials without pair effects), 53–70 (Lemma 5.1, source-only expansions and sources).
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-- A word: a party circuit whose gates are pair sources. Source: `04-compression.tex`,
lines 32–35. -/
abbrev Word (X Y : P → Type) := PartyCircuit (SourceGate (P := P)) X Y

namespace Word

variable {X Y Z : P → Type}

/-- A word is allowed when its local operations are contractions and its pair sources are
normalized. Source: `04-compression.tex`, lines 32–35. -/
def IsAllowed [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (w : Word X Y) : Prop :=
  PartyCircuit.IsAllowed SourceGate.ev (fun _ _ _ _ _ _ _ g ↦ g.IsAllowed) w

/-- The operator of a word. -/
noncomputable abbrev op [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (w : Word X Y) : Matrix (Config Y) (Config X) ℂ :=
  PartyCircuit.op SourceGate.ev w

section Basic

variable [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The operator of a composition of words is the product of the operators. -/
@[simp] theorem op_comp [Fintype P] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (w : Word X Y) (w' : Word Y Z) : Word.op (PartyCircuit.comp w w') = w'.op * w.op :=
  PartyCircuit.op_comp _ w w'

/-- The empty word is allowed. -/
theorem isAllowed_done : Word.IsAllowed (PartyCircuit.done X : Word X X) :=
  trivial

/-- A composition of allowed words is allowed. -/
theorem IsAllowed.comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] {w : Word X Y}
    {w' : Word Y Z} (hw : w.IsAllowed) (hw' : w'.IsAllowed) :
    Word.IsAllowed (PartyCircuit.comp w w') :=
  ⟨hw, hw'⟩

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- A contractive local operation is allowed. -/
theorem isAllowed_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s) (U : Matrix (Y p) (X p) ℂ)
    (hU : ‖U‖ ≤ 1) : Word.IsAllowed (PartyCircuit.localOp (G := SourceGate) p hY U) :=
  hU

/-- Contractive local operations at every party are allowed. -/
theorem isAllowed_localOps (U : ∀ p, Matrix (Y p) (X p) ℂ) (hU : ∀ p, ‖U p‖ ≤ 1) :
    Word.IsAllowed (PartyCircuit.localOps (G := SourceGate) U) :=
  hU

end Basic

section Constructors

variable [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The word of one pair source. -/
def source {D : Finset P} (g : SourceGate D X Y) : Word X Y :=
  PartyCircuit.gate D g.outside g

/-- The canonical pair source: `η` on fresh factors in front of the bases of `p` and `q`. -/
def sourceAt {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (η : EuclideanSpace ℂ (α × β)) (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] : Word X (addPair X hpq α β) :=
  source (SourceGate.ofAddPair hpq α β η X)

/-- A local preparation: the vector `x` prepared at the party `p` on a fresh factor, located in
the new basis of `p` by `e`. With `α` a product `α₁ × α₂`, it prepares a pair vector at one
party. -/
def localPrepare {α : Type} (p : P) (hY : ∀ s ≠ p, Y s = X s) (x : EuclideanSpace ℂ α)
    (e : Y p ≃ α × X p) : Word X Y :=
  PartyCircuit.localOp p hY (prepMatrix e x)

variable [∀ p, Fintype (X p)]

variable [Fintype P] in
/-- The operator of one pair source is the preparation of its vector, the output read through
`SourceGate.configEquiv`. -/
theorem op_source {D : Finset P} (g : SourceGate D X Y) :
    (source g).op = prepMatrix g.configEquiv g.vector :=
  g.op_gate

/-- One pair source with a normalized vector is allowed. -/
theorem isAllowed_source {D : Finset P} (g : SourceGate D X Y) (hg : ‖g.vector‖ = 1) :
    (source g).IsAllowed :=
  ⟨(g.norm_ev_le ()).trans hg.le, hg⟩

variable [Fintype P] in
/-- The operator of a local preparation is the placement of the preparation at the party. -/
theorem op_localPrepare {α : Type} (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (x : EuclideanSpace ℂ α) (e : Y p ≃ α × X p) :
    (localPrepare p hY x e).op =
      placeBetween {p} (fun s hs ↦ hY s (Finset.notMem_singleton.mp hs))
        ((prepMatrix e x).submatrix (fun y ↦ y ⟨p, Finset.mem_singleton_self p⟩)
          (fun x ↦ x ⟨p, Finset.mem_singleton_self p⟩)) :=
  PartyCircuit.op_localOp _ p hY _

/-- A local preparation of a unit vector is allowed. -/
theorem isAllowed_localPrepare {α : Type} [Fintype α] (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (x : EuclideanSpace ℂ α) (e : Y p ≃ α × X p) (hx : ‖x‖ = 1) :
    (localPrepare p hY x e).IsAllowed :=
  (norm_prepMatrix_le e x).trans hx.le

end Constructors

/-- The canonical pair source prepares `η` in front of every configuration: read through
`addPairConfigEquiv`, its operator maps `|x⟩` to `η ⊗ |x⟩`. -/
theorem op_sourceAt [Fintype P] {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (η : EuclideanSpace ℂ (α × β)) (X : P → Type)
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] :
    (sourceAt hpq α β η X).op = prepMatrix (addPairConfigEquiv hpq α β) η := by
  rw [sourceAt, op_source, SourceGate.configEquiv_ofAddPair]
  rfl

/-- **Every pair source is the canonical one followed by a relabelling** of the output bases
along `SourceGate.toAddPair`. -/
theorem op_source_eq_op_relabel_mul [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] {D : Finset P} (g : SourceGate D X Y) :
    (source g).op = (PartyCircuit.relabel (G := SourceGate) g.toAddPair).op SourceGate.ev *
      (sourceAt g.distinct g.leftBasis g.rightBasis g.vector X).op := by
  rw [PartyCircuit.op_relabel_mul, op_sourceAt, op_source]
  rfl

/-! ### Source lists -/

/-- The pair sources of a word, those of the later part first. Source: `04-compression.tex`,
lines 68–70. -/
def sources : {X Y : P → Type} → Word X Y → SourceInventory P
  | _, _, PartyCircuit.done _ => []
  | _, _, PartyCircuit.gate _ _ g => [g.toPairSource]
  | _, _, PartyCircuit.localOp _ _ _ => []
  | _, _, PartyCircuit.localOps _ => []
  | _, _, PartyCircuit.comp w w' => sources w' ++ sources w

/-- The number of pair sources of a word. -/
abbrev sourceCount (w : Word X Y) : ℕ := w.sources.length

/-- The sources of a composition: those of the later word first. -/
@[simp] theorem sources_comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (w : Word X Y)
    (w' : Word Y Z) : Word.sources (PartyCircuit.comp w w') = w'.sources ++ w.sources :=
  rfl

/-- The source list of one pair source. -/
@[simp] theorem sources_source [∀ p, Fintype (Y p)]
    [∀ p, DecidableEq (Y p)] {D : Finset P} (g : SourceGate D X Y) :
    (source g).sources = [g.toPairSource] :=
  rfl

/-- Every gate of a word is a pair source, so the number of gates of a word is its number of
sources. -/
theorem numGates_eq_sourceCount : {X Y : P → Type} → (w : Word X Y) →
    w.numGates = w.sourceCount
  | _, _, PartyCircuit.done _ => rfl
  | _, _, PartyCircuit.gate _ _ _ => rfl
  | _, _, PartyCircuit.localOp _ _ _ => rfl
  | _, _, PartyCircuit.localOps _ => rfl
  | _, _, PartyCircuit.comp w w' => by
    change w.numGates + w'.numGates = (sources w' ++ sources w).length
    rw [numGates_eq_sourceCount w, numGates_eq_sourceCount w', List.length_append, Nat.add_comm]

/-- No pair source acts on exactly one party. -/
theorem forallGate_card_ne_one : {X Y : P → Type} → (w : Word X Y) →
    w.ForallGate fun D _ _ _ ↦ D.card ≠ 1
  | _, _, PartyCircuit.done _ => trivial
  | _, _, PartyCircuit.gate _ _ g => by
    change _ ≠ 1
    rw [g.cell_eq, Finset.card_pair g.distinct]
    omega
  | _, _, PartyCircuit.localOp _ _ _ => trivial
  | _, _, PartyCircuit.localOps _ => trivial
  | _, _, PartyCircuit.comp w w' => ⟨forallGate_card_ne_one w, forallGate_card_ne_one w'⟩

/-- The gate count of a word is its number of sources. -/
theorem gateCount_eq_sourceCount (w : Word X Y) : w.gateCount = w.sourceCount :=
  (PartyCircuit.gateCount_eq_numGates w (forallGate_card_ne_one w)).trans
    (numGates_eq_sourceCount w)

/-- The sources of an allowed word are normalized. -/
theorem isNormalized_sources : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → w.IsAllowed → w.sources.IsNormalized
  | _, _, _, _, PartyCircuit.done _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | _, _, _, _, PartyCircuit.gate _ _ _, hw => fun _ h ↦ (List.mem_singleton.mp h) ▸ hw.2
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | _, _, _, _, PartyCircuit.localOps _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | _, _, _, _, PartyCircuit.comp w w', hw => fun s h ↦ (List.mem_append.mp h).elim
      (isNormalized_sources w' hw.2 s) (isNormalized_sources w hw.1 s)

/-! ### Words using a set of parties -/

open Classical in
/-- A word uses only the parties of `R`: its sources join parties of `R`, its local operations
act at parties of `R`, and its local operations at every party are the identity outside `R`.
Source: `04-compression.tex`, lines 32–35. -/
def UsesOnly (R : Set P) : {X Y : P → Type} → Word X Y → Prop
  | _, _, PartyCircuit.done _ => True
  | _, _, PartyCircuit.gate D _ _ => (D : Set P) ⊆ R
  | _, _, PartyCircuit.localOp p _ _ => p ∈ R
  | X, Y, PartyCircuit.localOps A =>
    ∀ p ∉ R, ∃ h : Y p = X p, ∀ y x, A p y x = if cast h y = x then 1 else 0
  | _, _, PartyCircuit.comp w w' => UsesOnly R w ∧ UsesOnly R w'

/-- A word using only the parties of `R` uses only those of a larger set. -/
theorem UsesOnly.mono {R R' : Set P} (h : R ⊆ R') : {X Y : P → Type} → {w : Word X Y} →
    w.UsesOnly R → w.UsesOnly R'
  | _, _, PartyCircuit.done _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, hw => hw.trans h
  | _, _, PartyCircuit.localOp _ _ _, hw => h hw
  | _, _, PartyCircuit.localOps _, hw => fun p hp ↦ hw p fun hR ↦ hp (h hR)
  | _, _, PartyCircuit.comp _ _, hw => ⟨UsesOnly.mono h hw.1, UsesOnly.mono h hw.2⟩

/-- Every source of a word using only the parties of `R` joins two parties of `R`. -/
theorem UsesOnly.mem_sources {R : Set P} : {X Y : P → Type} → {w : Word X Y} →
    w.UsesOnly R → ∀ s ∈ w.sources, s.left ∈ R ∧ s.right ∈ R
  | _, _, PartyCircuit.done _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | _, _, PartyCircuit.gate _ _ g, hw => fun _ h ↦
    (List.mem_singleton.mp h) ▸ ⟨hw g.left_mem, hw g.right_mem⟩
  | _, _, PartyCircuit.localOp _ _ _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | _, _, PartyCircuit.localOps _, _ => fun _ h ↦ absurd h List.not_mem_nil
  | _, _, PartyCircuit.comp _ _, hw => fun s h ↦ (List.mem_append.mp h).elim
      (UsesOnly.mem_sources hw.2 s) (UsesOnly.mem_sources hw.1 s)

/-! ### Product preparations -/

section Product

variable [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The preparation of the product vector `⊗_p φ_p` from the system with one basis vector at
every party, by one local operation at every party. -/
def prepareProduct (φ : ∀ p, EuclideanSpace ℂ (X p)) : Word (fun _ ↦ Unit) X :=
  PartyCircuit.localOps fun p ↦ Matrix.of fun x _ ↦ φ p x

/-- The prepared vector is the product vector. -/
theorem op_prepareProduct_mulVec [Fintype P] (φ : ∀ p, EuclideanSpace ℂ (X p)) :
    (prepareProduct φ).op *ᵥ (fun _ ↦ 1) = productVector fun p x ↦ φ p x := by
  rw [op, prepareProduct, PartyCircuit.op_localOps]
  funext y
  simp [mulVec, dotProduct, productVector]

/-- The preparation of a product of unit vectors is allowed. -/
theorem isAllowed_prepareProduct (φ : ∀ p, EuclideanSpace ℂ (X p)) (hφ : ∀ p, ‖φ p‖ = 1) :
    (prepareProduct φ).IsAllowed := by
  intro p
  change ‖(Matrix.of fun x (_ : Unit) ↦ φ p x)‖ ≤ 1
  have h : (Matrix.of fun x (_ : Unit) ↦ φ p x) =
      prepMatrix (Equiv.prodPUnit (X p)).symm (φ p) := by
    ext y x
    simp
  rw [h]
  exact (norm_prepMatrix_le _ _).trans (hφ p).le

/-- A product preparation has no source. -/
@[simp] theorem sources_prepareProduct (φ : ∀ p, EuclideanSpace ℂ (X p)) :
    (prepareProduct φ).sources = [] :=
  rfl

end Product

/-! ### Words as monomials -/

/-- A word as a party circuit whose gates are pair sources among the gates of monomials. -/
def toChain (w : Word X Y) : PartyCircuit (ChainGate (P := P)) X Y :=
  w.mapGates (GateMorphism.inl (G₂ := PairEffectGate))

omit [DecidableEq P] in
/-- The inclusion of pair sources among the gates of monomials keeps the matrices. -/
private theorem isCompatible_inl [DecidableEq P] :
    (GateMorphism.inl (G₁ := SourceGate (P := P)) (G₂ := PairEffectGate)).IsCompatible
      SourceGate.ev chainEv :=
  GateMorphism.isCompatible_inl _ _

/-- A word read as a monomial has the operator of the word. -/
theorem op_toChain [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (w : Word X Y) :
    w.toChain.op chainEv = w.op :=
  PartyCircuit.op_mapGates _ isCompatible_inl w

/-- An allowed word read as a monomial is allowed. -/
theorem IsAllowed.toChain [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] {w : Word X Y}
    (hw : w.IsAllowed) : w.toChain.IsAllowed chainEv ChainGate.IsAllowed :=
  PartyCircuit.IsAllowed.mapGates _ isCompatible_inl
    (A := fun _ _ _ _ _ _ _ g ↦ g.IsAllowed) (fun _ _ _ _ _ _ _ _ h ↦ h) hw

/-- The gates of a word read as a monomial are its pair sources. -/
theorem gates_toChain (w : Word X Y) :
    w.toChain.gates = w.gates.map fun o ↦ ⟨o.1, o.2.1, o.2.2.1, .inl o.2.2.2⟩ :=
  PartyCircuit.gates_mapGates _ w

end Word

/-- An operator is source-only when it is the operator of an allowed word: a composition of
local contractions and normalized pair sources. Source: `04-compression.tex`, lines 65–66. -/
def IsSourceOnly [Fintype P] {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (T : Matrix (Config Y) (Config X) ℂ) : Prop :=
  ∃ w : Word X Y, w.IsAllowed ∧ w.op = T

/-! ### Sources and effects of monomials -/

namespace Monomial

variable {D : Finset P} {X Y : D → Type}

/-- The pair data of a gate of a monomial, if it is a pair source. -/
def chainSource? : GateOccurrence (ChainGate (P := ↥D)) → Option (PairSource ↥D)
  | ⟨_, _, _, .inl g⟩ => some g.toPairSource
  | ⟨_, _, _, .inr _⟩ => none

/-- The pair data of a gate of a monomial, if it is a pair effect. -/
def chainEffect? : GateOccurrence (ChainGate (P := ↥D)) → Option (PairSource ↥D)
  | ⟨_, _, _, .inl _⟩ => none
  | ⟨_, _, _, .inr g⟩ => some g.toPairSource

/-- The pair sources of a monomial, the latest first. -/
def sources (M : Monomial D X Y) : SourceInventory ↥D :=
  (M.gates.filterMap chainSource?).reverse

/-- The pair effects of a monomial, their endpoints and vectors, in chronological order. -/
def effects (M : Monomial D X Y) : List (PairSource ↥D) :=
  M.gates.filterMap chainEffect?

/-- The endpoint parties of the pair effects of a monomial, in chronological order. -/
def effectParties (M : Monomial D X Y) : List (↥D × ↥D) :=
  M.effects.map fun e ↦ (e.left, e.right)

/-- The number of pair effects of a monomial. Source: `04-compression.tex`, lines 56–57. -/
def effectCount (M : Monomial D X Y) : ℕ := M.effects.length

/-- The number of pair sources of a monomial. -/
def sourceCount (M : Monomial D X Y) : ℕ := M.sources.length

/-- Every gate of a monomial is a pair source or a pair effect. -/
theorem effectCount_add_sourceCount (M : Monomial D X Y) :
    M.effectCount + M.sourceCount = M.numGates := by
  rw [effectCount, sourceCount, sources, List.length_reverse, effects,
    ← PartyCircuit.length_gates]
  induction M.gates with
  | nil => rfl
  | cons o l ih =>
    obtain ⟨_, _, _, g | g⟩ := o
    · simp only [List.filterMap_cons, chainEffect?, chainSource?, List.length_cons] at ih ⊢
      omega
    · simp only [List.filterMap_cons, chainEffect?, chainSource?, List.length_cons] at ih ⊢
      omega

/-- Numbers of pair effects add under composition. -/
theorem effectCount_comp {Z : D → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (M : Monomial D X Y) (M' : Monomial D Y Z) :
    Monomial.effectCount (PartyCircuit.comp M M') = M.effectCount + M'.effectCount := by
  rw [effectCount, effects, PartyCircuit.gates, List.filterMap_append, List.length_append]
  rfl

/-- Numbers of pair sources add under composition. -/
theorem sourceCount_comp {Z : D → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (M : Monomial D X Y) (M' : Monomial D Y Z) :
    Monomial.sourceCount (PartyCircuit.comp M M') = M.sourceCount + M'.sourceCount := by
  rw [sourceCount, sources, PartyCircuit.gates, List.filterMap_append, List.reverse_append,
    List.length_append, Nat.add_comm]
  rfl

/-- A word read as a monomial has no pair effect. -/
theorem effects_toChain (w : Word (P := ↥D) X Y) : Monomial.effects w.toChain = [] := by
  rw [effects, Word.gates_toChain, List.filterMap_map]
  exact List.filterMap_eq_nil_iff.mpr fun _ _ ↦ rfl

end Monomial

end QuantumCircuit.Party
