/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.GateExpansion.CoefficientBounds
import QICLean.Circuit.Party.Compression.GateExpansion.Messages
import QICLean.Circuit.Party.Compression.GateExpansion.Reexpansion

/-!
# Gate expansions with messages on a fixed chronology

Each gate occurrence of an effect circuit is assigned a gate expansion with messages
(`MessageGateLists`). Expanding the messages chooses new gate expansions for the same chronology
(`expandMessageGateLists`, read through `EffectCircuit.reexpand`); no other chronology appears.
Local operations, cells and gate maps are kept. If every expansion with messages approximates its
gate map (`IsMessageGateApproximation`), so does every expansion after the messages are expanded
(`isGateApproximation_expandMessageGateLists`). Bounds on the number of message monomials, their
coefficients, their pair effects and the number and dimensions of their messages
(`IsMessageResourceBounded`) give bounds on the number of monomials and termwise bounds after
the expansion, before any pair effect is eliminated.

## Main definitions

* `QuantumCircuit.Party.EffectCircuit.MessageGateLists`, `expandMessageGateLists`,
  `IsMessageGateApproximation`, `IsMessageResourceBounded`.

## Main results

* `QuantumCircuit.Party.EffectCircuit.IsMessageGateApproximation.mono`,
  `IsMessageResourceBounded.mono_dimension`, `IsMessageResourceBounded.mono_coefficient`.
* `QuantumCircuit.Party.EffectCircuit.isGateApproximation_expandMessageGateLists`,
  `monomialCount_expandMessageGateLists_le`, `isTermwiseBounded_expandMessageGateLists`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 32–45, 137–178 and 590–598.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace EffectCircuit

/-- One gate expansion with messages on the cell of each gate occurrence. Source: Theorem 5.2,
`04-compression.tex`, lines 32–45 and 137–147. -/
@[reducible] def MessageGateLists : {X Y : P → Type} → EffectCircuit X Y → Type 1
  | _, _, PartyCircuit.done _ => PUnit
  | X, Y, PartyCircuit.gate D _ _ => MessageGate D (fun s ↦ X s) (fun s ↦ Y s)
  | _, _, PartyCircuit.localOp _ _ _ => PUnit
  | _, _, PartyCircuit.localOps _ => PUnit
  | _, _, PartyCircuit.comp c c' => MessageGateLists c × MessageGateLists c'

/-- Expand the messages at every gate occurrence of the same chronology. Source: Theorem 5.2,
`04-compression.tex`, lines 32–45 and 137–147. -/
def expandMessageGateLists : {X Y : P → Type} → (c : EffectCircuit X Y) →
    c.MessageGateLists → c.GateLists
  | _, _, PartyCircuit.done _, _ => PUnit.unit
  | _, _, PartyCircuit.gate _ _ _, lists => ⟨MessageGate.expand lists⟩
  | _, _, PartyCircuit.localOp _ _ _, _ => PUnit.unit
  | _, _, PartyCircuit.localOps _, _ => PUnit.unit
  | _, _, PartyCircuit.comp c c', lists =>
    (expandMessageGateLists c lists.1, expandMessageGateLists c' lists.2)

/-- The local operations and the gate maps are contractions, every gate is not private, every
message monomial is allowed, and every expansion with messages is within `δ` of its gate map. No
comparison of whole circuits is assumed. Source: Theorem 5.2, `04-compression.tex`,
lines 143–147, 167–170 and 590–598. -/
def IsMessageGateApproximation (δ : ℝ) : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) → c.MessageGateLists → c.GateMaps → Prop
  | _, _, _, _, PartyCircuit.done _, _, _ => True
  | _, _, _, _, PartyCircuit.gate D _ _, lists, G =>
    D.card ≠ 1 ∧ (∀ t ∈ lists, t.2.IsAllowed) ∧ ‖G‖ ≤ 1 ∧ ‖MessageGate.op lists - G‖ ≤ δ
  | _, _, _, _, PartyCircuit.localOp _ _ A, _, _ => ‖A‖ ≤ 1
  | _, _, _, _, PartyCircuit.localOps A, _, _ => ∀ p, ‖A p‖ ≤ 1
  | _, _, _, _, PartyCircuit.comp c c', lists, G =>
    IsMessageGateApproximation δ c lists.1 G.1 ∧ IsMessageGateApproximation δ c' lists.2 G.2

/-- Bounds on the expansions with messages, before any expansion: at most `K` message monomials,
each with at most `r` pair effects, a coefficient of norm at most `C`, and at most `m` messages
of dimension at most `D`; repeated messages count separately. Source: Theorem 5.2,
`04-compression.tex`, lines 143–147, 175–178 and 199–208. -/
def IsMessageResourceBounded (r m K : ℕ) (D C : ℝ) :
    {X Y : P → Type} → (c : EffectCircuit X Y) → c.MessageGateLists → Prop
  | _, _, PartyCircuit.done _, _ => True
  | _, _, PartyCircuit.gate _ _ _, lists =>
    lists.length ≤ K ∧ ∀ t ∈ lists, t.2.effectCount ≤ r ∧ ‖t.1‖ ≤ C ∧
      t.2.messageDimensions.length ≤ m ∧ ∀ d ∈ t.2.messageDimensions, (d : ℝ) ≤ D
  | _, _, PartyCircuit.localOp _ _ _, _ => True
  | _, _, PartyCircuit.localOps _, _ => True
  | _, _, PartyCircuit.comp c c', lists =>
    IsMessageResourceBounded r m K D C c lists.1 ∧ IsMessageResourceBounded r m K D C c' lists.2

section Rules

variable {X Y Z : P → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- At one gate the messages of its expansion are expanded. -/
@[simp] theorem expandMessageGateLists_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : WeightedGate D X Y) (lists : MessageGate D (fun s ↦ X s) (fun s ↦ Y s)) :
    expandMessageGateLists (PartyCircuit.gate D hY g : EffectCircuit X Y) lists =
      ⟨MessageGate.expand lists⟩ :=
  rfl

/-- The messages of a composition are expanded part by part. -/
@[simp] theorem expandMessageGateLists_comp (c : EffectCircuit X Y) (c' : EffectCircuit Y Z)
    (lists : MessageGateLists (PartyCircuit.comp c c')) :
    expandMessageGateLists (PartyCircuit.comp c c') lists =
      (expandMessageGateLists c lists.1, expandMessageGateLists c' lists.2) :=
  rfl

/-- The resource bounds of one gate. -/
@[simp] theorem isMessageResourceBounded_gate (r m K : ℕ) (Dm C : ℝ) (D : Finset P)
    (hY : ∀ s ∉ D, Y s = X s) (g : WeightedGate D X Y)
    (lists : MessageGate D (fun s ↦ X s) (fun s ↦ Y s)) :
    IsMessageResourceBounded r m K Dm C (PartyCircuit.gate D hY g : EffectCircuit X Y) lists ↔
      lists.length ≤ K ∧ ∀ t ∈ lists, t.2.effectCount ≤ r ∧ ‖t.1‖ ≤ C ∧
        t.2.messageDimensions.length ≤ m ∧ ∀ d ∈ t.2.messageDimensions, (d : ℝ) ≤ Dm :=
  Iff.rfl

/-- A composition satisfies the resource bounds when both parts do. -/
@[simp] theorem isMessageResourceBounded_comp (r m K : ℕ) (Dm C : ℝ) (c : EffectCircuit X Y)
    (c' : EffectCircuit Y Z) (lists : MessageGateLists (PartyCircuit.comp c c')) :
    IsMessageResourceBounded r m K Dm C (PartyCircuit.comp c c') lists ↔
      IsMessageResourceBounded r m K Dm C c lists.1 ∧
        IsMessageResourceBounded r m K Dm C c' lists.2 :=
  Iff.rfl

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The approximation condition at one gate. -/
@[simp] theorem isMessageGateApproximation_gate (δ : ℝ) (D : Finset P)
    (hY : ∀ s ∉ D, Y s = X s) (g : WeightedGate D X Y)
    (lists : MessageGate D (fun s ↦ X s) (fun s ↦ Y s))
    (G : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    IsMessageGateApproximation δ (PartyCircuit.gate D hY g : EffectCircuit X Y) lists G ↔
      D.card ≠ 1 ∧ (∀ t ∈ lists, t.2.IsAllowed) ∧ ‖G‖ ≤ 1 ∧ ‖MessageGate.op lists - G‖ ≤ δ :=
  Iff.rfl

/-- A composition satisfies the approximation condition when both parts do. -/
@[simp] theorem isMessageGateApproximation_comp (δ : ℝ) (c : EffectCircuit X Y)
    (c' : EffectCircuit Y Z) (lists : MessageGateLists (PartyCircuit.comp c c'))
    (G : GateMaps (PartyCircuit.comp c c')) :
    IsMessageGateApproximation δ (PartyCircuit.comp c c') lists G ↔
      IsMessageGateApproximation δ c lists.1 G.1 ∧ IsMessageGateApproximation δ c' lists.2 G.2 :=
  Iff.rfl

end Rules

/-- A larger gate error budget keeps the same expansions and gate maps. Source: Theorem 5.2,
`04-compression.tex`, lines 590–598. -/
theorem IsMessageGateApproximation.mono {δ ε : ℝ} : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → {c : EffectCircuit X Y} →
    {lists : c.MessageGateLists} → {G : c.GateMaps} → c.IsMessageGateApproximation δ lists G →
      δ ≤ ε → c.IsMessageGateApproximation ε lists G
  | _, _, _, _, PartyCircuit.done _, _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _, h, hδε =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hδε⟩
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, h, _ => h
  | _, _, _, _, PartyCircuit.localOps _, _, _, h, _ => h
  | _, _, _, _, PartyCircuit.comp _ _, _, _, h, hδε => ⟨h.1.mono hδε, h.2.mono hδε⟩

/-- A larger bound on the message dimensions keeps the other bounds. Source: Theorem 5.2,
`04-compression.tex`, lines 137–175. -/
theorem IsMessageResourceBounded.mono_dimension {r m K : ℕ} {D D' C : ℝ} : {X Y : P → Type} →
    {c : EffectCircuit X Y} → {lists : c.MessageGateLists} →
      c.IsMessageResourceBounded r m K D C lists → D ≤ D' →
        c.IsMessageResourceBounded r m K D' C lists
  | _, _, PartyCircuit.done _, _, _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, _, h, hD =>
    ⟨h.1, fun t ht ↦ ⟨(h.2 t ht).1, (h.2 t ht).2.1, (h.2 t ht).2.2.1,
      fun d hd ↦ ((h.2 t ht).2.2.2 d hd).trans hD⟩⟩
  | _, _, PartyCircuit.localOp _ _ _, _, _, _ => trivial
  | _, _, PartyCircuit.localOps _, _, _, _ => trivial
  | _, _, PartyCircuit.comp _ _, _, h, hD => ⟨h.1.mono_dimension hD, h.2.mono_dimension hD⟩

/-- A larger coefficient bound keeps the other bounds. Source: Theorem 5.2, `04-compression.tex`,
lines 137–175. -/
theorem IsMessageResourceBounded.mono_coefficient {r m K : ℕ} {D C C' : ℝ} : {X Y : P → Type} →
    {c : EffectCircuit X Y} → {lists : c.MessageGateLists} →
      c.IsMessageResourceBounded r m K D C lists → C ≤ C' →
        c.IsMessageResourceBounded r m K D C' lists
  | _, _, PartyCircuit.done _, _, _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, _, h, hC =>
    ⟨h.1, fun t ht ↦ ⟨(h.2 t ht).1, (h.2 t ht).2.1.trans hC, (h.2 t ht).2.2⟩⟩
  | _, _, PartyCircuit.localOp _ _ _, _, _, _ => trivial
  | _, _, PartyCircuit.localOps _, _, _, _ => trivial
  | _, _, PartyCircuit.comp _ _, _, h, hC => ⟨h.1.mono_coefficient hC, h.2.mono_coefficient hC⟩

/-- **Expanding the messages keeps the comparison with every gate map**: the gate maps are carried
along the same chronology, not replaced by the expanded sums. Source: Theorem 5.2,
`04-compression.tex`, lines 32–45, 137–147 and 590–598. -/
theorem isGateApproximation_expandMessageGateLists {δ : ℝ} : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) →
    (lists : c.MessageGateLists) → (G : c.GateMaps) → c.IsMessageGateApproximation δ lists G →
      (c.reexpand (c.expandMessageGateLists lists)).IsGateApproximation δ
        (c.reexpandGateMaps (c.expandMessageGateLists lists) G)
  | _, _, _, _, PartyCircuit.done _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, lists, G, h =>
    ⟨h.1, MessageGate.isAllowed_expand lists h.2.1, h.2.2.1, by
      change ‖WeightedGate.ev (⟨MessageGate.expand lists⟩ : WeightedGate _ _ _) () - G‖ ≤ δ
      rw [WeightedGate.ev_eq_gate_toGate, MessageGate.op_expand]
      exact h.2.2.2⟩
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, h => h
  | _, _, _, _, PartyCircuit.localOps _, _, _, h => h
  | _, _, _, _, PartyCircuit.comp c c', lists, G, h =>
    ⟨isGateApproximation_expandMessageGateLists c lists.1 G.1 h.1,
      isGateApproximation_expandMessageGateLists c' lists.2 G.2 h.2⟩

/-- At most `K` message monomials, each with at most `m` messages of dimension at most `D ≥ 1`,
give at most `⌈K D ^ m⌉` monomials at every gate occurrence of the same chronology; empty
expansions and messages of dimension zero are included. Source: Theorem 5.2,
`04-compression.tex`, lines 32–45 and 137–175. -/
theorem monomialCount_expandMessageGateLists_le : {X Y : P → Type} → (c : EffectCircuit X Y) →
    {r m K : ℕ} → {D C : ℝ} → 1 ≤ D → (lists : c.MessageGateLists) →
      c.IsMessageResourceBounded r m K D C lists →
        ∀ g, (c.reexpand (c.expandMessageGateLists lists)).monomialCount g ≤ ⌈(K : ℝ) * D ^ m⌉₊
  | _, _, PartyCircuit.done _, _, _, _, _, _, _, _, _, g => g.elim
  | _, _, PartyCircuit.gate _ _ _, _, m, K, D, _, hD, lists, hb, _ => by
    have hs := MessageGate.expansion_size_le lists D m K hD hb.1
      (fun t ht ↦ (hb.2 t ht).2.2.2) (fun t ht ↦ (hb.2 t ht).2.2.1)
    change (MessageGate.expand lists).length ≤ ⌈(K : ℝ) * D ^ m⌉₊
    exact_mod_cast hs.1.trans (Nat.le_ceil ((K : ℝ) * D ^ m))
  | _, _, PartyCircuit.localOp _ _ _, _, _, _, _, _, _, _, _, g => g.elim
  | _, _, PartyCircuit.localOps _, _, _, _, _, _, _, _, _, g => g.elim
  | _, _, PartyCircuit.comp c c', _, _, _, _, _, hD, lists, hb, g => by
    rcases g with g | g
    exacts [monomialCount_expandMessageGateLists_le c hD lists.1 hb.1 g,
      monomialCount_expandMessageGateLists_le c' hD lists.2 hb.2 g]

/-- Bounds on the individual coefficients of the message monomials give individual bounds after
the expansion of the messages, with the same bound on the pair effects; no bound on the
coefficient sums is assumed. Source: Theorem 5.2, `04-compression.tex`, lines 32–45, 137–175
and 199–208. -/
theorem isTermwiseBounded_expandMessageGateLists : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) → {δ D C : ℝ} → {r m K : ℕ} → 1 ≤ D →
    0 ≤ C → (lists : c.MessageGateLists) → (G : c.GateMaps) →
      c.IsMessageGateApproximation δ lists G → c.IsMessageResourceBounded r m K D C lists →
        (c.reexpand (c.expandMessageGateLists lists)).IsTermwiseBounded r ((K : ℝ) * C * D ^ m)
  | _, _, _, _, PartyCircuit.done _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, _, D, C, _, m, K, hD, hC, lists, _, ha, hb => by
    have hs := MessageGate.expansion_size_le_of_coeff_le lists D C m K hD hC hb.1
      (fun t ht ↦ (hb.2 t ht).2.2.2) (fun t ht ↦ (hb.2 t ht).2.2.1) (fun t ht ↦ (hb.2 t ht).2.1)
    intro t ht
    refine ⟨MessageGate.effectCount_expand_le lists ha.2.1 (fun q hq ↦ (hb.2 q hq).1) t ht, ?_⟩
    refine le_trans ?_ hs.2
    exact List.single_le_sum (fun x hx ↦ by
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg u.1) _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.comp c c', _, _, _, _, _, _, hD, hC, lists, G, ha, hb =>
    ⟨isTermwiseBounded_expandMessageGateLists c hD hC lists.1 G.1 ha.1 hb.1,
      isTermwiseBounded_expandMessageGateLists c' hD hC lists.2 G.2 ha.2 hb.2⟩

end EffectCircuit

end QuantumCircuit.Party
