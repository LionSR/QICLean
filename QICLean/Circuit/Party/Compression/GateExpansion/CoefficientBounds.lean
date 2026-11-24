/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.Basic

/-!
# Coefficient sums from termwise bounds on the gate expansions

Theorem 5.2 bounds, at every gate, the number of monomials of its expansion and each scalar
coefficient. These two bounds give the bound on the absolute coefficient sum used in the
elimination of the pair effects: a weighted list of `K` monomials with coefficients of norm at
most `C` has coefficient sum at most `K C`. The termwise bound is a structural predicate on
effect circuits (`EffectCircuit.IsTermwiseBounded`), read on original circuits through their
effect circuits. Empty expansions and gates on the empty cell are included; no private dimension
enters.

## Main definitions

* `QuantumCircuit.Party.EffectCircuit.IsTermwiseBounded`,
  `QuantumCircuit.Party.OriginalCircuit.IsTermwiseBounded`.

## Main results

* `QuantumCircuit.Party.WeightedGate.sum_norm_coefficients_le` and its power form.
* `QuantumCircuit.Party.EffectCircuit.isExpansionBounded_of_isTermwiseBounded`,
  `QuantumCircuit.Party.OriginalCircuit.isExpansionBounded_of_isTermwiseBounded` and their power
  forms; `exists_one_le_isExpansionBounded_of_termwise_power_bounds`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, item 3, `04-compression.tex`,
  lines 143–147, and its use at lines 175–178, 199–208 and 590–598.
-/

open scoped NNReal

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Weighted lists of monomials -/

namespace WeightedGate

variable {D : Finset P} {A B : ↥D → Type}

/-- The absolute coefficient sum of a weighted list is at most its length times a bound on the
individual coefficients. Source: Theorem 5.2, item 3, `04-compression.tex`, lines 143–147 and
175–178. -/
theorem sum_norm_coefficients_le (G : List (ℂ × Monomial D A B)) (C : ℝ)
    (hC : ∀ t ∈ G, ‖t.1‖ ≤ C) : (G.map fun t ↦ ‖t.1‖).sum ≤ (G.length : ℝ) * C :=
  (List.sum_le_sum hC).trans_eq (by simp)

/-- Power bounds on the length and on the individual coefficients give a power bound on the
absolute coefficient sum. Source: Theorem 5.2, item 3, `04-compression.tex`, lines 143–147 and
175–178. -/
theorem sum_norm_coefficients_le_of_power_bounds (G : List (ℂ × Monomial D A B))
    (L C_K C_C : ℝ) (u v : ℕ) (hL : 0 ≤ L) (hCC : 0 ≤ C_C)
    (hK : (G.length : ℝ) ≤ C_K * L ^ u) (hC : ∀ t ∈ G, ‖t.1‖ ≤ C_C * L ^ v) :
    (G.map fun t ↦ ‖t.1‖).sum ≤ C_K * C_C * L ^ (u + v) := by
  calc
    _ ≤ (G.length : ℝ) * (C_C * L ^ v) := sum_norm_coefficients_le G _ hC
    _ ≤ (C_K * L ^ u) * (C_C * L ^ v) := mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by rw [pow_add]; ring

end WeightedGate

/-! ### Termwise bounds on effect circuits -/

namespace EffectCircuit

/-- Every monomial of every gate expansion has at most `r` pair effects and a coefficient of norm
at most `C`. Source: Theorem 5.2, item 3, `04-compression.tex`, lines 143–147 and 590–598. -/
def IsTermwiseBounded (r : ℕ) (C : ℝ) : {X Y : P → Type} → EffectCircuit X Y → Prop
  | _, _, PartyCircuit.done _ => True
  | _, _, PartyCircuit.gate _ _ g => ∀ t ∈ g.terms, t.2.effectCount ≤ r ∧ ‖t.1‖ ≤ C
  | _, _, PartyCircuit.localOp _ _ _ => True
  | _, _, PartyCircuit.localOps _ => True
  | _, _, PartyCircuit.comp c c' => IsTermwiseBounded r C c ∧ IsTermwiseBounded r C c'

variable {X Y Z : P → Type}

section Rules

variable [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- The empty circuit satisfies every termwise bound. -/
@[simp] theorem isTermwiseBounded_done (r : ℕ) (C : ℝ) :
    IsTermwiseBounded r C (PartyCircuit.done X : EffectCircuit X X) ↔ True :=
  Iff.rfl

/-- The termwise bound of one gate: every monomial has few pair effects and a small
coefficient. -/
@[simp] theorem isTermwiseBounded_gate (r : ℕ) (C : ℝ) (D : Finset P)
    (hY : ∀ s ∉ D, Y s = X s) (g : WeightedGate D X Y) :
    IsTermwiseBounded r C (PartyCircuit.gate D hY g : EffectCircuit X Y) ↔
      ∀ t ∈ g.terms, t.2.effectCount ≤ r ∧ ‖t.1‖ ≤ C :=
  Iff.rfl

/-- A local operation satisfies every termwise bound. -/
@[simp] theorem isTermwiseBounded_localOp (r : ℕ) (C : ℝ) (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (A : Matrix (Y p) (X p) ℂ) :
    IsTermwiseBounded r C (PartyCircuit.localOp p hY A : EffectCircuit X Y) ↔ True :=
  Iff.rfl

/-- Local operations at every party satisfy every termwise bound. -/
@[simp] theorem isTermwiseBounded_localOps (r : ℕ) (C : ℝ) (A : ∀ p, Matrix (Y p) (X p) ℂ) :
    IsTermwiseBounded r C (PartyCircuit.localOps A : EffectCircuit X Y) ↔ True :=
  Iff.rfl

/-- A composition satisfies a termwise bound when both parts do. -/
@[simp] theorem isTermwiseBounded_comp (r : ℕ) (C : ℝ) (c : EffectCircuit X Y)
    (c' : EffectCircuit Y Z) :
    IsTermwiseBounded r C (PartyCircuit.comp c c') ↔
      IsTermwiseBounded r C c ∧ IsTermwiseBounded r C c' :=
  Iff.rfl

end Rules

/-- A larger coefficient bound bounds the coefficients as well. Source: Theorem 5.2,
`04-compression.tex`, lines 137–175. -/
theorem IsTermwiseBounded.mono_coefficient {r : ℕ} {C C' : ℝ} : {X Y : P → Type} →
    {c : EffectCircuit X Y} → IsTermwiseBounded r C c → C ≤ C' → IsTermwiseBounded r C' c
  | _, _, PartyCircuit.done _, _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, h, hC => fun t ht ↦ ⟨(h t ht).1, (h t ht).2.trans hC⟩
  | _, _, PartyCircuit.localOp _ _ _, _, _ => trivial
  | _, _, PartyCircuit.localOps _, _, _ => trivial
  | _, _, PartyCircuit.comp _ _, h, hC => ⟨h.1.mono_coefficient hC, h.2.mono_coefficient hC⟩

/-- **Monomial counts and individual coefficient bounds give the coefficient-sum bound** at every
gate occurrence. Source: Theorem 5.2, item 3, `04-compression.tex`, lines 143–147 and 199–208. -/
theorem isExpansionBounded_of_isTermwiseBounded : {X Y : P → Type} → (c : EffectCircuit X Y) →
    {r K : ℕ} → {C S : ℝ} → (∀ g, c.monomialCount g ≤ K) → c.IsTermwiseBounded r C →
      0 ≤ C → (K : ℝ) * C ≤ S → c.IsExpansionBounded r S
  | _, _, PartyCircuit.done _, _, _, _, _, _, _, _, _ => trivial
  | _, _, PartyCircuit.gate _ _ g, _, _, C, _, hK, ht, hC, hS =>
    ⟨fun t htg ↦ (ht t htg).1,
      (WeightedGate.sum_norm_coefficients_le g.terms C fun t htg ↦ (ht t htg).2).trans
        ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hK ())) hC).trans hS)⟩
  | _, _, PartyCircuit.localOp _ _ _, _, _, _, _, _, _, _, _ => trivial
  | _, _, PartyCircuit.localOps _, _, _, _, _, _, _, _, _ => trivial
  | _, _, PartyCircuit.comp c c', _, _, _, _, hK, ht, hC, hS =>
    ⟨isExpansionBounded_of_isTermwiseBounded c (fun g ↦ hK (.inl g)) ht.1 hC hS,
      isExpansionBounded_of_isTermwiseBounded c' (fun g ↦ hK (.inr g)) ht.2 hC hS⟩

/-- Power bounds `K ≤ C_K L ^ u` on the monomial counts and `C_C L ^ v` on the individual
coefficients give the coefficient-sum bound `C_K C_C L ^ (u + v)`. Source: Theorem 5.2, item 3,
`04-compression.tex`, lines 143–147 and 199–208. -/
theorem isExpansionBounded_of_termwise_power_bounds (c : EffectCircuit X Y) {r K : ℕ}
    (L C_K C_C : ℝ) (u v : ℕ) (hL : 0 ≤ L) (hCC : 0 ≤ C_C) (hK : ∀ g, c.monomialCount g ≤ K)
    (ht : c.IsTermwiseBounded r (C_C * L ^ v)) (hKbound : (K : ℝ) ≤ C_K * L ^ u) :
    c.IsExpansionBounded r (C_K * C_C * L ^ (u + v)) := by
  apply c.isExpansionBounded_of_isTermwiseBounded hK ht (by positivity)
  calc
    (K : ℝ) * (C_C * L ^ v) ≤ (C_K * L ^ u) * (C_C * L ^ v) :=
      mul_le_mul_of_nonneg_right hKbound (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- Power bounds on the monomial counts and on the individual coefficients give a
coefficient-sum bound `B ≥ 1`, with constants independent of the circuit and of its private
dimensions. Source: Theorem 5.2, item 3, `04-compression.tex`, lines 143–175, 199–208 and
590–598. -/
theorem exists_one_le_isExpansionBounded_of_termwise_power_bounds (c : EffectCircuit X Y)
    {r K : ℕ} (L C_K C_C : ℝ) (u v : ℕ) (hL : 1 ≤ L) (hCK : 0 ≤ C_K) (hCC : 0 ≤ C_C)
    (hK : ∀ g, c.monomialCount g ≤ K) (ht : c.IsTermwiseBounded r (C_C * L ^ v))
    (hKbound : (K : ℝ) ≤ C_K * L ^ u) :
    ∃ B : ℝ≥0, 1 ≤ B ∧ c.IsExpansionBounded r (B : ℝ) ∧
      (B : ℝ) ≤ (1 + C_K * C_C) * L ^ (u + v) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hB1 : 1 ≤ (1 + C_K * C_C) * L ^ (u + v) :=
    one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (mul_nonneg hCK hCC))
      (one_le_pow₀ hL)
  refine ⟨⟨(1 + C_K * C_C) * L ^ (u + v), zero_le_one.trans hB1⟩, hB1, ?_, le_rfl⟩
  exact IsExpansionBounded.mono le_rfl
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity))
    (c.isExpansionBounded_of_termwise_power_bounds L C_K C_C u v hL0 hCC hK ht hKbound)

end EffectCircuit

/-! ### Termwise bounds on original circuits -/

namespace OriginalCircuit

variable {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- Every monomial of every original gate expansion has at most `r` pair effects and a
coefficient of norm at most `C`; allowedness of the local maps is a field of the original gates.
Source: Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
def IsTermwiseBounded (r : ℕ) (C : ℝ) (w : OriginalCircuit X Y) : Prop :=
  w.toEffectCircuit.IsTermwiseBounded r C

section Rules

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- A composition satisfies a termwise bound when both parts do. -/
@[simp] theorem isTermwiseBounded_comp (r : ℕ) (C : ℝ) (w : OriginalCircuit X Y)
    (w' : OriginalCircuit Y Z) :
    (w.comp w').IsTermwiseBounded r C ↔ w.IsTermwiseBounded r C ∧ w'.IsTermwiseBounded r C :=
  Iff.rfl

/-- The termwise bound of one original gate. -/
@[simp] theorem isTermwiseBounded_gate (r : ℕ) (C : ℝ) (D : Finset P)
    (hY : ∀ s ∉ D, Y s = X s) (g : OriginalGate D X Y) :
    (gate D hY g).IsTermwiseBounded r C ↔
      ∀ t ∈ g.toWeightedGate.terms, t.2.effectCount ≤ r ∧ ‖t.1‖ ≤ C :=
  Iff.rfl

end Rules

/-- **Termwise bounds give the expansion bounds** on an original circuit. Source: Theorem 5.2,
item 3, `04-compression.tex`, lines 143–147 and 175–178. -/
theorem isExpansionBounded_of_isTermwiseBounded (w : OriginalCircuit X Y) {r K : ℕ} {C S : ℝ}
    (hK : w.IsMonomialBounded K) (ht : w.IsTermwiseBounded r C) (hC : 0 ≤ C)
    (hS : (K : ℝ) * C ≤ S) : w.IsExpansionBounded r S :=
  w.toEffectCircuit.isExpansionBounded_of_isTermwiseBounded
    (w.monomialCount_toEffectCircuit_le_of_isMonomialBounded hK) ht hC hS

/-- Power bounds on the monomial counts and on the individual coefficients give the
coefficient-sum bound on an original circuit. Source: Theorem 5.2, item 3, `04-compression.tex`,
lines 143–147 and 175–178. -/
theorem isExpansionBounded_of_termwise_power_bounds (w : OriginalCircuit X Y) {r K : ℕ}
    (L C_K C_C : ℝ) (u v : ℕ) (hL : 0 ≤ L) (hCC : 0 ≤ C_C) (hK : w.IsMonomialBounded K)
    (ht : w.IsTermwiseBounded r (C_C * L ^ v)) (hKbound : (K : ℝ) ≤ C_K * L ^ u) :
    w.IsExpansionBounded r (C_K * C_C * L ^ (u + v)) :=
  w.toEffectCircuit.isExpansionBounded_of_termwise_power_bounds L C_K C_C u v hL hCC
    (w.monomialCount_toEffectCircuit_le_of_isMonomialBounded hK) ht hKbound

end OriginalCircuit

end QuantumCircuit.Party
