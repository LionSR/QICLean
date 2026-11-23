/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Effect.Replacement

/-!
# Resources of the source-only replacement

The replacement of an effect circuit (`EffectCircuit.replacement`) has one prepared gate for
each gate, on the same cell: its gate occurrences are those of the circuit
(`replacementLocationsEquiv`, `participants_replacementLocationsEquiv`), so the number of
gates, the cells and the participation of every party are unchanged. Every prepared gate has at
most `K m^r` branch labels and absolute coefficient sum at most `S`, from the original bounds
on the gate expansions (`isExpansionBounded_replacement`, with the arithmetic of the expansion
of Lemma 5.1: `length_wordList_le`, `sum_norm_replacementCoefficients_le`, `stackLength_le`).

## Main definitions

* `QuantumCircuit.Party.EffectCircuit.replacementLocationsEquiv`.
* `QuantumCircuit.Party.SourceCircuit.IsExpansionBounded`.
* `QuantumCircuit.Party.OriginalCircuit.replacement`, `OriginalCircuit.replacementLocationsEquiv`.

## Main results

* `QuantumCircuit.Party.EffectCircuit.numGates_replacement`, `gateCells_replacement`,
  `participationCount_replacement`.
* `QuantumCircuit.Party.OriginalCircuit.participationCount_replacement(_le)`.
* `QuantumCircuit.Party.WeightedGate.sum_norm_coeff_wordList`, `length_wordList_le`,
  `sum_norm_replacementCoefficients(_le)`, `card_replacementLabels_le`, `stackLength_le`,
  `card_replacementLabels_stackLength_le`.
* `QuantumCircuit.Party.OriginalCircuit.isExpansionBounded_replacement`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 137–151 and 199–229; Lemma 5.1, lines 65–67.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

open GateExpansion

variable {P : Type} [DecidableEq P]

/-! ### Arithmetic of the replaced gate -/

namespace WeightedGate

variable {D : Finset P} {A B : ↥D → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Fintype (B s)] [∀ s, DecidableEq (B s)]

/-- The words of the replaced gate keep the absolute coefficient sum. Source: `04-compression.tex`,
lines 65–67. -/
theorem sum_norm_coeff_wordList {m : ℕ} (hm : m ≠ 0) : (L : List (ℂ × Monomial D A B)) →
    ((wordList m L).map fun q ↦ ‖q.1‖).sum = (L.map fun t ↦ ‖t.1‖).sum
  | [] => rfl
  | t :: L => by
    simp only [wordList, List.map_append, List.sum_append, List.map_map, List.map_cons,
      List.sum_cons]
    congr 1
    · rw [show ((fun q : ℂ × Word A (gateOut m (t :: L)) ↦ ‖q.1‖) ∘ _) =
          fun _ ↦ ‖t.1 * ((m : ℂ) ^ t.2.toEffectChain.effectCount)⁻¹‖ from rfl, List.map_const',
        List.sum_replicate, Finset.length_toList, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
      have : ((m : ℝ) ^ t.2.toEffectChain.effectCount) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm)
      push_cast
      field_simp
      simp only [Fintype.card_fin]
      ring
    · exact sum_norm_coeff_wordList hm L

/-- The labels of the replaced gate obey the source's monomial count. Source: `04-compression.tex`,
lines 65–67. -/
theorem length_wordList_le {m r : ℕ} (hm : m ≠ 0) (L : List (ℂ × Monomial D A B))
    (hr : ∀ t ∈ L, t.2.effectCount ≤ r) : (wordList m L).length ≤ L.length * m ^ r := by
  induction L with
  | nil => simp [wordList]
  | cons t L ih =>
    simp only [wordList, List.length_append, List.length_map, Finset.length_toList,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, List.length_cons, add_mul, one_mul]
    rw [add_comm]
    exact add_le_add (ih fun t' ht' ↦ hr t' (List.mem_cons_of_mem _ ht'))
      (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm)
        (t.2.effectCount_toEffectChain.trans_le (hr t List.mem_cons_self)))

/-- Rescaling multiplies the absolute coefficient sum by one scalar norm. -/
theorem sum_norm_replacementCoefficients {m : ℕ} (hm : m ≠ 0) (δ : ℝ)
    (L : List (ℂ × Monomial D A B)) :
    (∑ i, ‖replacementCoefficients m δ L i‖) =
      ‖(((1 + δ)⁻¹ : ℝ) : ℂ)‖ * (L.map fun t ↦ ‖t.1‖).sum := by
  simp only [replacementCoefficients, norm_mul, ← Finset.mul_sum, List.get_eq_getElem,
    Fin.sum_univ_fun_getElem (wordList m L) fun q ↦ ‖q.1‖, sum_norm_coeff_wordList hm L]

/-- The rescaled coefficients have absolute sum at most the original one. -/
theorem sum_norm_replacementCoefficients_le {m : ℕ} (hm : m ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (L : List (ℂ × Monomial D A B)) :
    (∑ i, ‖replacementCoefficients m δ L i‖) ≤ (L.map fun t ↦ ‖t.1‖).sum := by
  rw [sum_norm_replacementCoefficients hm δ L]
  have hscalar : ‖(((1 + δ)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_right hδ)
  have hsum : 0 ≤ (L.map fun t ↦ ‖t.1‖).sum := List.sum_nonneg fun x hx ↦ by
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  exact (mul_le_mul_of_nonneg_right hscalar hsum).trans_eq (one_mul _)

/-- The number of branch labels of the replaced gate. -/
theorem card_replacementLabels_le {m r : ℕ} (hm : m ≠ 0) (L : List (ℂ × Monomial D A B))
    (hr : ∀ t ∈ L, t.2.effectCount ≤ r) :
    Fintype.card (Fin (wordList m L).length) ≤ L.length * m ^ r := by
  simpa only [Fintype.card_fin] using length_wordList_le hm L hr

/-- **The uniformly chosen prepared gate** with its approximation and resource bounds, all from the
original expansion. Source: `04-compression.tex`, lines 199–212. -/
theorem exists_prepared_effectReplacement_uniform_resources {r : ℕ} {S δ : ℝ}
    (hδ : 0 < δ) (L : List (ℂ × Monomial D A B))
    (hL : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed ∧ t.2.effectCount ≤ r)
    (hG : ‖gate (toGate L)‖ ≤ 1) (hS : (L.map fun t ↦ ‖t.1‖).sum ≤ S) :
    ∃ G : PreparedSourceGate (replacementCoefficients (stackLength r S δ) δ L) A
        (gateOut (stackLength r S δ) L),
      reindex (gateEquiv (stackLength r S δ) L) (Equiv.refl _) G.eval =
        (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate (stackLength r S δ) (toGate L) ∧
      ‖G.eval - (prepGate (stackLength r S δ) L).op * gate (toGate L)‖ ≤ 2 * δ ∧
      (∑ i, ‖replacementCoefficients (stackLength r S δ) δ L i‖) ≤
        (L.map fun t ↦ ‖t.1‖).sum ∧
      Fintype.card (Fin (wordList (stackLength r S δ) L).length) ≤
        L.length * (stackLength r S δ) ^ r := by
  obtain ⟨G, he, herr⟩ := exists_prepared_effectReplacement_uniform hδ L hL hG hS
  exact ⟨G, he, herr,
    sum_norm_replacementCoefficients_le (stackLength_ne_zero r S δ) hδ.le L,
    card_replacementLabels_le (stackLength_ne_zero r S δ) L (fun t ht ↦ (hL t ht).2)⟩

omit [DecidableEq P] in
/-- The chosen stack length is polynomial in `r S / δ`. Source: `04-compression.tex`, lines 201–208.
-/
theorem stackLength_le (r : ℕ) (S δ : ℝ) : (stackLength r S δ : ℝ) ≤ (r * S / δ) ^ 2 + 2 := by
  have h := Nat.ceil_lt_add_one (sq_nonneg ((r : ℝ) * S / δ))
  simp only [stackLength, Nat.cast_add, Nat.cast_one]
  linarith

/-- The number of branch labels at the chosen stack length is polynomial. -/
theorem card_replacementLabels_stackLength_le (r : ℕ) (S δ : ℝ) (L : List (ℂ × Monomial D A B))
    (hr : ∀ t ∈ L, t.2.effectCount ≤ r) :
    (Fintype.card (Fin (wordList (stackLength r S δ) L).length) : ℝ) ≤
      L.length * ((r * S / δ) ^ 2 + 2) ^ r := by
  have h : (Fintype.card (Fin (wordList (stackLength r S δ) L).length) : ℝ) ≤
      (L.length : ℝ) * (stackLength r S δ : ℝ) ^ r := by
    exact_mod_cast card_replacementLabels_le (stackLength_ne_zero r S δ) L hr
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (stackLength_le r S δ) r) (Nat.cast_nonneg _))

end WeightedGate

/-! ### Bounds on the prepared gates of a source circuit -/

namespace SourceCircuit

/-- Every prepared gate has at most `K` branch labels and absolute coefficient sum at most `S`;
local operations need no expansion. Source: `04-compression.tex`, lines 65–67 and 199–212. -/
def IsExpansionBounded (K : ℕ) (S : ℝ) : {X Y : P → Type} → SourceCircuit X Y → Prop
  | _, _, PartyCircuit.done _ => True
  | _, _, PartyCircuit.gate _ _ g => Fintype.card g.ι ≤ K ∧ (∑ ξ, ‖g.coeff ξ‖) ≤ S
  | _, _, PartyCircuit.localOp _ _ _ => True
  | _, _, PartyCircuit.localOps _ => True
  | _, _, PartyCircuit.comp c c' => IsExpansionBounded K S c ∧ IsExpansionBounded K S c'

/-- A circuit without gates satisfies every expansion bound. -/
theorem isExpansionBounded_of_numGates_eq_zero (K : ℕ) (S : ℝ) :
    {X Y : P → Type} → {c : SourceCircuit X Y} → c.numGates = 0 → IsExpansionBounded K S c
  | _, _, PartyCircuit.done _, _ => trivial
  | _, _, PartyCircuit.gate _ _ _, h => absurd h one_ne_zero
  | _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, PartyCircuit.comp _ _, h =>
    ⟨isExpansionBounded_of_numGates_eq_zero K S (Nat.add_eq_zero_iff.mp h).1,
      isExpansionBounded_of_numGates_eq_zero K S (Nat.add_eq_zero_iff.mp h).2⟩

/-- Framing keeps the expansion bounds. -/
theorem isExpansionBounded_frame (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]
    {K : ℕ} {S : ℝ} : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
      {c : SourceCircuit X Y} → IsExpansionBounded K S c → IsExpansionBounded K S (c.frame W)
  | _, _, _, _, PartyCircuit.done _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, h => h
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _ => trivial
  | _, _, _, _, PartyCircuit.comp _ _, h =>
    ⟨isExpansionBounded_frame W h.1, isExpansionBounded_frame W h.2⟩

end SourceCircuit

/-! ### Gate occurrences of the replacement -/

namespace EffectCircuit

variable {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)

/-- **The replacement neither merges nor creates gate occurrences**. Source: `04-compression.tex`,
lines 199–229. -/
def replacementLocationsEquiv : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] → [∀ p, DecidableEq (Y p)] →
    (c : EffectCircuit X Y) → (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) →
    (hb : IsExpansionBounded r S c) → c.gateLocations ≃ (c.replacement hδ hw hb).gateLocations
  | _, _, _, _, _, _, PartyCircuit.done _, _, _ => Equiv.refl _
  | _, _, _, _, _, _, PartyCircuit.gate _ _ _, _, _ => (Equiv.sumEmpty Unit Empty).symm
  | _, _, _, _, _, _, PartyCircuit.localOp _ _ _, _, _ => (Equiv.sumEmpty Empty Empty).symm
  | _, _, _, _, _, _, PartyCircuit.localOps _, _, _ => (Equiv.sumEmpty Empty Empty).symm
  | _, _, _, _, _, _, PartyCircuit.comp c c', hw, hb =>
    Equiv.sumCongr (replacementLocationsEquiv c hw.1 hb.1)
      ((replacementLocationsEquiv c' hw.2 hb.2).trans
        ((SourceCircuit.gateLocationsFrameEquiv _ _).symm.trans (Equiv.sumEmpty _ Empty).symm))

/-- The replacement keeps the cell of every gate occurrence. Source: `04-compression.tex`, line 229.
-/
theorem participants_replacementLocationsEquiv : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] → [∀ p, DecidableEq (Y p)] →
    (c : EffectCircuit X Y) → (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) →
    (hb : IsExpansionBounded r S c) → (g : c.gateLocations) →
      PartyCircuit.participants (c.replacement hδ hw hb) (replacementLocationsEquiv hδ c hw hb g) =
        c.participants g
  | _, _, _, _, _, _, PartyCircuit.done _, _, _, g => g.elim
  | _, _, _, _, _, _, PartyCircuit.gate _ _ _, _, _, _ => rfl
  | _, _, _, _, _, _, PartyCircuit.localOp _ _ _, _, _, g => g.elim
  | _, _, _, _, _, _, PartyCircuit.localOps _, _, _, g => g.elim
  | _, _, _, _, _, _, PartyCircuit.comp c c', hw, hb, g => by
    rcases g with g | g
    · exact participants_replacementLocationsEquiv c hw.1 hb.1 g
    · exact (SourceCircuit.participants_frame _ _ _).trans
        ((congrArg _ (Equiv.apply_symm_apply _ _)).trans
          (participants_replacementLocationsEquiv c' hw.2 hb.2 g))

/-- One prepared gate for each gate. -/
theorem numGates_replacement {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (c : EffectCircuit X Y)
    (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) (hb : IsExpansionBounded r S c) :
    (c.replacement hδ hw hb).numGates = c.numGates := by
  rw [← PartyCircuit.card_gateLocations, ← PartyCircuit.card_gateLocations]
  exact (Fintype.card_congr (replacementLocationsEquiv hδ c hw hb)).symm

/-- The replacement has the cells of the circuit, in chronological order. Source:
`04-compression.tex`, line 229. -/
theorem gateCells_replacement : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] → [∀ p, DecidableEq (Y p)] →
    (c : EffectCircuit X Y) → (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) →
    (hb : IsExpansionBounded r S c) → (c.replacement hδ hw hb).gateCells = c.gateCells
  | _, _, _, _, _, _, PartyCircuit.done _, _, _ => rfl
  | _, _, _, _, _, _, PartyCircuit.gate _ _ _, _, _ => rfl
  | _, _, _, _, _, _, PartyCircuit.localOp _ _ _, _, _ => rfl
  | _, _, _, _, _, _, PartyCircuit.localOps _, _, _ => rfl
  | _, _, _, _, _, _, PartyCircuit.comp c c', hw, hb => by
    change (replacement hδ c hw.1 hb.1).gateCells ++
      ((PartyCircuit.frame _ (replacement hδ c' hw.2 hb.2)).gateCells ++ []) = _
    rw [List.append_nil, PartyCircuit.gateCells_frame, gateCells_replacement c hw.1 hb.1,
      gateCells_replacement c' hw.2 hb.2]
    rfl

/-- **The replacement keeps the participation counts** of every party over the whole chronology,
one-party gates included. Source: `04-compression.tex`, lines 140–142 and 229. -/
theorem participationCount_replacement {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (c : EffectCircuit X Y) (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed)
    (hb : IsExpansionBounded r S c) (p : P) :
    (c.replacement hδ hw hb).participationCount p = c.participationCount p := by
  rw [← PartyCircuit.natCard_participants_mem, ← PartyCircuit.natCard_participants_mem]
  exact (Nat.card_congr ((replacementLocationsEquiv hδ c hw hb).subtypeEquiv fun g ↦ by
    rw [participants_replacementLocationsEquiv])).symm

/-- The replacement keeps the participations (gates of cost one). -/
theorem participation_replacement (p : P) : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] → [∀ p, DecidableEq (Y p)] →
    (c : EffectCircuit X Y) → (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) →
    (hb : IsExpansionBounded r S c) →
      (c.replacement hδ hw hb).participation p = c.participation p
  | _, _, _, _, _, _, PartyCircuit.done _, _, _ => rfl
  | _, _, _, _, _, _, PartyCircuit.gate _ _ _, _, _ => rfl
  | _, _, _, _, _, _, PartyCircuit.localOp _ _ _, _, _ => rfl
  | _, _, _, _, _, _, PartyCircuit.localOps _, _, _ => rfl
  | _, _, _, _, _, _, PartyCircuit.comp c c', hw, hb => by
    change (replacement hδ c hw.1 hb.1).participation p +
      ((PartyCircuit.frame _ (replacement hδ c' hw.2 hb.2)).participation p + 0) = _
    rw [Nat.add_zero, PartyCircuit.participation_frame, participation_replacement p c hw.1 hb.1,
      participation_replacement p c' hw.2 hb.2]
    rfl

/-- **Every prepared gate of the replacement has at most `K m^r` labels and coefficient sum at most
`S`**, both bounds from the original data. Source: `04-compression.tex`, lines 199–212 and 229. -/
theorem isExpansionBounded_replacement {K : ℕ} : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] → [∀ p, DecidableEq (Y p)] →
    (c : EffectCircuit X Y) → (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) →
    (hb : IsExpansionBounded r S c) → IsMonomialBounded K c →
      (c.replacement hδ hw hb).IsExpansionBounded (K * (stackLength r S δ) ^ r) S
  | _, _, _, _, _, _, PartyCircuit.done _, _, _, _ => trivial
  | _, _, _, _, _, _, PartyCircuit.gate _ _ g, _, hb, hK =>
    ⟨⟨(WeightedGate.card_replacementLabels_le (stackLength_ne_zero r S δ) g.terms hb.1).trans
        (Nat.mul_le_mul_right _ hK),
      (WeightedGate.sum_norm_replacementCoefficients_le (stackLength_ne_zero r S δ) hδ.le
        g.terms).trans hb.2⟩, trivial⟩
  | _, _, _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _ => ⟨trivial, trivial⟩
  | _, _, _, _, _, _, PartyCircuit.localOps _, _, _, _ => ⟨trivial, trivial⟩
  | _, _, _, _, _, _, PartyCircuit.comp c c', hw, hb, hK =>
    ⟨isExpansionBounded_replacement c hw.1 hb.1 hK.1,
      SourceCircuit.isExpansionBounded_frame _ (isExpansionBounded_replacement c' hw.2 hb.2 hK.2),
      trivial⟩

end EffectCircuit

/-! ### Original circuits -/

namespace OriginalCircuit

variable {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The source-only replacement of an original circuit: that of its effect circuit. Source:
`04-compression.tex`, lines 199–229. -/
abbrev replacement (w : OriginalCircuit X Y) (hb : w.IsExpansionBounded r S) :
    SourceCircuit X fun p ↦ EffectCircuit.auxiliary (stackLength r S δ) w.toEffectCircuit p × Y p :=
  w.toEffectCircuit.replacement hδ w.isAllowed_toEffectCircuit hb

/-- The nonprivate occurrences are the gate occurrences of the replacement. -/
def replacementLocationsEquiv (w : OriginalCircuit X Y) (hb : w.IsExpansionBounded r S) :
    w.nonprivateLocations ≃ (w.replacement hδ hb).gateLocations :=
  w.toEffectCircuitLocationsEquiv.trans
    (EffectCircuit.replacementLocationsEquiv hδ _ w.isAllowed_toEffectCircuit hb)

/-- The replacement keeps the participants of every nonprivate occurrence. Source:
`04-compression.tex`, line 229. -/
theorem participants_replacementLocationsEquiv (w : OriginalCircuit X Y)
    (hb : w.IsExpansionBounded r S) (g : w.nonprivateLocations) :
    PartyCircuit.participants (w.replacement hδ hb) (w.replacementLocationsEquiv hδ hb g) =
      w.participants g :=
  (EffectCircuit.participants_replacementLocationsEquiv hδ _ _ hb _).trans
    (w.participants_toEffectCircuitLocationsEquiv g)

/-- The occurrences of the replacement containing a party are the nonprivate occurrences containing
it. -/
def participationLocationsEquiv (w : OriginalCircuit X Y) (hb : w.IsExpansionBounded r S)
    (p : P) :
    {g : w.nonprivateLocations // p ∈ w.participants g} ≃
      {g : (w.replacement hδ hb).gateLocations //
        p ∈ PartyCircuit.participants (w.replacement hδ hb) g} :=
  (w.replacementLocationsEquiv hδ hb).subtypeEquiv fun g ↦ by
    rw [participants_replacementLocationsEquiv]

/-- **Replacement keeps the participation of every party** over the whole chronology, repeated uses
of a gate included. Source: `04-compression.tex`, lines 140–142 and 229. -/
theorem participationCount_replacement (w : OriginalCircuit X Y) (hb : w.IsExpansionBounded r S)
    (p : P) : (w.replacement hδ hb).participationCount p = w.participation p := by
  rw [← PartyCircuit.natCard_participants_mem, ← natCard_participants_mem]
  exact (Nat.card_congr (w.participationLocationsEquiv hδ hb p)).symm

/-- The whole-lifetime participation bound of the original circuit holds for the replacement.
Source: `04-compression.tex`, lines 140–142. -/
theorem participationCount_replacement_le {b₀ : ℕ} (w : OriginalCircuit X Y)
    (hb : w.IsExpansionBounded r S) (hlifetime : ∀ p, w.participation p ≤ b₀) (p : P) :
    (w.replacement hδ hb).participationCount p ≤ b₀ :=
  (w.participationCount_replacement hδ hb p).trans_le (hlifetime p)

/-- The replacement has one prepared gate for each nonprivate gate. -/
theorem numGates_replacement (w : OriginalCircuit X Y) (hb : w.IsExpansionBounded r S) :
    (w.replacement hδ hb).numGates = w.nonprivateCount :=
  (EffectCircuit.numGates_replacement hδ _ _ hb).trans w.numGates_toEffectCircuit

/-- **Every prepared gate of the replacement of an original circuit has at most `K m^r` labels and
coefficient sum at most `S`**. Source: `04-compression.tex`, lines 199–212 and 229. -/
theorem isExpansionBounded_replacement {K : ℕ} (w : OriginalCircuit X Y)
    (hb : w.IsExpansionBounded r S) (hK : w.IsMonomialBounded K) :
    (w.replacement hδ hb).IsExpansionBounded (K * (stackLength r S δ) ^ r) S :=
  EffectCircuit.isExpansionBounded_replacement hδ _ _ hb hK

end OriginalCircuit

end QuantumCircuit.Party
