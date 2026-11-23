/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Effect.Resources
import QICLean.Circuit.Party.Effect.Error

/-!
# Approximate gate expansions and the rescaled original circuit

In the proof of Theorem 5.2 every gate `M` of a circuit is approximated by a gate expansion
`G = ∑_ξ c_ξ M_ξ` with `‖M‖ ≤ 1` and `‖G - M‖ ≤ δ`. The effect circuit `c` carries the
expansions, the family `GateMaps c` the gates `M`, one for each occurrence
(`evalWithGateMaps`: the circuit with the gates `M`). Rescaling all coefficients of every
expansion by `(1 + δ)⁻¹` makes every gate a contraction, so the rescaled circuit is an original
circuit (`rescaledOriginal`), with the same gate occurrences, cells, participations and
expansion bounds, and within `2 δ N` of the circuit of the gates `M`, `N` its number of gates
(`norm_rescaledOriginal_sub_evalWithGateMaps_le`).

## Main definitions

* `QuantumCircuit.Party.EffectCircuit.GateMaps`, `evalWithGateMaps`, `IsGateApproximation`.
* `QuantumCircuit.Party.EffectCircuit.rescaledOriginal`, `rescaledLocationsEquiv`.

## Main results

* `QuantumCircuit.Party.EffectCircuit.norm_evalWithGateMaps_le_one`.
* `nonprivateCount_rescaledOriginal`, `participants_rescaledOriginal`,
  `participation_rescaledOriginal`, `isExpansionBounded_rescaledOriginal`,
  `isMonomialBounded_rescaledOriginal`, `isSourceBounded_rescaledOriginal`.
* `QuantumCircuit.Party.EffectCircuit.norm_rescaledOriginal_sub_evalWithGateMaps_le`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2 `thm:compression` and its proof,
  `04-compression.tex`, lines 132–171 (the last assertion, lines 167–170) and 590–598.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace EffectCircuit

/-! ### Gate maps -/

/-- The gates `M` of the chronology, one for each gate occurrence: a matrix on the configurations of
the cell. -/
@[reducible] def GateMaps : {X Y : P → Type} → EffectCircuit X Y → Type
  | _, _, PartyCircuit.done _ => PUnit
  | X, Y, PartyCircuit.gate D _ _ => Matrix (RegionConfig Y D) (RegionConfig X D) ℂ
  | _, _, PartyCircuit.localOp _ _ _ => PUnit
  | _, _, PartyCircuit.localOps _ => PUnit
  | _, _, PartyCircuit.comp c c' => GateMaps c × GateMaps c'

/-- The circuit with the gate maps in place of the gate expansions, with the same spectator
identities. -/
def evalWithGateMaps [Fintype P] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] →
    (c : EffectCircuit X Y) → c.GateMaps → Matrix (Config Y) (Config X) ℂ
  | _, _, _, _, PartyCircuit.done _, _ => 1
  | _, _, _, _, PartyCircuit.gate D hY _, G => placeBetween D hY G
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A, _ =>
    (PartyCircuit.localOp (G := WeightedGate) p hY A).op WeightedGate.ev
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A, _ => piKronecker A
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', G =>
    evalWithGateMaps c' G.2 * evalWithGateMaps c G.1

section EvalRules

variable [Fintype P] {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The empty circuit of gate maps is the identity. -/
@[simp] theorem evalWithGateMaps_done (G : GateMaps (PartyCircuit.done X : EffectCircuit X X)) :
    evalWithGateMaps (PartyCircuit.done X : EffectCircuit X X) G = 1 :=
  rfl

/-- One gate map is placed on its cell. -/
@[simp] theorem evalWithGateMaps_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : WeightedGate D X Y) (G : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    evalWithGateMaps (PartyCircuit.gate D hY g : EffectCircuit X Y) G = placeBetween D hY G :=
  rfl

/-- The gate maps of a composition act one after the other, the later on the left. -/
@[simp] theorem evalWithGateMaps_comp (c : EffectCircuit X Y) (c' : EffectCircuit Y Z)
    (G : GateMaps (PartyCircuit.comp c c')) :
    evalWithGateMaps (PartyCircuit.comp c c') G =
      evalWithGateMaps c' G.2 * evalWithGateMaps c G.1 :=
  rfl

end EvalRules

/-- The local hypotheses of an approximate expansion: the local operations and the gate maps are
contractions, every gate is not private and has allowed monomials, and every expansion is within `δ`
of its gate map. No comparison of whole circuits is assumed. Source: Theorem 5.2,
`04-compression.tex`, lines 167–170 and 590–598. -/
def IsGateApproximation (δ : ℝ) : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) → c.GateMaps → Prop
  | _, _, _, _, PartyCircuit.done _, _ => True
  | _, _, _, _, PartyCircuit.gate D _ g, G =>
    D.card ≠ 1 ∧ WeightedGate.IsAllowed g ∧ ‖G‖ ≤ 1 ∧ ‖WeightedGate.ev g () - G‖ ≤ δ
  | _, _, _, _, PartyCircuit.localOp _ _ A, _ => ‖A‖ ≤ 1
  | _, _, _, _, PartyCircuit.localOps A, _ => ∀ p, ‖A p‖ ≤ 1
  | _, _, _, _, PartyCircuit.comp c c', G =>
    IsGateApproximation δ c G.1 ∧ IsGateApproximation δ c' G.2

/-- The circuit of the gate maps is a contraction. -/
theorem norm_evalWithGateMaps_le_one [Fintype P] {δ : ℝ} : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] → (c : EffectCircuit X Y) →
      (G : c.GateMaps) → c.IsGateApproximation δ G → ‖c.evalWithGateMaps G‖ ≤ 1
  | X, _, iF, _, iF', PartyCircuit.done _, _, _ => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    change ‖(1 : Matrix (Config X) (Config X) ℂ)‖ ≤ 1
    simpa using l2_opNorm_toMatrix_toPEquiv_le (Equiv.refl (Config X))
  | _, _, _, _, iF', @PartyCircuit.gate _ _ _ _ iF _ _ _ _, _, h => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    exact (norm_placeBetween_le _ _).trans h.2.2.1
  | _, _, _, _, iF', @PartyCircuit.localOp _ _ _ _ iF _ p hY A, _, h => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    exact PartyCircuit.norm_op_le_one WeightedGate.ev
      (c := PartyCircuit.localOp (G := WeightedGate) p hY A) (A := WeightedGate.IsAllowed) h
  | _, _, _, _, iF', @PartyCircuit.localOps _ _ _ _ iF _ _, _, h => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    exact l2_opNorm_piKronecker_le_one h
  | _, _, _, _, _, PartyCircuit.comp c c', G, h =>
    l2_opNorm_mul_le_one _ _ (norm_evalWithGateMaps_le_one c' G.2 h.2)
      (norm_evalWithGateMaps_le_one c G.1 h.1)

/-! ### The rescaled original circuit -/

/-- **The rescaled original circuit**: every expansion rescaled by `(1 + δ)⁻¹`, a contraction; the
local operations, the cells and the systems unchanged. Source: Theorem 5.2, `04-compression.tex`,
lines 590–598. -/
def rescaledOriginal {δ : ℝ} (hδ : 0 ≤ δ) : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) → (G : c.GateMaps) →
      c.IsGateApproximation δ G → OriginalCircuit X Y
  | _, _, _, _, PartyCircuit.done X, _, _ => OriginalCircuit.done X
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, _, h =>
    OriginalCircuit.gate D hY (OriginalGate.ofWeightedGate (WeightedGate.rescale δ g) h.1
      (WeightedGate.isAllowed_rescale δ h.2.1) (by
        rw [WeightedGate.ev_rescale]
        exact norm_inv_one_add_smul_le_one hδ (norm_le_one_add_of_norm_sub_le h.2.2.1 h.2.2.2)))
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A, _, h => OriginalCircuit.localOp p hY A h
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A, _, h => OriginalCircuit.localOps A h
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', G, h =>
    (rescaledOriginal hδ c G.1 h.1).comp (rescaledOriginal hδ c' G.2 h.2)

variable {δ : ℝ} (hδ : 0 ≤ δ)

/-- The rescaled circuit of a composition is the composition of the rescaled circuits. -/
@[simp] theorem rescaledOriginal_comp {X Y Z : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (c : EffectCircuit X Y) (c' : EffectCircuit Y Z) (G : GateMaps (PartyCircuit.comp c c'))
    (h : IsGateApproximation δ (PartyCircuit.comp c c') G) :
    rescaledOriginal hδ (PartyCircuit.comp c c') G h =
      (rescaledOriginal hδ c G.1 h.1).comp (rescaledOriginal hδ c' G.2 h.2) :=
  rfl

/-- The rescaled circuit has the gate occurrences of the circuit. -/
def rescaledLocationsEquiv : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) → (G : c.GateMaps) →
      (h : c.IsGateApproximation δ G) →
        (c.rescaledOriginal hδ G h).nonprivateLocations ≃ c.gateLocations
  | _, _, _, _, PartyCircuit.done _, _, _ => Equiv.refl _
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _ => Equiv.refl _
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _ => Equiv.refl _
  | _, _, _, _, PartyCircuit.localOps _, _, _ => Equiv.refl _
  | _, _, _, _, PartyCircuit.comp c c', G, h =>
    Equiv.sumCongr (rescaledLocationsEquiv c G.1 h.1) (rescaledLocationsEquiv c' G.2 h.2)

/-- No gate is added or removed by the rescaling: the number of nonprivate gates of the rescaled
circuit is the number of gates. -/
theorem nonprivateCount_rescaledOriginal {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] (c : EffectCircuit X Y) (G : c.GateMaps)
    (h : c.IsGateApproximation δ G) :
    (c.rescaledOriginal hδ G h).nonprivateCount = c.numGates := by
  rw [OriginalCircuit.nonprivateCount_eq_numGates, ← PartyCircuit.card_gateLocations,
    ← PartyCircuit.card_gateLocations]
  exact Fintype.card_congr (c.rescaledLocationsEquiv hδ G h)

/-- Every rescaled gate keeps its cell. -/
theorem participants_rescaledOriginal : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) → (G : c.GateMaps) →
      (h : c.IsGateApproximation δ G) → (g : (c.rescaledOriginal hδ G h).nonprivateLocations) →
        (c.rescaledOriginal hδ G h).participants g =
          c.participants (c.rescaledLocationsEquiv hδ G h g)
  | _, _, _, _, PartyCircuit.done _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.localOps _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.comp c c', G, h, g => by
    rcases g with g | g
    exacts [participants_rescaledOriginal c G.1 h.1 g, participants_rescaledOriginal c' G.2 h.2 g]

/-- A party participates in the same gate occurrences after rescaling. -/
theorem participation_rescaledOriginal {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] (c : EffectCircuit X Y) (G : c.GateMaps)
    (h : c.IsGateApproximation δ G) (p : P) :
    (c.rescaledOriginal hδ G h).participation p =
      Nat.card {g : c.gateLocations // p ∈ c.participants g} := by
  rw [← OriginalCircuit.natCard_participants_mem]
  exact Nat.card_congr ((c.rescaledLocationsEquiv hδ G h).subtypeEquiv fun g ↦ by
    rw [participants_rescaledOriginal])

/-- The rescaled circuit keeps the pair-effect and coefficient-sum bounds. -/
theorem isExpansionBounded_rescaledOriginal {r : ℕ} {S : ℝ} : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) →
    (G : c.GateMaps) → (h : c.IsGateApproximation δ G) → c.IsExpansionBounded r S →
      (c.rescaledOriginal hδ G h).IsExpansionBounded r S
  | _, _, _, _, PartyCircuit.done _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ g, _, _, hb =>
    ⟨fun t ht ↦ by
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
      exact hb.1 t' ht', (WeightedGate.sum_norm_rescale_le hδ g).trans hb.2⟩
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.comp c c', G, h, hb =>
    ⟨isExpansionBounded_rescaledOriginal c G.1 h.1 hb.1,
      isExpansionBounded_rescaledOriginal c' G.2 h.2 hb.2⟩

/-- The rescaled circuit keeps the monomial bound. -/
theorem isMonomialBounded_rescaledOriginal {K : ℕ} : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) →
    (G : c.GateMaps) → (h : c.IsGateApproximation δ G) → (∀ g, c.monomialCount g ≤ K) →
      (c.rescaledOriginal hδ G h).IsMonomialBounded K
  | _, _, _, _, PartyCircuit.done _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _, hK => (List.length_map _).trans_le (hK ())
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.comp c c', G, h, hK =>
    ⟨isMonomialBounded_rescaledOriginal c G.1 h.1 fun g ↦ hK (Sum.inl g),
      isMonomialBounded_rescaledOriginal c' G.2 h.2 fun g ↦ hK (Sum.inr g)⟩

/-- The rescaled circuit keeps the pair-source bound. -/
theorem isSourceBounded_rescaledOriginal {r : ℕ} : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) →
    (G : c.GateMaps) → (h : c.IsGateApproximation δ G) → c.IsSourceBounded r →
      (c.rescaledOriginal hδ G h).IsSourceBounded r
  | _, _, _, _, PartyCircuit.done _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _, hr => fun t ht ↦ by
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact hr t' ht'
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.localOps _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.comp c c', G, h, hr =>
    ⟨isSourceBounded_rescaledOriginal c G.1 h.1 hr.1,
      isSourceBounded_rescaledOriginal c' G.2 h.2 hr.2⟩

/-- The number of monomials at an occurrence is unchanged by the rescaling. -/
theorem monomialCount_rescaledOriginal : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) → (G : c.GateMaps) →
      (h : c.IsGateApproximation δ G) →
      (g : (c.rescaledOriginal hδ G h).toEffectCircuit.gateLocations) →
        (c.rescaledOriginal hδ G h).toEffectCircuit.monomialCount g =
          c.monomialCount (c.rescaledLocationsEquiv hδ G h
            ((c.rescaledOriginal hδ G h).toEffectCircuitLocationsEquiv.symm g))
  | _, _, _, _, PartyCircuit.done _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.gate _ _ _, _, _, _ => List.length_map _
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.localOps _, _, _, g => g.elim
  | _, _, _, _, PartyCircuit.comp c c', G, h, g => by
    rcases g with g | g
    · exact monomialCount_rescaledOriginal c G.1 h.1 g
    · exact monomialCount_rescaledOriginal c' G.2 h.2 g

/-- **The rescaled circuit is within `2 δ` per gate of the circuit of the gate maps**, every gate
counted (`numGates`). Source: Theorem 5.2, `04-compression.tex`, lines 210–216 and 590–598. -/
theorem norm_rescaledOriginal_sub_evalWithGateMaps_le [Fintype P] : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] →
    (c : EffectCircuit X Y) → (G : c.GateMaps) → (h : c.IsGateApproximation δ G) →
      ‖(c.rescaledOriginal hδ G h).op - c.evalWithGateMaps G‖ ≤ 2 * δ * c.numGates
  | X, _, iF, _, iF', PartyCircuit.done _, _, _ => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    change ‖(1 : Matrix (Config X) (Config X) ℂ) - 1‖ ≤ 2 * δ * ((0 : ℕ) : ℝ)
    simp
  | _, _, _, _, iF', @PartyCircuit.gate _ _ _ _ iF _ D hY g, G, h => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    change ‖(OriginalCircuit.gate D hY _).op - placeBetween D hY G‖ ≤ 2 * δ * ((1 : ℕ) : ℝ)
    rw [OriginalCircuit.op_gate, placeBetween_sub, Nat.cast_one, mul_one]
    refine (norm_placeBetween_le _ _).trans ?_
    change ‖WeightedGate.ev (WeightedGate.rescale δ g) () - G‖ ≤ 2 * δ
    rw [WeightedGate.ev_rescale]
    exact norm_inv_one_add_smul_sub_le hδ h.2.2.1 h.2.2.2
  | _, _, _, _, iF', @PartyCircuit.localOp _ _ _ _ iF _ p hY A, _, h => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    change ‖(OriginalCircuit.localOp p hY A h).op -
      (PartyCircuit.localOp (G := WeightedGate) p hY A).op WeightedGate.ev‖ ≤ _
    rw [show (OriginalCircuit.localOp p hY A h).op = _ from
      (OriginalCircuit.op_localOp p hY A h).trans
        (PartyCircuit.op_localOp WeightedGate.ev p hY A).symm, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hδ) (Nat.cast_nonneg _)
  | _, _, _, _, iF', @PartyCircuit.localOps _ _ _ _ iF _ A, _, h => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    change ‖(OriginalCircuit.localOps A h).op - piKronecker A‖ ≤ _
    rw [show (OriginalCircuit.localOps A h).op = _ from OriginalCircuit.op_localOps A h, sub_self,
      norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hδ) (Nat.cast_nonneg _)
  | _, _, _, _, _, PartyCircuit.comp c c', G, h => by
    change ‖((rescaledOriginal hδ c G.1 h.1).comp (rescaledOriginal hδ c' G.2 h.2)).op -
      evalWithGateMaps c' G.2 * evalWithGateMaps c G.1‖ ≤
        2 * δ * ((c.numGates + c'.numGates : ℕ) : ℝ)
    rw [OriginalCircuit.op_comp]
    refine (Matrix.norm_mul_sub_mul_le _ _ _ _ (OriginalCircuit.norm_op_le_one _)
      (norm_evalWithGateMaps_le_one c G.1 h.1)).trans ?_
    have h1 := norm_rescaledOriginal_sub_evalWithGateMaps_le c G.1 h.1
    have h2 := norm_rescaledOriginal_sub_evalWithGateMaps_le c' G.2 h.2
    push_cast
    linarith

end EffectCircuit

end QuantumCircuit.Party
