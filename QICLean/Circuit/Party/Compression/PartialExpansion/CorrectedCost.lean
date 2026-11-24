/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Coefficients
import QICLean.Algebra.Combinatorics.GateIncidence

/-!
# The coefficient cost of corrected source positions

For a set `S` of source positions of a source circuit, the affected parties are the endpoints of
the positions of `S` (`SourceCircuit.correctedMask`). The gate occurrences touched by them are
those meeting these endpoints, so a bound `b` on the number of gates each party takes part in
over the whole circuit bounds the touched occurrences by `2 b |S|`
(`SourceCircuit.card_touched_correctedMask_le`). The ket–bra coefficient sum of the partial
expansion along these parties, times the squared physical dimensions of the endpoints, is the
weighted choice count of `GateIncidence.correctedPositionChoiceCost` and is at most
`(B ^ (4 lifetime) d ^ 4) ^ |S|` (`SourceCircuit.coefficient_physical_cost_le`). The participation
count of a party is the number of occurrences it takes part in.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.correctedMask` — the endpoints of a set of positions.

## Main results

* `QuantumCircuit.Party.SourceCircuit.card_touched_correctedMask_le`.
* `QuantumCircuit.Party.SourceCircuit.coefficient_physical_cost_le`,
  `QuantumCircuit.Party.SourceCircuit.sum_norm_coefficient_mul_conj_le_lifetime`.
* `QuantumCircuit.Party.SourceCircuit.participationCount_eq_card_incidentGates`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, equation
  `eq:compression-choice-cost`, `04-compression.tex`, lines 140–147, 199–229 and 342–381.

Adapted from TNLean, `TNLean/Lattice/Compression/SourceCircuitLifetime.lean` and
`TNLean/Lattice/Compression/SourceCircuitResourceBounds.lean` at commit `a05f5d6d0a`
(Apache-2.0). Changes: the participation count is the one of `PartyCircuit` (one-party gates
included, as before).
-/

open scoped NNReal

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace SourceCircuit

open GateIncidence

variable {X Y : P → Type}

/-! ### The parties of corrected positions -/

/-- The affected parties of a set of source positions: the endpoints of its positions.
Source: Theorem 5.2, `04-compression.tex`, lines 342–364. -/
def correctedMask (w : SourceCircuit X Y) (S : Finset w.sourceLocations) : P → Bool :=
  fun p ↦ decide (p ∈ correctedParties w.endpoints S)

open Classical in
/-- An occurrence is touched by the endpoints of `S` exactly when it meets them.
Source: Theorem 5.2, `04-compression.tex`, lines 356–364. -/
theorem isTouched_correctedMask_iff (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (g : w.gateLocations) :
    IsTouched (correctedMask w S) w g ↔
      g ∈ gatesTouching Finset.univ w.participants (correctedParties w.endpoints S) := by
  simp only [IsTouched, correctedMask, decide_eq_true_eq, mem_gatesTouching, Finset.mem_univ,
    true_and]
  exact exists_congr fun _ ↦ and_comm

open Classical in
/-- The touched occurrences are the gates meeting the endpoints of `S`. -/
private theorem filter_isTouched_correctedMask (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) :
    Finset.univ.filter (IsTouched (correctedMask w S) w) =
      gatesTouching Finset.univ w.participants (correctedParties w.endpoints S) := by
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isTouched_correctedMask_iff]

/-- The occurrence of every position of `S` is touched by the endpoints of `S`.
Source: Theorem 5.2, `04-compression.tex`, lines 342–364. -/
theorem corrected_slot_isTouched (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    {e : w.sourceLocations} (he : e ∈ S) : IsTouched (correctedMask w S) w e.1 :=
  ⟨(w.endpoints e).1, (w.endpoints_mem_participants e).1,
    decide_eq_true ((mem_correctedParties _ _ _).2 ⟨e, he, Or.inl rfl⟩)⟩

/-! ### Lifetime bounds -/

/-! ### Participation -/

/-- The participation count of a party, one-party gates included, is the number of gate
occurrences it takes part in. Source: Theorem 5.2, `04-compression.tex`, lines 140–142 and
356–364. -/
theorem participationCount_eq_card_incidentGates (w : SourceCircuit X Y) (p : P) :
    w.participationCount p = (incidentGates Finset.univ w.participants p).card := by
  rw [← PartyCircuit.natCard_participants_mem, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- **At most `2 lifetime |S|` occurrences are touched** when every endpoint of `S` takes part
in at most `lifetime` gates of the whole circuit. Source: Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 356–372. -/
theorem card_touched_correctedMask_le (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (lifetime : ℕ)
    (hlifetime : ∀ p ∈ correctedParties w.endpoints S, w.participationCount p ≤ lifetime) :
    (Finset.univ.filter (IsTouched (correctedMask w S) w)).card ≤ 2 * lifetime * S.card := by
  classical
  rw [filter_isTouched_correctedMask]
  exact card_gatesTouching_correctedParties_le Finset.univ w.participants w.endpoints S lifetime
    (fun p hp ↦ (participationCount_eq_card_incidentGates w p) ▸ hlifetime p hp)

open Classical in
/-- The ket–bra coefficient sum of the expansion along the endpoints of `S`, times the squared
physical dimensions of these endpoints, is the weighted choice count of the positions of `S`.
Source: Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex`, lines 365–381. -/
theorem coefficient_physical_cost_eq (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (physicalDim : P → ℕ) :
    (∑ ξ, ∑ ζ, ‖coefficient (correctedMask w S) w ξ *
        star (coefficient (correctedMask w S) w ζ)‖) *
        ∏ p ∈ correctedParties w.endpoints S, (physicalDim p : ℝ) ^ 2 =
      (correctedPositionChoiceCost Finset.univ w.participants w.endpoints S
        (fun g ↦ (Finset.univ : Finset (w.branchLabels g)))
        (fun g ξ ↦ ‖w.branchCoefficient g ξ‖₊) physicalDim : ℝ) := by
  rw [sum_norm_coefficient_mul_conj_eq_prod_sq]
  have h := filter_isTouched_correctedMask w S
  simp only [correctedPositionChoiceCost, ketBraCoefficientCost, NNReal.coe_mul,
    NNReal.coe_prod, NNReal.coe_pow, NNReal.coe_sum, coe_nnnorm, NNReal.coe_natCast,
    ← Finset.prod_pow]
  congr 2

/-- **The corrected-position cost.** With at most `lifetime` gates at every endpoint of `S`,
absolute coefficient sums at most `B ≥ 1` at the touched gates and physical dimensions at most
`d ≥ 1` at the endpoints, the ket–bra coefficient sum times the squared dimensions is at most
`(B ^ (4 lifetime) d ^ 4) ^ |S|`; the other systems are unrestricted. Source: Theorem 5.2,
`eq:compression-choice-cost`, `04-compression.tex`, lines 356–381. -/
theorem coefficient_physical_cost_le (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (physicalDim : P → ℕ) (lifetime : ℕ) (B d : ℝ≥0) (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hlifetime : ∀ p ∈ correctedParties w.endpoints S, w.participationCount p ≤ lifetime)
    (hcoeff : ∀ g, IsTouched (correctedMask w S) w g →
      ∑ ξ, ‖w.branchCoefficient g ξ‖₊ ≤ B)
    (hphysical : ∀ p ∈ correctedParties w.endpoints S, (physicalDim p : ℝ≥0) ≤ d) :
    (∑ ξ, ∑ ζ, ‖coefficient (correctedMask w S) w ξ *
        star (coefficient (correctedMask w S) w ζ)‖) *
        ∏ p ∈ correctedParties w.endpoints S, (physicalDim p : ℝ) ^ 2 ≤
      ((B : ℝ) ^ (4 * lifetime) * (d : ℝ) ^ 4) ^ S.card := by
  classical
  rw [coefficient_physical_cost_eq]
  have h := correctedPositionChoiceCost_le Finset.univ w.participants w.endpoints S
    (fun g ↦ (Finset.univ : Finset (w.branchLabels g)))
    (fun g ξ ↦ ‖w.branchCoefficient g ξ‖₊) physicalDim lifetime B d hB hd
    (fun p hp ↦ (participationCount_eq_card_incidentGates w p) ▸ hlifetime p hp)
    (fun g hg ↦ hcoeff g ((isTouched_correctedMask_iff w S g).mpr hg)) hphysical
  exact_mod_cast h

/-- With at most `lifetime` gates at every endpoint of `S` and absolute coefficient sums at most
`B ≥ 1` at the touched gates, the ket–bra coefficient sum is at most
`B ^ (4 lifetime |S|)`.
Source: Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex`, lines 356–373. -/
theorem sum_norm_coefficient_mul_conj_le_lifetime (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations) (lifetime : ℕ) (B : ℝ≥0) (hB : 1 ≤ B)
    (hlifetime : ∀ p ∈ correctedParties w.endpoints S, w.participationCount p ≤ lifetime)
    (hcoeff : ∀ g, IsTouched (correctedMask w S) w g →
      ∑ ξ, ‖w.branchCoefficient g ξ‖₊ ≤ B) :
    ∑ ξ, ∑ ζ, ‖coefficient (correctedMask w S) w ξ *
        star (coefficient (correctedMask w S) w ζ)‖ ≤
      (B : ℝ) ^ (4 * lifetime * S.card) := by
  have h := coefficient_physical_cost_le w S (fun _ ↦ 1) lifetime B 1 hB le_rfl hlifetime hcoeff
    fun _ _ ↦ by simp
  simpa only [Nat.cast_one, one_pow, Finset.prod_const_one, mul_one, NNReal.coe_one,
    ← pow_mul] using h

end SourceCircuit

end QuantumCircuit.Party
