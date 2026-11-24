/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Sym.Card
import QICLean.Analysis.Real.SampleCount
import QICLean.Circuit.Party.Effect.Resources
import QICLean.Circuit.Party.Original.Density

/-!
# Polynomial resources of the source-only replacement

The elimination of pair effects at the gate budget `sourceGateBudget ε N` uses the stack length
`stackLength r S δ`; it is the sample count `binomialSampleCount (max 1 N) (r S) ε`, so power
bounds on the original data give power bounds on it and on the number of branch labels of every
prepared gate of the replacement (`card_branchLabels_replacement_le_power`).

Every prepared gate has one source slot for each unordered pair of distinct parties of its cell
(`PreparedSourceGate.length_slots`). The source positions of a source circuit are therefore
counted by the binomial coefficients of its cells (`card_sourceLocations_eq_sum_choose`), and
those of the replacement of an original circuit by the number of nonprivate gates times the
binomial coefficient of a bound on the cells (`card_sourceLocations_replacement_le`). With the
choice cost of Theorem 5.2 this bounds the sample count of the replacement by a power
(`binomialSampleCount_replacement_lt_power`). No private dimension or source rank enters.

## Main results

* `QuantumCircuit.Party.stackLength_sourceGateBudget_eq`,
  `stackLength_sourceGateBudget_lt_of_power_bounds`,
  `replacementMonomialBound_le_of_power_bounds`.
* `QuantumCircuit.Party.SourceCircuit.IsExpansionBounded.at_gate`.
* `QuantumCircuit.Party.PreparedSourceGate.length_slots`,
  `length_sources_branchWord_eq_choose`, `length_sources_branchWord_le_choose`.
* `QuantumCircuit.Party.SourceCircuit.slotCount_eq_choose`, `card_sourceLocations_eq_sum_choose`,
  `card_sourceLocations_le`.
* `QuantumCircuit.Party.OriginalCircuit.card_branchLabels_replacement_le_power`,
  `card_sourceLocations_replacement_le`, `binomialSampleCount_replacement_lt_power`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
  `eq:compression-effect-circuit-error`, `04-compression.tex`, lines 137–175, 199–251,
  342–381 and 565–588.
-/

noncomputable section

namespace QuantumCircuit.Party

/-! ### The stack length at the gate budget -/

/-- The stack length at the gate budget has the ceiling formula of the sample count, with cost
`r S`. Source: Theorem 5.2, `04-compression.tex`, lines 199–208 and 548–558. -/
theorem stackLength_sourceGateBudget_eq (r N : ℕ) (S ε : ℝ) :
    stackLength r S (sourceGateBudget ε N) = binomialSampleCount (max 1 N) (r * S) ε := by
  unfold stackLength sourceGateBudget binomialSampleCount
  congr 2
  rw [div_div_eq_mul_div]
  ring

/-- Power bounds on the original data give a power bound on the stack length at the gate budget,
the case without gates included. Source: Theorem 5.2, `04-compression.tex`, lines 174–175 and
199–208. -/
theorem stackLength_sourceGateBudget_lt_of_power_bounds (r N : ℕ) (S L C_N C_S : ℝ)
    (n s p : ℕ) (hL : 1 ≤ L) (hCN : 1 ≤ C_N) (hCS : 0 ≤ C_S) (hS : 0 ≤ S)
    (hN : (N : ℝ) ≤ C_N * L ^ n) (hSbound : S ≤ C_S * L ^ s) :
    (stackLength r S (sourceGateBudget (L ^ p)⁻¹ N) : ℝ) <
      (64 * C_N ^ 2 * ((r : ℝ) * C_S) ^ 2 + 2) * L ^ (2 * (n + s + p)) := by
  rw [stackLength_sourceGateBudget_eq]
  apply binomialSampleCount_inv_pow_lt N ((r : ℝ) * S) L C_N (r * C_S) n s p hL hCN
    (by positivity) (by positivity) hN
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hSbound (Nat.cast_nonneg r)

/-- The monomial bound `K m ^ r` of the replacement is polynomial in the original bounds; the
effect count `r` enters as a fixed exponent. Source: Theorem 5.2, `04-compression.tex`,
lines 174–175 and 199–212. -/
theorem replacementMonomialBound_le_of_power_bounds (K r N : ℕ) (S L C_K C_N C_S : ℝ)
    (a n s p : ℕ) (hL : 1 ≤ L) (hCK : 0 ≤ C_K) (hCN : 1 ≤ C_N) (hCS : 0 ≤ C_S) (hS : 0 ≤ S)
    (hK : (K : ℝ) ≤ C_K * L ^ a) (hN : (N : ℝ) ≤ C_N * L ^ n) (hSbound : S ≤ C_S * L ^ s) :
    ((K * stackLength r S (sourceGateBudget (L ^ p)⁻¹ N) ^ r : ℕ) : ℝ) ≤
      C_K * (64 * C_N ^ 2 * ((r : ℝ) * C_S) ^ 2 + 2) ^ r * L ^ (a + 2 * r * (n + s + p)) := by
  have hm := (stackLength_sourceGateBudget_lt_of_power_bounds r N S L C_N C_S n s p hL hCN hCS
    hS hN hSbound).le
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ (C_K * L ^ a) * ((64 * C_N ^ 2 * ((r : ℝ) * C_S) ^ 2 + 2) * L ^ (2 * (n + s + p))) ^ r := by
      gcongr
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      ring

variable {P : Type} [DecidableEq P]

/-! ### Bounds at the gate occurrences of a source circuit -/

namespace SourceCircuit

/-- The expansion bounds hold at every gate occurrence, repeated uses of a gate included. Source:
Theorem 5.2, `04-compression.tex`, lines 199–212 and 351–381. -/
theorem IsExpansionBounded.at_gate {K : ℕ} {S : ℝ} : {X Y : P → Type} →
    {w : SourceCircuit X Y} → w.IsExpansionBounded K S → (g : w.gateLocations) →
      Fintype.card (w.branchLabels g) ≤ K ∧ (∑ ξ : w.branchLabels g, ‖w.branchCoefficient g ξ‖) ≤ S
  | _, _, PartyCircuit.done _, _, g => g.elim
  | _, _, PartyCircuit.gate _ _ _, hw, _ => hw
  | _, _, PartyCircuit.localOp _ _ _, _, g => g.elim
  | _, _, PartyCircuit.localOps _, _, g => g.elim
  | _, _, PartyCircuit.comp _ _, hw, g => by
    rcases g with g | g
    exacts [hw.1.at_gate g, hw.2.at_gate g]

end SourceCircuit

/-! ### Source slots of prepared gates -/

namespace PreparedSourceGate

variable [Fintype P] {ι : Type} [Fintype ι] {c : ι → ℂ} {X Y : P → Type}

/-- Each prepared branch has one pair source at each slot. Source: `04-compression.tex`,
lines 233–251 and 342–355. -/
theorem length_sources_branchWord [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (G : PreparedSourceGate c X Y) (ξ : ι) :
    (G.branchWord ξ).sources.length = G.slots.length := by
  rw [G.sources_branchWord]
  simp only [SourceInventory.ofSlots, List.length_ofFn]

/-- The slots of a prepared gate are the unordered pairs of distinct parties. Source:
`04-compression.tex`, lines 233–251 and 342–355. -/
theorem length_slots (G : PreparedSourceGate c X Y) :
    G.slots.length = (Fintype.card P).choose 2 := by
  let s := (G.slots.map PairSource.partyPair).toFinset
  have hc : Fintype.card {k : Sym2 P // ¬k.IsDiag} = s.card :=
    Fintype.card_of_subtype s (by intro k; simpa [s] using G.pair_complete k)
  have hlen : G.slots.length = s.card := by
    simpa only [s, List.length_map] using (List.toFinset_card_of_nodup G.pair_nodup).symm
  exact hlen.trans (hc.symm.trans Sym2.card_subtype_not_diag)

/-- A prepared branch has one normalized source on every pair of distinct parties,
one-dimensional padding slots included. Source: `04-compression.tex`, lines 233–251 and
342–355. -/
theorem length_sources_branchWord_eq_choose [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (G : PreparedSourceGate c X Y) (ξ : ι) :
    (G.branchWord ξ).sources.length = (Fintype.card P).choose 2 :=
  (G.length_sources_branchWord ξ).trans G.length_slots

/-- A bound on the number of parties bounds the sources of every prepared branch, independently
of the stack length, of the private dimensions and of the size of the expansion. Source:
`04-compression.tex`, lines 140–147 and 233–251. -/
theorem length_sources_branchWord_le_choose [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (G : PreparedSourceGate c X Y) (ξ : ι) {b : ℕ}
    (hb : Fintype.card P ≤ b) : (G.branchWord ξ).sources.length ≤ b.choose 2 := by
  rw [G.length_sources_branchWord_eq_choose]
  exact Nat.choose_le_choose 2 hb

end PreparedSourceGate

/-! ### Source positions of source circuits -/

namespace SourceCircuit

/-- Every gate occurrence has one source slot for each unordered pair of parties of its cell.
Source: `04-compression.tex`, lines 233–251 and 342–355. -/
theorem slotCount_eq_choose : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (g : w.gateLocations) → w.slotCount g = (w.participants g).card.choose 2
  | _, _, PartyCircuit.done _, g => g.elim
  | _, _, PartyCircuit.gate D _ g, _ =>
    g.gate.length_slots.trans (by rw [Fintype.card_coe]; rfl)
  | _, _, PartyCircuit.localOp _ _ _, g => g.elim
  | _, _, PartyCircuit.localOps _, g => g.elim
  | _, _, PartyCircuit.comp c c', g => by
    rcases g with g | g
    exacts [slotCount_eq_choose c g, slotCount_eq_choose c' g]

/-- The source positions over all gate occurrences. Source: `04-compression.tex`,
lines 342–364. -/
theorem card_sourceLocations_eq_sum_choose {X Y : P → Type} (w : SourceCircuit X Y) :
    Fintype.card w.sourceLocations = ∑ g : w.gateLocations, (w.participants g).card.choose 2 := by
  change Fintype.card (Σ g : w.gateLocations, Fin (w.slotCount g)) = _
  simp only [Fintype.card_sigma, Fintype.card_fin, slotCount_eq_choose]

/-- A bound on the cells bounds the source positions, independently of the branch labels and of
the private dimensions. Source: `04-compression.tex`, lines 140–147 and 342–364. -/
theorem card_sourceLocations_le {X Y : P → Type} (w : SourceCircuit X Y) {b₀ : ℕ}
    (hb : ∀ g : w.gateLocations, (w.participants g).card ≤ b₀) :
    Fintype.card w.sourceLocations ≤ Fintype.card w.gateLocations * b₀.choose 2 := by
  rw [card_sourceLocations_eq_sum_choose]
  exact (Finset.sum_le_sum fun g _ ↦ Nat.choose_le_choose 2 (hb g)).trans_eq (by simp)

end SourceCircuit

/-! ### The replacement of an original circuit -/

namespace OriginalCircuit

variable {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

/-- **Every prepared gate of the replacement has polynomially many branch labels**, from the
original monomial, coefficient and effect bounds. Source: Theorem 5.2, `04-compression.tex`,
lines 137–175 and 199–229. -/
theorem card_branchLabels_replacement_le_power (w : OriginalCircuit X Y) (K r N : ℕ)
    (S L C_K C_N C_S : ℝ) (u n s p : ℕ) (hw : w.IsExpansionBounded r S)
    (hmonomial : w.IsMonomialBounded K) (hL : 1 ≤ L) (hCK : 0 ≤ C_K) (hCN : 1 ≤ C_N)
    (hCS : 0 ≤ C_S) (hS : 0 ≤ S) (hK : (K : ℝ) ≤ C_K * L ^ u) (hN : (N : ℝ) ≤ C_N * L ^ n)
    (hSbound : S ≤ C_S * L ^ s) (hδ : 0 < sourceGateBudget (L ^ p)⁻¹ N)
    (j : (w.replacement hδ hw).gateLocations) :
    (Fintype.card ((w.replacement hδ hw).branchLabels j) : ℝ) ≤
      C_K * (64 * C_N ^ 2 * ((r : ℝ) * C_S) ^ 2 + 2) ^ r * L ^ (u + 2 * r * (n + s + p)) := by
  have hc : (Fintype.card ((w.replacement hδ hw).branchLabels j) : ℝ) ≤
      ((K * stackLength r S (sourceGateBudget (L ^ p)⁻¹ N) ^ r : ℕ) : ℝ) := by
    exact_mod_cast ((w.isExpansionBounded_replacement hδ hw hmonomial).at_gate j).1
  exact hc.trans (replacementMonomialBound_le_of_power_bounds K r N S L C_K C_N C_S u n s p hL
    hCK hCN hCS hS hK hN hSbound)

/-- **The source positions of the replacement** are at most the number of nonprivate gates times
the binomial coefficient of a bound on the cells. Source: `04-compression.tex`, lines 140–147,
199–229 and 342–364. -/
theorem card_sourceLocations_replacement_le {r : ℕ} {S δ : ℝ} (w : OriginalCircuit X Y)
    (hδ : 0 < δ) (hb : w.IsExpansionBounded r S) {b₀ : ℕ}
    (hpart : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ b₀) :
    Fintype.card (w.replacement hδ hb).sourceLocations ≤ w.nonprivateCount * b₀.choose 2 := by
  let e := w.replacementLocationsEquiv hδ hb
  have hpartR : ∀ g : (w.replacement hδ hb).gateLocations,
      ((w.replacement hδ hb).participants g).card ≤ b₀ := by
    intro g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [w.participants_replacementLocationsEquiv hδ hb g]
    exact hpart g
  exact ((w.replacement hδ hb).card_sourceLocations_le hpartR).trans_eq
    (congrArg (· * b₀.choose 2) ((Fintype.card_congr e).symm.trans w.card_nonprivateLocations))

/-- **The sample count of the replacement is polynomial**: with the choice cost
`B ^ (4 b) D ^ 4` of Theorem 5.2, power bounds on the number of nonprivate gates, on the
coefficient sums and on the dimension `D`, and a bound on the cells, bound the sample count at
`max 1` of the number of source positions and accuracy `L⁻ᵖ` by a power of `L`. The coefficient
is raised to at least one only to include the case without sources. Source: Theorem 5.2,
`04-compression.tex`, lines 137–175, 199–229, 342–381 and 565–588. -/
theorem binomialSampleCount_replacement_lt_power (w : OriginalCircuit X Y) {r arity lifetime : ℕ}
    {B D δ : ℝ} (hδ : 0 < δ) (hb : w.IsExpansionBounded r B)
    (hpart : ∀ g : w.nonprivateLocations, (w.participants g).card ≤ arity) (L C_N C_B C_D : ℝ)
    (n s d p : ℕ) (hL : 1 ≤ L) (hCB : 0 ≤ C_B) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hN : (w.nonprivateCount : ℝ) ≤ C_N * L ^ n) (hBbound : B ≤ C_B * L ^ s)
    (hDbound : D ≤ C_D * L ^ d) :
    let C_sources := max 1 (C_N * (arity.choose 2 : ℝ))
    (binomialSampleCount (max 1 (Fintype.card (w.replacement hδ hb).sourceLocations))
      (B ^ (4 * lifetime) * D ^ 4) (L ^ p)⁻¹ : ℝ) <
      (64 * C_sources ^ 2 * (C_B ^ (4 * lifetime) * C_D ^ 4) ^ 2 + 2) *
        L ^ (2 * (n + 4 * lifetime * s + 4 * d + p)) := by
  intro C_sources
  apply binomialSampleCount_lt_of_cost_power_bounds _ lifetime B D L C_sources C_B C_D n s d p
    hL (le_max_left _ _) hCB hB hD _ hBbound hDbound
  calc
    _ ≤ (w.nonprivateCount : ℝ) * (arity.choose 2 : ℝ) := by
      exact_mod_cast w.card_sourceLocations_replacement_le hδ hb hpart
    _ ≤ (C_N * L ^ n) * (arity.choose 2 : ℝ) := mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg _)
    _ = (C_N * (arity.choose 2 : ℝ)) * L ^ n := by ring
    _ ≤ C_sources * L ^ n :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (zero_le_one.trans hL) _)

end OriginalCircuit

end QuantumCircuit.Party
