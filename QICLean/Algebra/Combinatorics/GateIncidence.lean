/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.NNReal.Basic
import Mathlib.Basic.Real.Basic

/-!
# Incidence of gates, parties and positions with two endpoints

A finite set of gates, each with a finite set of participating parties, and a type of
positions, each with an ordered pair of endpoint parties, are fixed. A set `S` of positions
touches the parties that are endpoints of its members, at most `2 |S|` of them. If every
party takes part in at most `b` gates, at most `2 b |S|` gates meet these parties.

The second half weights the gates meeting the endpoints of `S` by the square of the sum of
absolute coefficients of their labels, and the endpoint parties by the square of a dimension.
With coefficient sums at most `B ≥ 1` and dimensions at most `d ≥ 1`, the weighted count is at
most `(B ^ (4 b) d ^ 4) ^ |S|`.

These are finite incidence counts: the gates, parties and positions are arbitrary types.

The weighted form of the gate count is `Finset.sum_filter_not_disjoint_le`: if the weights
`w i ≥ 0` of the sets `D i`, `i ∈ s`, containing any given point sum to at most `g`, then the
weights of the sets meeting a set `S` sum to at most `g |S|`, since each such set contains a
point of `S`.

## Main definitions

* `GateIncidence.correctedParties`: the endpoints of a finite set of positions.
* `GateIncidence.incidentGates`: the gates in which a party takes part.
* `GateIncidence.gatesTouching`: the gates meeting a set of parties.
* `GateIncidence.correctedPositionChoiceCost`: the weighted count of label and entry choices
  at the gates and parties touched by a set of positions.

## Main results

* `Finset.sum_filter_not_disjoint_le`: the total weight of the sets meeting `S`.
* `GateIncidence.card_correctedParties_le`: at most `2 |S|` endpoints.
* `GateIncidence.card_gatesTouching_correctedParties_le`: at most `2 b |S|` gates.
* `GateIncidence.correctedPositionChoiceCost_le`: the bound `(B ^ (4 b) d ^ 4) ^ |S|`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), Theorem 5.2 (`thm:compression`), paragraph "Expansion by corrected
  positions", `04-compression.tex:342–381`, `eq:compression-subset-expansion` and
  `eq:compression-choice-cost`.
* Arad, Kuwahara and Landau, arXiv:1406.3898, proof of Lemma `lem:Hadamard-bound`,
  `low70.tex`, lines 860–868.
-/

open scoped BigOperators NNReal

namespace Finset

variable {ι V : Type*} [DecidableEq V]

/-- If the weights `w i ≥ 0` of the sets `D i`, `i ∈ s`, through every point sum to at most
`g`, then the weights of the sets meeting `S` sum to at most `g |S|`. AKL14, arXiv:1406.3898,
proof of `lem:Hadamard-bound`, `low70.tex`, lines 860–868. -/
theorem sum_filter_not_disjoint_le {s : Finset ι} (D : ι → Finset V) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) {g : ℝ} (hg : ∀ x : V, ∑ i ∈ s with x ∈ D i, w i ≤ g)
    (S : Finset V) :
    ∑ i ∈ s with ¬Disjoint (D i) S, w i ≤ g * S.card := by
  classical
  calc
    ∑ i ∈ s with ¬Disjoint (D i) S, w i ≤
        ∑ i ∈ s with ¬Disjoint (D i) S, ∑ x ∈ S, if x ∈ D i then w i else 0 := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      obtain ⟨x, hxD, hxS⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hi).2
      calc
        w i = if x ∈ D i then w i else 0 := (ite_eq_left hxD).symm
        _ ≤ _ := Finset.single_le_sum (f := fun x ↦ if x ∈ D i then w i else 0)
          (fun y _ ↦ by split_ifs <;> simp [hw i]) hxS
    _ = ∑ x ∈ S, ∑ i ∈ s with ¬Disjoint (D i) S, if x ∈ D i then w i else 0 :=
      Finset.sum_comm
    _ ≤ ∑ x ∈ S, ∑ i ∈ s, if x ∈ D i then w i else 0 := by
      refine Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) fun i _ _ ↦ ?_
      split_ifs <;> simp [hw i]
    _ ≤ ∑ _x ∈ S, g := Finset.sum_le_sum fun x _ ↦ by rw [← Finset.sum_filter]; exact hg x
    _ = g * S.card := by simp [mul_comm]

end Finset

namespace GateIncidence

variable {Party Gate Position : Type*} [DecidableEq Party]

/-- The two endpoints of a position, counted once when they coincide.
Theorem 5.2, corrected-position expansion, `04-compression.tex:342–360`. -/
def sourceEndpoints (endpoints : Position → Party × Party) (e : Position) : Finset Party :=
  {(endpoints e).1, (endpoints e).2}

/-- The parties that are endpoints of a member of `S`; `S` is a set of positions, without
labels. Theorem 5.2, `04-compression.tex:342–360`. -/
def correctedParties (endpoints : Position → Party × Party) (S : Finset Position) :
    Finset Party :=
  S.biUnion (sourceEndpoints endpoints)

/-- The gates of `gates` in which the party `p` takes part. Theorem 5.2,
`04-compression.tex:133–151,356–364`. -/
def incidentGates (gates : Finset Gate) (participants : Gate → Finset Party) (p : Party) :
    Finset Gate :=
  gates.filter fun g ↦ p ∈ participants g

/-- The gates of `gates` meeting the party set `A`. Theorem 5.2,
`04-compression.tex:356–364`. -/
def gatesTouching [DecidableEq Gate] (gates : Finset Gate) (participants : Gate → Finset Party)
    (A : Finset Party) : Finset Gate :=
  A.biUnion (incidentGates gates participants)

/-- Membership in the endpoints of a position. Theorem 5.2, `04-compression.tex:356–360`. -/
@[simp] theorem mem_sourceEndpoints (endpoints : Position → Party × Party) (e : Position)
    (p : Party) :
    p ∈ sourceEndpoints endpoints e ↔ p = (endpoints e).1 ∨ p = (endpoints e).2 := by
  simp [sourceEndpoints]

/-- Membership in the endpoints of a set of positions. Theorem 5.2,
`eq:compression-subset-expansion`, `04-compression.tex:342–360`. -/
@[simp] theorem mem_correctedParties (endpoints : Position → Party × Party)
    (S : Finset Position) (p : Party) :
    p ∈ correctedParties endpoints S ↔ ∃ e ∈ S, p = (endpoints e).1 ∨ p = (endpoints e).2 := by
  simp [correctedParties]

/-- Membership in the gates of a party. Theorem 5.2, `04-compression.tex:133–151,356–364`. -/
@[simp] theorem mem_incidentGates (gates : Finset Gate) (participants : Gate → Finset Party)
    (p : Party) (g : Gate) :
    g ∈ incidentGates gates participants p ↔ g ∈ gates ∧ p ∈ participants g := by
  simp [incidentGates]

/-- A gate meets `A` exactly when one of its participants lies in `A`. Theorem 5.2,
`04-compression.tex:356–364`. -/
theorem mem_gatesTouching [DecidableEq Gate] (gates : Finset Gate)
    (participants : Gate → Finset Party) (A : Finset Party) (g : Gate) :
    g ∈ gatesTouching gates participants A ↔ g ∈ gates ∧ ∃ p ∈ A, p ∈ participants g := by
  simp only [gatesTouching, Finset.mem_biUnion, mem_incidentGates]
  exact ⟨fun ⟨p, hp, hg, hpg⟩ ↦ ⟨hg, p, hp, hpg⟩, fun ⟨hg, p, hp, hpg⟩ ↦ ⟨p, hp, hg, hpg⟩⟩

/-- A position has at most two endpoints. Theorem 5.2, `04-compression.tex:356–360`. -/
theorem card_sourceEndpoints_le (endpoints : Position → Party × Party) (e : Position) :
    (sourceEndpoints endpoints e).card ≤ 2 :=
  Finset.card_le_two

/-- A set `S` of positions has at most `2 |S|` endpoints. Theorem 5.2,
`04-compression.tex:356–360`. -/
theorem card_correctedParties_le (endpoints : Position → Party × Party)
    (S : Finset Position) :
    (correctedParties endpoints S).card ≤ 2 * S.card := by
  simpa [correctedParties, Nat.mul_comm] using
    Finset.card_biUnion_le_card_mul S (sourceEndpoints endpoints) 2
      fun e _ ↦ card_sourceEndpoints_le endpoints e

/-- If every party of `A` takes part in at most `b` gates, at most `b |A|` gates meet `A`.
Theorem 5.2, `04-compression.tex:356–364`. -/
theorem card_gatesTouching_le [DecidableEq Gate] (gates : Finset Gate)
    (participants : Gate → Finset Party) (A : Finset Party) (b : ℕ)
    (hlifetime : ∀ p ∈ A, (incidentGates gates participants p).card ≤ b) :
    (gatesTouching gates participants A).card ≤ b * A.card := by
  simpa [gatesTouching, Nat.mul_comm] using
    Finset.card_biUnion_le_card_mul A (incidentGates gates participants) b hlifetime

/-- If every endpoint of `S` takes part in at most `b` gates, at most `2 b |S|` gates meet the
endpoints of `S`. Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex:356–372`. -/
theorem card_gatesTouching_correctedParties_le [DecidableEq Gate] (gates : Finset Gate)
    (participants : Gate → Finset Party) (endpoints : Position → Party × Party)
    (S : Finset Position) (b : ℕ)
    (hlifetime : ∀ p ∈ correctedParties endpoints S,
      (incidentGates gates participants p).card ≤ b) :
    (gatesTouching gates participants (correctedParties endpoints S)).card ≤
      2 * b * S.card :=
  calc
    _ ≤ b * (correctedParties endpoints S).card :=
      card_gatesTouching_le gates participants _ b hlifetime
    _ ≤ b * (2 * S.card) := Nat.mul_le_mul_left b (card_correctedParties_le endpoints S)
    _ = 2 * b * S.card := by ac_rfl

/-- The gate `owner e` of a member `e` of `S` meets the endpoints of `S` when it lies in
`gates` and the first endpoint of `e` takes part in it. Theorem 5.2,
`04-compression.tex:342–364`. -/
theorem owner_mem_gatesTouching_correctedParties [DecidableEq Gate] (gates : Finset Gate)
    (participants : Gate → Finset Party) (endpoints : Position → Party × Party)
    (owner : Position → Gate) (S : Finset Position) {e : Position} (he : e ∈ S)
    (howner : owner e ∈ gates) (hparticipant : (endpoints e).1 ∈ participants (owner e)) :
    owner e ∈ gatesTouching gates participants (correctedParties endpoints S) :=
  (mem_gatesTouching _ _ _ _).2
    ⟨howner, (endpoints e).1, (mem_correctedParties _ _ _).2 ⟨e, he, Or.inl rfl⟩,
      hparticipant⟩

/-- A gate of `gates` not meeting `A` has no participant in `A`. Theorem 5.2,
`04-compression.tex:356–381`. -/
theorem disjoint_participants_of_not_mem_gatesTouching [DecidableEq Gate]
    (gates : Finset Gate) (participants : Gate → Finset Party) (A : Finset Party) {g : Gate}
    (hg : g ∈ gates) (hnot : g ∉ gatesTouching gates participants A) :
    Disjoint (participants g) A :=
  Finset.disjoint_left.2 fun p hpg hpA ↦
    hnot ((mem_gatesTouching _ _ _ _).2 ⟨hg, p, hpA, hpg⟩)

/-! ### Weighted choices at the gates and parties touched by a set of positions -/

section Cost

variable {Label : Type*}

/-- The square `(∑_ξ c_ξ)²` of the sum of the absolute coefficients `c_ξ` of a family of
labels: the weight of a choice of a ket and a bra label at one gate. Theorem 5.2,
`eq:compression-choice-cost`, `04-compression.tex:365–373`. -/
def ketBraCoefficientCost (labels : Finset Label) (coeff : Label → ℝ≥0) : ℝ≥0 :=
  (∑ ξ ∈ labels, coeff ξ) ^ 2

/-- The weight of a choice of two labels is the sum over pairs of labels of the products of
their coefficients. Theorem 5.2, `04-compression.tex:365–373`. -/
theorem ketBraCoefficientCost_eq_sum (labels : Finset Label) (coeff : Label → ℝ≥0) :
    ketBraCoefficientCost labels coeff = ∑ ξ ∈ labels, ∑ ζ ∈ labels, coeff ξ * coeff ζ := by
  rw [ketBraCoefficientCost, pow_two, Finset.sum_mul_sum]

/-- The weighted count of label and entry choices for a set `S` of positions: the product of
`ketBraCoefficientCost` over the gates meeting the endpoints of `S`, times the product of
`d_p ^ 2` over these endpoints. Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex:356–381`. -/
def correctedPositionChoiceCost [DecidableEq Gate] (gates : Finset Gate)
    (participants : Gate → Finset Party) (endpoints : Position → Party × Party)
    (S : Finset Position) {Labels : Gate → Type*} (labels : ∀ g, Finset (Labels g))
    (coeff : ∀ g, Labels g → ℝ≥0) (physicalDim : Party → ℕ) : ℝ≥0 :=
  (∏ g ∈ gatesTouching gates participants (correctedParties endpoints S),
    ketBraCoefficientCost (labels g) (coeff g)) *
    ∏ p ∈ correctedParties endpoints S, (physicalDim p : ℝ≥0) ^ 2

/-- With at most `b` gates at every endpoint of `S`, coefficient sums at most `B ≥ 1` at the
gates meeting these endpoints and dimensions at most `d ≥ 1` at the endpoints, the weighted
count of choices is at most `(B ^ (4 b) d ^ 4) ^ |S|`. Theorem 5.2,
`eq:compression-choice-cost`, `04-compression.tex:356–381`. -/
theorem correctedPositionChoiceCost_le [DecidableEq Gate] (gates : Finset Gate)
    (participants : Gate → Finset Party) (endpoints : Position → Party × Party)
    (S : Finset Position) {Labels : Gate → Type*} (labels : ∀ g, Finset (Labels g))
    (coeff : ∀ g, Labels g → ℝ≥0) (physicalDim : Party → ℕ) (b : ℕ) (B d : ℝ≥0)
    (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hlifetime : ∀ p ∈ correctedParties endpoints S,
      (incidentGates gates participants p).card ≤ b)
    (hcoeff : ∀ g ∈ gatesTouching gates participants (correctedParties endpoints S),
      ∑ ξ ∈ labels g, coeff g ξ ≤ B)
    (hphysical : ∀ p ∈ correctedParties endpoints S, (physicalDim p : ℝ≥0) ≤ d) :
    correctedPositionChoiceCost gates participants endpoints S labels coeff physicalDim ≤
      (B ^ (4 * b) * d ^ 4) ^ S.card := by
  set A := correctedParties endpoints S
  set G := gatesTouching gates participants A
  have hgateExponent : 2 * G.card ≤ 4 * b * S.card := by
    simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left 2
      (card_gatesTouching_correctedParties_le gates participants endpoints S b hlifetime)
  have hpartyExponent : 2 * A.card ≤ 4 * S.card := by
    simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left 2
      (card_correctedParties_le endpoints S)
  have hgateCost : (∏ g ∈ G, ketBraCoefficientCost (labels g) (coeff g)) ≤
      B ^ (4 * b * S.card) :=
    calc
      _ ≤ (B ^ 2) ^ G.card :=
        Finset.prod_le_pow_card G _ _ fun g hg ↦ pow_le_pow_left' (hcoeff g hg) 2
      _ = B ^ (2 * G.card) := (pow_mul B 2 G.card).symm
      _ ≤ B ^ (4 * b * S.card) := pow_le_pow_right' hB hgateExponent
  have hpartyCost : (∏ p ∈ A, (physicalDim p : ℝ≥0) ^ 2) ≤ d ^ (4 * S.card) :=
    calc
      _ ≤ (d ^ 2) ^ A.card :=
        Finset.prod_le_pow_card A _ _ fun p hp ↦ pow_le_pow_left' (hphysical p hp) 2
      _ = d ^ (2 * A.card) := (pow_mul d 2 A.card).symm
      _ ≤ d ^ (4 * S.card) := pow_le_pow_right' hd hpartyExponent
  calc
    _ ≤ B ^ (4 * b * S.card) * d ^ (4 * S.card) := mul_le_mul' hgateCost hpartyCost
    _ = (B ^ (4 * b) * d ^ 4) ^ S.card := by
      rw [pow_mul B (4 * b) S.card, pow_mul d 4 S.card, mul_pow]

end Cost

/-- Monomial bounds `B ≤ C L ^ a` and `d ≤ D L ^ c` give the monomial bound
`B ^ (4 b) d ^ 4 ≤ C ^ (4 b) D ^ 4 L ^ (4 b a + 4 c)`, whose exponent does not depend on `L`.
Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex:365–381`. -/
theorem compressionChoiceBase_le_of_monomial_bounds (L B d C D : ℝ≥0) (a c b : ℕ)
    (hB : B ≤ C * L ^ a) (hd : d ≤ D * L ^ c) :
    B ^ (4 * b) * d ^ 4 ≤ (C ^ (4 * b) * D ^ 4) * L ^ (4 * b * a + 4 * c) :=
  calc
    _ ≤ (C * L ^ a) ^ (4 * b) * (D * L ^ c) ^ 4 :=
      mul_le_mul' (pow_le_pow_left' hB _) (pow_le_pow_left' hd _)
    _ = (C ^ (4 * b) * D ^ 4) * L ^ (4 * b * a + 4 * c) := by
      rw [mul_pow C (L ^ a) (4 * b), mul_pow D (L ^ c) 4, ← pow_mul L a (4 * b),
        ← pow_mul L c 4, pow_add, Nat.mul_comm a (4 * b), Nat.mul_comm c 4]
      exact mul_mul_mul_comm _ _ _ _

end GateIncidence
