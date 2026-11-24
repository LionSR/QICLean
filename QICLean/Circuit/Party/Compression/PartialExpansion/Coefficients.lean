/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Choices

/-!
# The coefficients of a partial expansion

The coefficient of a choice of the partial expansion of a source circuit along affected parties
is the product of the branch coefficients at the touched gate occurrences
(`SourceCircuit.coefficient_eq_prod_dite`). The total absolute coefficient
`∑_ξ |c_ξ|` is therefore the product, over the touched occurrences, of the absolute coefficient
sums of their gates (`SourceCircuit.sum_norm_coefficient_eq_prod`): a touched gate contributes
its absolute coefficient sum, an untouched gate the factor one, and a composition the product.
A bound on every touched gate gives one factor of the bound per touched occurrence, and two
factors for the ket–bra coefficients `c_ξ c̄_ζ`. For the expansion along all parties, the
coefficients are products over the occurrences with a nonempty cell.

## Main results

* `QuantumCircuit.Party.SourceCircuit.sum_norm_coefficient_eq_prod`,
  `QuantumCircuit.Party.SourceCircuit.sum_norm_coefficient_le_pow_card`,
  `QuantumCircuit.Party.SourceCircuit.sum_norm_coefficient_mul_conj_le_pow_card`.
* `QuantumCircuit.Party.SourceCircuit.coefficient_eq_prod_dite`,
  `QuantumCircuit.Party.SourceCircuit.coefficient_all_eq_prod_nonemptyGateLocations`,
  `QuantumCircuit.Party.SourceCircuit.sum_coefficient_all_mul_conj_smul_eq_sum_nonemptyGateLabels`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, equation
  `eq:compression-choice-cost`, `04-compression.tex`, lines 351–381 and 565–573.

Adapted from TNLean, `TNLean/Lattice/Compression/SourceChoiceCost.lean`,
`TNLean/Lattice/Compression/SourceCircuitChoiceProduct.lean` and
`TNLean/Lattice/Compression/PointwiseChoiceCoefficient.lean` at commit `a05f5d6d0a`
(Apache-2.0). Changes: the frame case is stated on `PartyCircuit.frame`; the swap case is gone;
a case for local operations at every party is added.
-/

open scoped ComplexConjugate

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace SourceCircuit

variable (A : P → Bool) {X Y Z : P → Type}

/-! ### The absolute coefficient sum on the constructors -/

/-- A touched gate contributes the sum of the absolute values of its coefficients, zero for an
empty branch type. Source: Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex`,
lines 351–381. -/
theorem sum_norm_coefficient_gate_of_touches [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (h : PreparedGate.IsTouched A D) :
    ∑ ξ, ‖coefficient A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ‖ =
      ∑ ξ, ‖g.coeff ξ‖ := by
  let e : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y) ≃ g.ι :=
    Equiv.cast (ite_eq_left h)
  refine Fintype.sum_equiv e _ _ fun ξ ↦ ?_
  simp only [coefficient_gate, dite_eq_left h]
  rfl

/-- An untouched gate has one choice, with coefficient one, also for an empty branch type.
Source: Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex`, lines 351–417. -/
theorem sum_norm_coefficient_gate_of_exterior [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (h : ¬ PreparedGate.IsTouched A D) :
    ∑ ξ, ‖coefficient A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ‖ = 1 := by
  let e : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y) ≃ Unit :=
    Equiv.cast (ite_eq_right h)
  refine (Fintype.sum_equiv e _ (fun _ ↦ (1 : ℝ)) fun ξ ↦ ?_).trans (by simp)
  simp only [coefficient_gate, dite_eq_right h, norm_one]

/-- Independent choices in a composition multiply the absolute coefficient sums.
Source: Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (w : SourceCircuit X Y) (w' : SourceCircuit Y Z) :
    ∑ ξ, ‖coefficient A (PartyCircuit.comp w w') ξ‖ =
      (∑ ξ, ‖coefficient A w ξ‖) * ∑ ξ, ‖coefficient A w' ξ‖ := by
  change ∑ ξ : Choices A w × Choices A w', ‖coefficient A w ξ.1 * coefficient A w' ξ.2‖ = _
  simp only [norm_mul, Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- The empty circuit has one choice with coefficient one.
Source: Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_done :
    ∑ ξ, ‖coefficient A (PartyCircuit.done X : SourceCircuit X X) ξ‖ = 1 := by
  change ∑ _ : Unit, ‖(1 : ℂ)‖ = 1
  simp

/-- A local operation contributes no coefficient.
Source: Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_localOp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (p : P)
    (hY : ∀ s ≠ p, Y s = X s) (U : Matrix (Y p) (X p) ℂ) :
    ∑ ξ, ‖coefficient A (PartyCircuit.localOp p hY U : SourceCircuit X Y) ξ‖ = 1 := by
  change ∑ _ : Unit, ‖(1 : ℂ)‖ = 1
  simp

/-- Local operations at every party contribute no coefficient. -/
theorem sum_norm_coefficient_localOps [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (U : ∀ p, Matrix (Y p) (X p) ℂ) :
    ∑ ξ, ‖coefficient A (PartyCircuit.localOps U : SourceCircuit X Y) ξ‖ = 1 := by
  change ∑ _ : Unit, ‖(1 : ℂ)‖ = 1
  simp

/-- Spectator factors change neither the choices nor their coefficients.
Source: Theorem 5.2, `04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_frame (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (w : SourceCircuit X Y) :
    ∑ ξ, ‖coefficient A (w.frame W) ξ‖ = ∑ ξ, ‖coefficient A w ξ‖ :=
  Fintype.sum_equiv (choicesFrameEquiv A W w) _ _ fun ξ ↦ by rw [coefficient_frame]

/-! ### Products over the touched occurrences -/

/-- The total absolute coefficient as a product over all occurrences, with factor one at the
untouched ones. -/
private theorem sum_norm_coefficient_eq_prod_ite : {X Y : P → Type} → (w : SourceCircuit X Y) →
    ∑ ξ, ‖coefficient A w ξ‖ =
      ∏ g : w.gateLocations,
        if IsTouched A w g then ∑ ξ, ‖w.branchCoefficient g ξ‖ else 1
  | _, _, PartyCircuit.done _ => sum_norm_coefficient_done A
  | _, _, PartyCircuit.gate D hY g => by
    refine Eq.trans ?_ (Fintype.prod_unique (ι := Unit) _).symm
    by_cases h : PreparedGate.IsTouched A D
    · rw [sum_norm_coefficient_gate_of_touches A D hY g h]
      exact (ite_eq_left (α := ℝ) h).symm
    · rw [sum_norm_coefficient_gate_of_exterior A D hY g h]
      exact (ite_eq_right (α := ℝ) h).symm
  | _, _, PartyCircuit.localOp p hY U => sum_norm_coefficient_localOp A p hY U
  | _, _, PartyCircuit.localOps U => sum_norm_coefficient_localOps A U
  | _, _, PartyCircuit.comp c c' => by
    rw [sum_norm_coefficient_comp, sum_norm_coefficient_eq_prod_ite c,
      sum_norm_coefficient_eq_prod_ite c']
    exact (Fintype.prod_sum_type fun g : (PartyCircuit.comp c c').gateLocations ↦
      if IsTouched A (PartyCircuit.comp c c') g then
        ∑ ξ, ‖branchCoefficient (PartyCircuit.comp c c') g ξ‖ else 1).symm

/-- **The total absolute coefficient factors over the touched occurrences.** Repeated uses of
one gate are separate factors; untouched gates contribute no factor. Source: Theorem 5.2,
`eq:compression-choice-cost`, `04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_eq_prod (w : SourceCircuit X Y) :
    ∑ ξ, ‖coefficient A w ξ‖ =
      ∏ g ∈ Finset.univ.filter (IsTouched A w), ∑ ξ, ‖w.branchCoefficient g ξ‖ := by
  rw [Finset.prod_filter]
  exact sum_norm_coefficient_eq_prod_ite A w

/-- A bound on the absolute coefficient sum of every touched gate gives one factor of the bound
per touched occurrence. Source: Theorem 5.2, `eq:compression-choice-cost`,
`04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_le_pow_card (w : SourceCircuit X Y) (B : ℝ)
    (hB : ∀ g, IsTouched A w g → ∑ ξ, ‖w.branchCoefficient g ξ‖ ≤ B) :
    ∑ ξ, ‖coefficient A w ξ‖ ≤ B ^ (Finset.univ.filter (IsTouched A w)).card := by
  rw [sum_norm_coefficient_eq_prod]
  calc
    _ ≤ ∏ _g ∈ Finset.univ.filter (IsTouched A w), B :=
      Finset.prod_le_prod₀ (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
        fun g hg ↦ hB g (Finset.mem_filter.mp hg).2
    _ = _ := Finset.prod_const B

/-- The ket–bra coefficients `c_ξ c̄_ζ` have total absolute value the square of the product of
the absolute coefficient sums of the touched gates. Source: Theorem 5.2,
`eq:compression-choice-cost`, `04-compression.tex`, lines 351–381. -/
theorem sum_norm_coefficient_mul_conj_eq_prod_sq (w : SourceCircuit X Y) :
    ∑ ξ, ∑ ζ, ‖coefficient A w ξ * star (coefficient A w ζ)‖ =
      (∏ g ∈ Finset.univ.filter (IsTouched A w), ∑ ξ, ‖w.branchCoefficient g ξ‖) ^ 2 := by
  simp only [norm_mul, norm_star, ← Finset.sum_mul_sum]
  rw [← pow_two, sum_norm_coefficient_eq_prod]

/-- The ket–bra coefficients cost two factors of the bound per touched occurrence; untouched
gates cost nothing. Source: Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex`,
lines 351–381. -/
theorem sum_norm_coefficient_mul_conj_le_pow_card (w : SourceCircuit X Y) (B : ℝ)
    (hB : ∀ g, IsTouched A w g → ∑ ξ, ‖w.branchCoefficient g ξ‖ ≤ B) :
    ∑ ξ, ∑ ζ, ‖coefficient A w ξ * star (coefficient A w ζ)‖ ≤
      B ^ (2 * (Finset.univ.filter (IsTouched A w)).card) := by
  calc
    _ = (∑ ξ, ‖coefficient A w ξ‖) ^ 2 := by
      simp only [norm_mul, norm_star, ← Finset.sum_mul_sum, pow_two]
    _ ≤ (B ^ (Finset.univ.filter (IsTouched A w)).card) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
        (sum_norm_coefficient_le_pow_card A w B hB) 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

/-! ### Coefficients as products over occurrences -/

/-- **The coefficient of a choice is the product of the branch coefficients at the touched
occurrences.** Source: `04-compression.tex`, lines 351–381 and 565–573. -/
theorem coefficient_eq_prod_dite : {X Y : P → Type} → (w : SourceCircuit X Y) →
    (ξ : Choices A w) →
      coefficient A w ξ = ∏ g : w.gateLocations,
        if hg : IsTouched A w g then w.branchCoefficient g (choiceAt A w ξ g hg) else 1
  | _, _, PartyCircuit.done _, _ => rfl
  | _, _, PartyCircuit.gate D hY g, ξ =>
    (Fintype.prod_unique (ι := Unit) fun o ↦
      let w : SourceCircuit _ _ := PartyCircuit.gate D hY g
      let o' : w.gateLocations := o
      if hg : IsTouched A w o' then branchCoefficient w o' (choiceAt A w ξ o' hg) else 1).symm
  | _, _, PartyCircuit.localOp _ _ _, _ => rfl
  | _, _, PartyCircuit.localOps _, _ => rfl
  | _, _, PartyCircuit.comp c c', ξ => by
    rw [coefficient_comp, coefficient_eq_prod_dite c ξ.1, coefficient_eq_prod_dite c' ξ.2]
    exact (Fintype.prod_sum_type fun g : (PartyCircuit.comp c c').gateLocations ↦
      if hg : IsTouched A (PartyCircuit.comp c c') g then
        branchCoefficient (PartyCircuit.comp c c') g
          (choiceAt A (PartyCircuit.comp c c') ξ g hg) else 1).symm

/-- The coefficient of a choice of the expansion along all parties is the product of the branch
coefficients at the occurrences with a nonempty cell; a gate with an empty cell is kept as a
scalar instead. Source: `04-compression.tex`, lines 351–381 and 565–573. -/
theorem coefficient_all_eq_prod_nonemptyGateLocations (w : SourceCircuit X Y)
    (ξ : Choices (fun _ ↦ true) w) :
    coefficient (fun _ ↦ true) w ξ = ∏ g : w.nonemptyGateLocations,
      w.branchCoefficient g.1 (allChoicesNonemptyLabelsEquiv w ξ g) := by
  let F := fun g : w.gateLocations ↦
    if hg : IsTouched (fun _ ↦ true) w g then
      w.branchCoefficient g (choiceAt (fun _ ↦ true) w ξ g hg) else 1
  calc
    coefficient (fun _ ↦ true) w ξ = ∏ g : w.gateLocations, F g :=
      coefficient_eq_prod_dite (fun _ ↦ true) w ξ
    _ = ∏ g ∈ Finset.univ.filter fun g ↦ (w.participants g).Nonempty, F g := by
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl fun g _ ↦ ?_
      by_cases hg : (w.participants g).Nonempty
      · rw [ite_eq_left hg]
      · rw [ite_eq_right hg]
        exact dite_eq_right fun h ↦ hg ((isTouched_all_iff w g).mp h)
    _ = ∏ g : w.nonemptyGateLocations, F g.1 :=
      Finset.prod_subtype _ (fun _ ↦ by simp) F
    _ = _ := Finset.prod_congr rfl fun g _ ↦ dite_eq_left ((isTouched_all_iff w g.1).mpr g.2)

/-- The mixed coefficient `c_ξ c̄_ζ` of two choices along all parties is the product of the
mixed branch coefficients at the occurrences with a nonempty cell. Source: Theorem 5.2,
`04-compression.tex`, lines 351–381 and 565–573. -/
theorem coefficient_all_mul_conj_eq_prod_nonemptyGateLocations (w : SourceCircuit X Y)
    (ξ ζ : Choices (fun _ ↦ true) w) :
    coefficient (fun _ ↦ true) w ξ * conj (coefficient (fun _ ↦ true) w ζ) =
      ∏ g : w.nonemptyGateLocations,
        w.branchCoefficient g.1 (allChoicesNonemptyLabelsEquiv w ξ g) *
          conj (w.branchCoefficient g.1 (allChoicesNonemptyLabelsEquiv w ζ g)) := by
  rw [coefficient_all_eq_prod_nonemptyGateLocations w ξ,
    coefficient_all_eq_prod_nonemptyGateLocations w ζ, map_prod, Finset.prod_mul_distrib]

open Classical in
/-- The double sum over two choices along all parties, reindexed by the label functions at the
occurrences with a nonempty cell, with the mixed coefficient written as a product over these
occurrences; the matrix summand is arbitrary. Source: Theorem 5.2, `04-compression.tex`,
lines 351–381 and 565–573. -/
theorem sum_coefficient_all_mul_conj_smul_eq_sum_nonemptyGateLabels (w : SourceCircuit X Y)
    {m n : Type} (K : Choices (fun _ ↦ true) w → Choices (fun _ ↦ true) w → Matrix m n ℂ) :
    ∑ ξ, ∑ ζ, (coefficient (fun _ ↦ true) w ξ * conj (coefficient (fun _ ↦ true) w ζ)) •
        K ξ ζ =
      ∑ η : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
        ∑ θ : (g : w.nonemptyGateLocations) → w.branchLabels g.1,
          (∏ g : w.nonemptyGateLocations,
            w.branchCoefficient g.1 (η g) * conj (w.branchCoefficient g.1 (θ g))) •
              K ((allChoicesNonemptyLabelsEquiv w).symm η)
                ((allChoicesNonemptyLabelsEquiv w).symm θ) := by
  simp_rw [coefficient_all_mul_conj_eq_prod_nonemptyGateLocations]
  refine Fintype.sum_equiv (allChoicesNonemptyLabelsEquiv w) _ _ fun ξ ↦ ?_
  refine Fintype.sum_equiv (allChoicesNonemptyLabelsEquiv w) _ _ fun ζ ↦ ?_
  simp only [Equiv.symm_apply_apply]

end SourceCircuit

end QuantumCircuit.Party
