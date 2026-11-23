/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Monomial.EffectChain
import QICLean.Analysis.Norm.ApproximateContractionRescaling

/-!
# Elimination of normalized pair effects

A monomial of a gate expansion is a composition of contractions, preparations of normalized
pair vectors, and contractions by normalized pair bras (pair effects).  Grouping the steps
between consecutive effects, a monomial with `n` effects is a chain
`F_n E_n F_{n-1} ⋯ E_1 F_0`, where each `F_i` is a contraction and each `E_i = ⟨η_i| ⊗ 1`
contracts a pair register with a normalized pair vector `η_i` and leaves a spectator register
untouched.  Such chains, `EffectChain`, their replacement and the telescoping bound for one
monomial are defined and proved in `QICLean.Circuit.Party.Monomial.EffectChain`, on finite
basis types and matrices with the operator norm.

Each effect occurrence receives its own output stack of `m` pair registers.  In the replaced
monomial the effect `⟨η|` is replaced by the cyclic insertion `T_m`, and the stack stays idle
afterwards.  The ideal replacement appends the fixed vector `η^{⊗ m}`.  For a whole gate
expansion `G = ∑_ξ c_ξ M_ξ`, every monomial is given the stacks of all effect occurrences of
all monomials: those of other monomials are prepared as the fixed vectors `η^{⊗ m}`.  All
branches therefore have the same additional output register `inventory m L`, and the ideal
additional output is the common normalized vector `Γ_m = ⨂_o η_o^{⊗ m}`.

Telescoping the at most `r` replacements in one monomial gives the error `r / √m`, and summing
with the original coefficients gives `‖G'_m - G ⊗ |Γ_m⟩‖ ≤ (r / √m) ∑_ξ |c_ξ|`.  Expanding the
averages over insertion positions writes `G'_m` as a weighted sum of at most `K m^r`
contractions, with unchanged absolute coefficient sum.

The model here has no parties: the effect-free pieces `F_i` of an `EffectChain` are arbitrary
contractions.  The statements of Lemma 5.1 about parties (the expansion of `G'_m` uses only
local contractions and normalized pair sources, its additional registers are owned by the
original participating parties, and all sources on one pair of parties combine into one) are
statements about party circuits and are not treated here; the effect chains of such
monomials are the `EffectChain`s of `QICLean.Circuit.Party.Monomial.EffectChain`.  The
combination of two normalized pair vectors into one is `EuclideanSpace.norm_pairCombine`.

## Main definitions

* `QuantumCircuit.Party.GateExpansion` : a weighted list of monomials.
* `QuantumCircuit.Party.GateExpansion.inventory`, `inventoryVector` : the common stack
  registers and the common garbage vector `Γ_m` of a gate expansion.
* `QuantumCircuit.Party.GateExpansion.replaceGate` : the replaced gate `G'_m`.
* `QuantumCircuit.Party.GateExpansion.termList` : the expansion of `G'_m` into weighted
  contractions.
* `QuantumCircuit.Party.stackLength` : a choice of `m` from `r`, the coefficient sum and the
  target error.

## Main results

* `QuantumCircuit.Party.EffectChain.replace_eq_sum` : expansion of a replaced monomial.
* `QuantumCircuit.Party.GateExpansion.norm_replaceGate_sub_le` : the gate error
  `(r / √m) ∑_ξ |c_ξ|`.
* `QuantumCircuit.Party.GateExpansion.replaceGate_eq_sum_termList`, `length_termList_le`,
  `sum_norm_coeff_termList`, `norm_term_le_one` : the expansion of `G'_m`, its count `K m^r`,
  its absolute coefficient sum and contractivity of its terms.
* `QuantumCircuit.Party.pairEffectElimination` : the error, count and coefficient-sum clauses
  of Lemma 5.1 `lem:effects`.
* `QuantumCircuit.Party.GateExpansion.replaceGate_rescaled`, `replaceGate_rescaled_stackLength`
  : near-contractivity and rescaling, also at the stack length chosen for a target error.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 21–127; choice of `m` and rescaling, lines 199–212.

Adapted from TNLean, `TNLean/Lattice/PartyCircuit/PairEffectElimination.lean` at commit
`ded76a266d` (Apache-2.0).  Changes: operators are matrices on finite basis types with the
operator norm; the inventory is a product of basis types; appending a vector and the
reassociation and exchange of tensor factors become `appendVector` and
`Matrix.reindex` along `Equiv.prodAssoc` and `prodPrependEquiv`; the definitions about one gate
expansion are in the namespace `GateExpansion`.
-/

noncomputable section

open scoped InnerProductSpace Kronecker Matrix.Norms.L2Operator
open Matrix EuclideanSpace CyclicInsertion

namespace QuantumCircuit.Party

namespace EffectChain

variable {Y : Type} [Fintype Y] [DecidableEq Y]

/-- **Expansion of a replaced monomial.** Expanding the averages over insertion positions
writes the replaced monomial with `n` effects as the average of the `m^n` terms `replaceTerm`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 121–125. -/
theorem replace_eq_sum (m : ℕ) : {X : Type} → (M : EffectChain X Y) →
    M.replace m = ∑ κ, ((m : ℂ) ^ M.effectCount)⁻¹ • M.replaceTerm m κ
  | _, final F => by
      simp only [replace, Finset.univ_unique, pow_zero, inv_one, replaceTerm, one_smul,
        Finset.sum_const, Finset.card_singleton]
  | _, effect α β S F η rest => by
      have hl : ∀ (s : Finset (Fin rest.effectCount → Fin m))
          (g : (Fin rest.effectCount → Fin m) → Matrix (Y × rest.stackIndex m) S ℂ),
          (1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ) ⊗ₖ (∑ κ ∈ s, g κ) =
            ∑ κ ∈ s, (1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ) ⊗ₖ g κ := fun s g =>
        map_sum (kroneckerBilinear (R := ℂ) (1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ)) g s
      have hr : ∀ (s : Finset (Fin m)) (g : Fin m → Matrix (Fin m → α × β) (α × β) ℂ),
          (∑ k ∈ s, g k) ⊗ₖ (1 : Matrix S S ℂ) = ∑ k ∈ s, g k ⊗ₖ (1 : Matrix S S ℂ) :=
        fun s g => map_sum ((kroneckerBilinear (R := ℂ)).flip (1 : Matrix S S ℂ)) g s
      rw [replace, replace_eq_sum m rest, cyclicInsertionMatrix_eq_sum, hl, hr]
      simp only [kronecker_smul, smul_kronecker, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
        Matrix.mul_smul, ← coe_reindexLinearEquiv ℂ ℂ, map_sum, map_smul, smul_smul,
        replaceTerm, Finset.smul_sum]
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (rest.effectCount + 1) => Fin m),
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun κ _ => ?_
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.tail_cons, Fin.cons_zero, effectCount,
        pow_succ, mul_inv, mul_comm]

end EffectChain

/-! ### Gate expansions with a common stack inventory -/

/-- The regrouping `((y, i), t) ↦ (y, (t, i))` that puts a new stack `t` in front of an
inventory `i`. -/
def prodPrependEquiv (Y I T : Type*) : (Y × I) × T ≃ Y × (T × I) :=
  (Equiv.prodAssoc Y I T).trans ((Equiv.refl Y).prodCongr (Equiv.prodComm I T))

/-- A gate expansion `G = ∑_ξ c_ξ M_ξ`: a finite list of coefficients and monomials.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`,
lines 55–57. -/
abbrev GateExpansion (X Y : Type) : Type 1 := List (ℂ × EffectChain X Y)

namespace GateExpansion

variable {X Y : Type}

/-- The gate `∑_ξ c_ξ M_ξ` of an expansion. -/
def gate : GateExpansion X Y → Matrix Y X ℂ
  | [] => 0
  | p :: L => p.1 • p.2.eval + gate L

/-- The gate of an expansion is the weighted sum of the matrices of its monomials. -/
theorem gate_eq_sum : (L : GateExpansion X Y) → gate L = (L.map fun p => p.1 • p.2.eval).sum
  | [] => rfl
  | p :: L => by simp only [gate, List.map_cons, List.sum_cons, gate_eq_sum L]

/-- The common stack inventory of a gate expansion: the stacks of every effect occurrence of
every monomial, indexed by the monomial and the position of the occurrence in it. -/
@[reducible] def inventory (m : ℕ) : GateExpansion X Y → Type
  | [] => Unit
  | p :: L => p.2.stackIndex m × inventory m L

/-- The inventory is a finite type. -/
instance instFintypeInventory (m : ℕ) : (L : GateExpansion X Y) → Fintype (inventory m L)
  | [] => inferInstanceAs (Fintype Unit)
  | p :: L =>
      haveI := instFintypeInventory m L
      inferInstanceAs (Fintype (p.2.stackIndex m × inventory m L))

/-- The inventory has decidable equality. -/
instance instDecidableEqInventory (m : ℕ) :
    (L : GateExpansion X Y) → DecidableEq (inventory m L)
  | [] => inferInstanceAs (DecidableEq Unit)
  | p :: L =>
      haveI := instDecidableEqInventory m L
      inferInstanceAs (DecidableEq (p.2.stackIndex m × inventory m L))

/-- The common normalized garbage vector `Γ_m = ⨂_o η_o^{⊗ m}`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 105–112. -/
def inventoryVector (m : ℕ) : (L : GateExpansion X Y) → EuclideanSpace ℂ (inventory m L)
  | [] => EuclideanSpace.single () 1
  | p :: L => vecKron (p.2.stackVector m) (inventoryVector m L)

/-- The garbage vector of a gate expansion of allowed monomials is a unit vector. -/
theorem norm_inventoryVector [Fintype X] [DecidableEq X] [Fintype Y] (m : ℕ) :
    (L : GateExpansion X Y) → (∀ p ∈ L, p.2.IsAllowed) → ‖inventoryVector m L‖ = 1
  | [], _ => by simp [inventoryVector]
  | p :: L, hL => by
      simp only [inventoryVector]
      rw [norm_vecKron, p.2.norm_stackVector m (hL p List.mem_cons_self),
        norm_inventoryVector m L fun q hq => hL q (List.mem_cons_of_mem _ hq), one_mul]

variable [Fintype Y] [DecidableEq Y]

/-- The replaced gate `G'_m`: in the branch of each monomial its effect occurrences are
replaced by cyclic insertions, and the stacks of all other monomials are prepared as their
fixed vectors `η^{⊗ m}`.  Every branch has the same output register `Y × inventory m L`.

Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 5.1, `04-compression.tex`,
lines 100–115. -/
def replaceGate (m : ℕ) : (L : GateExpansion X Y) → Matrix (Y × inventory m L) X ℂ
  | [] => 0
  | p :: L =>
      p.1 • reindex (Equiv.prodAssoc _ _ _) (Equiv.refl X)
          (appendVector (Y × p.2.stackIndex m) (inventoryVector m L) * p.2.replace m) +
        reindex (prodPrependEquiv _ _ _)
          (Equiv.refl X) (appendVector (Y × inventory m L) (p.2.stackVector m) * replaceGate m L)

/-- The expansion of the replaced gate into terms with their coefficients: the term of a
monomial `c M` with `n` effects and insertion positions `κ` has coefficient `c / m^n`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 121–125. -/
def termList (m : ℕ) :
    (L : GateExpansion X Y) → List (ℂ × Matrix (Y × inventory m L) X ℂ)
  | [] => []
  | p :: L =>
      (Finset.univ.toList.map fun κ => (p.1 * ((m : ℂ) ^ p.2.effectCount)⁻¹,
        reindex (Equiv.prodAssoc _ _ _) (Equiv.refl X)
          (appendVector (Y × p.2.stackIndex m) (inventoryVector m L) * p.2.replaceTerm m κ))) ++
      (termList m L).map fun q => (q.1,
        reindex (prodPrependEquiv _ _ _)
          (Equiv.refl X) (appendVector (Y × inventory m L) (p.2.stackVector m) * q.2))

/-- **Expansion of the replaced gate** into the weighted terms of `termList`. -/
theorem replaceGate_eq_sum_termList (m : ℕ) : (L : GateExpansion X Y) →
    replaceGate m L = ((termList m L).map fun q => q.1 • q.2).sum
  | [] => rfl
  | p :: L => by
      simp only [replaceGate, termList, List.map_append, List.sum_append, List.map_map]
      congr 1
      · rw [p.2.replace_eq_sum m]
        simp only [Matrix.mul_sum, Matrix.mul_smul, ← coe_reindexLinearEquiv ℂ ℂ, map_sum,
          map_smul, Finset.smul_sum, smul_smul]
        rw [← Finset.sum_map_toList]
        rfl
      · have key : ∀ l : List (ℂ × Matrix (Y × inventory m L) X ℂ),
            reindex (prodPrependEquiv _ _ _) (Equiv.refl X)
                (appendVector (Y × inventory m L) (p.2.stackVector m) *
                  (l.map fun q => q.1 • q.2).sum) =
              ((l.map fun q => (q.1, reindex (prodPrependEquiv _ _ _) (Equiv.refl X)
                (appendVector (Y × inventory m L) (p.2.stackVector m) * q.2))).map
                  fun q => q.1 • q.2).sum := by
          intro l
          induction l with
          | nil => simp
          | cons q l ih =>
              simp only [List.map_cons, List.sum_cons, ← ih]
              simp only [Matrix.mul_add, Matrix.mul_smul, ← coe_reindexLinearEquiv ℂ ℂ, map_add,
                map_smul]
        rw [replaceGate_eq_sum_termList m L, key, List.map_map]

/-- **Monomial count.** The expansion of `G'_m` has at most `K m^r` terms, where `K` is the
number of monomials of `G`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 65–66 and
120–124. -/
theorem length_termList_le {m r : ℕ} (hm : m ≠ 0) : (L : GateExpansion X Y) →
    (∀ p ∈ L, p.2.effectCount ≤ r) → (termList m L).length ≤ L.length * m ^ r
  | [], _ => by simp [termList]
  | p :: L, hL => by
      simp only [termList, List.length_append, List.length_map, Finset.length_toList,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, List.length_cons, add_mul,
        one_mul]
      rw [add_comm]
      exact add_le_add (length_termList_le hm L fun q hq => hL q (List.mem_cons_of_mem _ hq))
        (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hm) (hL p List.mem_cons_self))

/-- **Absolute coefficient sum.** The expansion of `G'_m` has the same absolute coefficient
sum `∑_ξ |c_ξ|` as the original expansion.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 66–67 and
121–123. -/
theorem sum_norm_coeff_termList {m : ℕ} (hm : m ≠ 0) : (L : GateExpansion X Y) →
    ((termList m L).map fun q => ‖q.1‖).sum = (L.map fun p => ‖p.1‖).sum
  | [] => rfl
  | p :: L => by
      simp only [termList, List.map_append, List.sum_append, List.map_map, List.map_cons,
        List.sum_cons]
      congr 1
      · rw [show ((fun q : ℂ × Matrix (Y × inventory m (p :: L)) X ℂ => ‖q.1‖) ∘ _) =
            fun _ => ‖p.1 * ((m : ℂ) ^ p.2.effectCount)⁻¹‖ from rfl, List.map_const',
          List.sum_replicate, Finset.length_toList, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
        have : ((m : ℝ) ^ p.2.effectCount) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm)
        push_cast
        field_simp
        simp only [Fintype.card_fin]
        ring
      · exact sum_norm_coeff_termList hm L

variable [Fintype X] [DecidableEq X]

/-- **Gate error.** If every monomial of `G = ∑_ξ c_ξ M_ξ` is allowed and has at most `r`
pair effects, then `‖G'_m - G ⊗ |Γ_m⟩‖ ≤ (r / √m) ∑_ξ |c_ξ|`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`, displayed
equation `eq:compression-effect-error`, `04-compression.tex`, lines 60–64 and 117–121. -/
theorem norm_replaceGate_sub_le {m : ℕ} (hm : m ≠ 0) {r : ℕ} :
    (L : GateExpansion X Y) → (∀ p ∈ L, p.2.IsAllowed ∧ p.2.effectCount ≤ r) →
    ‖replaceGate m L - appendVector Y (inventoryVector m L) * gate L‖ ≤
      r / Real.sqrt m * (L.map fun p => ‖p.1‖).sum
  | [], _ => by
      simp only [replaceGate, gate, Matrix.mul_zero, sub_self, norm_zero, List.map_nil,
        List.sum_nil, mul_zero, le_refl]
  | p :: L, hL => by
      obtain ⟨hpA, hpr⟩ := hL p List.mem_cons_self
      have hL' : ∀ q ∈ L, q.2.IsAllowed ∧ q.2.effectCount ≤ r :=
        fun q hq => hL q (List.mem_cons_of_mem _ hq)
      have ih := norm_replaceGate_sub_le hm L hL'
      have hGL : ‖inventoryVector m L‖ = 1 :=
        norm_inventoryVector m L fun q hq => (hL' q hq).1
      have e1 : appendVector Y (vecKron (p.2.stackVector m) (inventoryVector m L)) *
            (p.1 • p.2.eval) =
          p.1 • reindex (Equiv.prodAssoc _ _ _) (Equiv.refl X)
            (appendVector (Y × p.2.stackIndex m) (inventoryVector m L) *
              (appendVector Y (p.2.stackVector m) * p.2.eval)) := by
        ext ⟨y, s, i⟩ x
        simp only [appendVector_mul_apply, reindex_apply, Matrix.smul_apply, submatrix_apply,
          Equiv.refl_symm, Equiv.coe_refl, id_eq, Equiv.prodAssoc_symm_apply, vecKron,
          smul_eq_mul]
        ring
      have e2 : appendVector Y (vecKron (p.2.stackVector m) (inventoryVector m L)) * gate L =
          reindex (prodPrependEquiv _ _ _)
            (Equiv.refl X) (appendVector (Y × inventory m L) (p.2.stackVector m) *
              (appendVector Y (inventoryVector m L) * gate L)) := by
        ext ⟨y, s, i⟩ x
        simp only [appendVector_mul_apply, reindex_apply, submatrix_apply, Equiv.refl_symm,
          Equiv.coe_refl, id_eq, Equiv.symm_trans_apply, Equiv.prodCongr_symm,
          Equiv.prodCongr_apply, Prod.map, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap,
          Equiv.prodAssoc_symm_apply, vecKron, prodPrependEquiv]
        ring
      have hsplit : replaceGate m (p :: L) -
          appendVector Y (inventoryVector m (p :: L)) * gate (p :: L) =
          p.1 • reindex (Equiv.prodAssoc _ _ _) (Equiv.refl X)
            (appendVector (Y × p.2.stackIndex m) (inventoryVector m L) *
              (p.2.replace m - appendVector Y (p.2.stackVector m) * p.2.eval)) +
          reindex (prodPrependEquiv _ _ _)
            (Equiv.refl X)
            (appendVector (Y × inventory m L) (p.2.stackVector m) *
              (replaceGate m L - appendVector Y (inventoryVector m L) * gate L)) := by
        simp only [replaceGate, gate, inventoryVector, Matrix.mul_add]
        rw [e1, e2]
        simp only [reindex_apply, Matrix.mul_sub, submatrix_sub, Pi.sub_apply, smul_sub]
        abel
      rw [hsplit, List.map_cons, List.sum_cons, mul_add]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, mul_comm (r / Real.sqrt m)]
        gcongr
        refine (l2_opNorm_reindex_le _ _ _).trans <| (l2_opNorm_mul _ _).trans ?_
        calc _ ≤ 1 * (p.2.effectCount / Real.sqrt m) :=
              mul_le_mul ((norm_appendVector_le _).trans hGL.le) (p.2.norm_replace_sub_le hm hpA)
                (norm_nonneg _) zero_le_one
          _ ≤ _ := by
              rw [one_mul]
              exact div_le_div_of_nonneg_right (by exact_mod_cast hpr) (Real.sqrt_nonneg _)
      · refine (l2_opNorm_reindex_le _ _ _).trans <| (l2_opNorm_mul _ _).trans ?_
        calc _ ≤ 1 * ‖replaceGate m L - appendVector Y (inventoryVector m L) * gate L‖ :=
              mul_le_mul_of_nonneg_right
                ((norm_appendVector_le _).trans (p.2.norm_stackVector m hpA).le) (norm_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact ih

/-- Every term of the expansion of `G'_m` is a contraction. -/
theorem norm_term_le_one (m : ℕ) : (L : GateExpansion X Y) → (∀ p ∈ L, p.2.IsAllowed) →
    ∀ q ∈ termList m L, ‖q.2‖ ≤ 1
  | [], _ => by simp [termList]
  | p :: L, hL => by
      have hp := hL p List.mem_cons_self
      have hL' : ∀ q ∈ L, q.2.IsAllowed := fun q hq => hL q (List.mem_cons_of_mem _ hq)
      intro q hq
      simp only [termList, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨κ, _, rfl⟩ | ⟨q', hq', rfl⟩
      · exact (l2_opNorm_reindex_le _ _ _).trans <| l2_opNorm_mul_le_one _ _
          ((norm_appendVector_le _).trans (norm_inventoryVector m L hL').le)
          (p.2.norm_replaceTerm_le_one m hp κ)
      · exact (l2_opNorm_reindex_le _ _ _).trans <| l2_opNorm_mul_le_one _ _
          ((norm_appendVector_le _).trans (p.2.norm_stackVector m hp).le)
          (norm_term_le_one m L hL' q' hq')

end GateExpansion

open GateExpansion

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- **Elimination of normalized pair effects.** Let `G = ∑_ξ c_ξ M_ξ` be a gate expansion into
`K` allowed monomials, each with at most `r` normalized pair effects, and let `m ≥ 1`.  The
replaced gate `G'_m` and the common garbage vector `Γ_m` satisfy:

* `Γ_m` is normalized;
* `‖G'_m - G ⊗ |Γ_m⟩‖ ≤ (r / √m) ∑_ξ |c_ξ|`;
* `G'_m` is the weighted sum of the terms of `termList`;
* there are at most `K m^r` such terms;
* their absolute coefficient sum equals `∑_ξ |c_ξ|`;
* each term is a contraction.

These are the error, count and coefficient-sum clauses of the source lemma, the last one with
equality where the source states an upper bound; the clauses about parties are statements
about party circuits.

The hypothesis that `G` is a contraction is not needed here; it enters
`replaceGate_rescaled`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`,
`04-compression.tex`, lines 53–127. -/
theorem pairEffectElimination {m r : ℕ} (hm : m ≠ 0) (L : GateExpansion X Y)
    (hL : ∀ p ∈ L, p.2.IsAllowed ∧ p.2.effectCount ≤ r) :
    ‖inventoryVector m L‖ = 1 ∧
    ‖replaceGate m L - appendVector Y (inventoryVector m L) * gate L‖ ≤
      r / Real.sqrt m * (L.map fun p => ‖p.1‖).sum ∧
    replaceGate m L = ((termList m L).map fun q => q.1 • q.2).sum ∧
    (termList m L).length ≤ L.length * m ^ r ∧
    ((termList m L).map fun q => ‖q.1‖).sum = (L.map fun p => ‖p.1‖).sum ∧
    ∀ q ∈ termList m L, ‖q.2‖ ≤ 1 :=
  ⟨norm_inventoryVector m L fun p hp => (hL p hp).1, norm_replaceGate_sub_le hm L hL,
    replaceGate_eq_sum_termList m L, length_termList_le hm L fun p hp => (hL p hp).2,
    sum_norm_coeff_termList hm L, norm_term_le_one m L fun p hp => (hL p hp).1⟩

/-! ### Near-contractivity, rescaling and the choice of `m` -/

/-- A number `m ≥ 1` of stack registers achieving the target gate error `δ` for at most `r`
effects per monomial and absolute coefficient sum `S`: `m = ⌈(r S / δ)^2⌉ + 1`.  It is chosen
from the original coefficients, before the averages are expanded.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 201–208. -/
def stackLength (r : ℕ) (S δ : ℝ) : ℕ := ⌈(r * S / δ) ^ 2⌉₊ + 1

/-- The chosen stack length is positive. -/
theorem stackLength_ne_zero (r : ℕ) (S δ : ℝ) : stackLength r S δ ≠ 0 := Nat.succ_ne_zero _

/-- The stack length `stackLength r S δ` achieves the target error: `(r / √m) S ≤ δ`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 201–208. -/
theorem stackLength_spec (r : ℕ) {S δ : ℝ} (hS : 0 ≤ S) (hδ : 0 < δ) :
    r / Real.sqrt (stackLength r S δ) * S ≤ δ := by
  set N := stackLength r S δ
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (stackLength_ne_zero r S δ)
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hrS : 0 ≤ r * S / δ := by positivity
  have hle : r * S / δ ≤ Real.sqrt N := by
    rw [Real.le_sqrt hrS hN.le]
    calc (r * S / δ) ^ 2 ≤ ⌈(r * S / δ) ^ 2⌉₊ := Nat.le_ceil _
      _ ≤ N := by simp only [N, stackLength]; push_cast; linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hsq]
  calc (r : ℝ) * S = r * S / δ * δ := by field_simp
    _ ≤ Real.sqrt N * δ := by gcongr
    _ = δ * Real.sqrt N := mul_comm _ _

namespace GateExpansion

/-- **Near-contractivity and rescaling of the replaced gate.** If `G` is a contraction and
`δ ≥ (r / √m) ∑_ξ |c_ξ|`, then `G'_m` is within `δ` of `G ⊗ |Γ_m⟩`, `‖G'_m‖ ≤ 1 + δ`, and
`(1 + δ)⁻¹ G'_m` is a contraction within `2δ` of `G ⊗ |Γ_m⟩`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 210–212. -/
theorem replaceGate_rescaled {m r : ℕ} (hm : m ≠ 0) (L : GateExpansion X Y)
    (hL : ∀ p ∈ L, p.2.IsAllowed ∧ p.2.effectCount ≤ r) (hG : ‖gate L‖ ≤ 1) {δ : ℝ}
    (hδ : r / Real.sqrt m * (L.map fun p => ‖p.1‖).sum ≤ δ) :
    ‖replaceGate m L - appendVector Y (inventoryVector m L) * gate L‖ ≤ δ ∧
    ‖replaceGate m L‖ ≤ 1 + δ ∧
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m L‖ ≤ 1 ∧
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m L - appendVector Y (inventoryVector m L) * gate L‖ ≤
      2 * δ := by
  have hB : ‖appendVector Y (inventoryVector m L) * gate L‖ ≤ 1 :=
    l2_opNorm_mul_le_one _ _ ((norm_appendVector_le _).trans
      (norm_inventoryVector m L fun p hp => (hL p hp).1).le) hG
  have h := (norm_replaceGate_sub_le hm L hL).trans hδ
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans h
  have hA := norm_le_one_add_of_norm_sub_le hB h
  exact ⟨h, hA, norm_inv_one_add_smul_le_one hδ0 hA,
    norm_inv_one_add_smul_sub_le hδ0 hB h⟩

/-- **Rescaling at the chosen stack length.** For a target error `δ > 0` and a bound
`S ≥ ∑_ξ |c_ξ|` on the original absolute coefficient sum, the stack length
`m = stackLength r S δ` makes `G'_m` lie within `δ` of `G ⊗ |Γ_m⟩` and `(1 + δ)⁻¹ G'_m` a
contraction within `2δ` of it.  The length `m` depends only on `r`, `S` and `δ`, not on the
expansion of `G'_m`.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 201–212. -/
theorem replaceGate_rescaled_stackLength {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    (L : GateExpansion X Y) (hL : ∀ p ∈ L, p.2.IsAllowed ∧ p.2.effectCount ≤ r)
    (hG : ‖gate L‖ ≤ 1) (hS : (L.map fun p => ‖p.1‖).sum ≤ S) :
    ‖replaceGate (stackLength r S δ) L -
        appendVector Y (inventoryVector (stackLength r S δ) L) * gate L‖ ≤ δ ∧
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate (stackLength r S δ) L‖ ≤ 1 ∧
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate (stackLength r S δ) L -
        appendVector Y (inventoryVector (stackLength r S δ) L) * gate L‖ ≤ 2 * δ := by
  have hsum : 0 ≤ (L.map fun p => ‖p.1‖).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have hle : r / Real.sqrt (stackLength r S δ) * (L.map fun p => ‖p.1‖).sum ≤ δ :=
    (mul_le_mul_of_nonneg_left hS (by positivity)).trans
      (stackLength_spec r (hsum.trans hS) hδ)
  obtain ⟨h1, -, h3, h4⟩ := replaceGate_rescaled (stackLength_ne_zero r S δ) L hL hG hle
  exact ⟨h1, h3, h4⟩

end GateExpansion

end QuantumCircuit.Party
