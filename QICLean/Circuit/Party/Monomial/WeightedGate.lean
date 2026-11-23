/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Monomial.Chain
import QICLean.Circuit.Party.Monomial.Elimination
import QICLean.Circuit.Party.Syntax.EffectCircuit

/-!
# Pair-effect elimination for weighted gates

This module proves the statements of Lemma 5.1 `lem:effects` about parties for a gate expansion
`G = ∑_ξ c_ξ M_ξ` into monomials on the parties of a cell `D` (the terms of a
`WeightedGate D X Y`): the replaced gate has an expansion into source-only words (local
contractions and normalized pair sources), and its additional registers are owned by the
endpoint parties of the eliminated effects.

The terms of the expansion become a `GateExpansion` of effect chains (`WeightedGate.toGate`),
so `QICLean.Circuit.Party.Monomial.Elimination` applies. In the replacement, the stack of an
effect occurrence on `(p, q)` consists of the fresh factors `Fin m → α` at `p` and `Fin m → β` at
`q` (`QICLean.Circuit.Party.Monomial.Stack`); the stacks of all monomials, in front of the output
system, form the output system `gateOut` of the replaced gate, whose configurations are those of
the output and the inventory of `replaceGate` (`gateEquiv`). This identifies the terms of the
expansion of the replaced gate with source-only words (`termList_toGate`), the common garbage
vector with a product of pair sources (`op_prepGate`), and the additional registers with the
stacks (`gateOut_of_forall_ne`, `card_gateOut`).

The last clause of Lemma 5.1, that all sources on one pair of parties combine into one normalized
pair source, is not treated here; for two pair vectors it is `EuclideanSpace.norm_pairCombine`.

The section *Rescaling* multiplies all coefficients of a weighted gate by `(1 + δ)⁻¹`, which
makes a gate of norm at most `1 + δ` a contraction.

## Main definitions

* `QuantumCircuit.Party.WeightedGate.toGate` : the gate expansion of effect chains.
* `QuantumCircuit.Party.WeightedGate.gateOut`, `gateEquiv` : the output system of the replaced
  gate and its identification with the output of `GateExpansion.replaceGate`.
* `QuantumCircuit.Party.WeightedGate.prepGate`, `wordList` : the preparation of the garbage vector
  and the expansion of the replaced gate into source-only words.
* `QuantumCircuit.Party.WeightedGate.rescale` : common rescaling of the coefficients.

## Main results

* `QuantumCircuit.Party.WeightedGate.termList_toGate` : the expansion of the replaced gate, term
  by term.
* `QuantumCircuit.Party.WeightedGate.op_prepGate` : the common garbage vector `Γ_m` is prepared by
  pair sources.
* `QuantumCircuit.Party.WeightedGate.gateOut_of_forall_ne`,
  `QuantumCircuit.Party.WeightedGate.card_gateOut` : the additional registers are owned by the
  endpoint parties of the effects.
* `QuantumCircuit.Party.WeightedGate.partyPairEffectElimination` : Lemma 5.1 `lem:effects`,
  except the clause on combining sources.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 21–127; proof of Theorem 5.2 `thm:compression`, lines 210–212 and
  590–598 (rescaling).
-/

noncomputable section

open Matrix ManyBody EuclideanSpace CyclicInsertion
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace WeightedGate

open GateExpansion

variable {D : Finset P} {A B : ↥D → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Fintype (B s)] [∀ s, DecidableEq (B s)]

/-! ### Gate expansions of monomials on parties -/

/-- The gate expansion of a weighted list of monomials: each monomial replaced by its effect
chain, with the same coefficient. -/
@[reducible] def toGate : List (ℂ × Monomial D A B) → GateExpansion (Config A) (Config B)
  | [] => []
  | t :: L => (t.1, t.2.toEffectChain) :: toGate L

/-- The gate expansion has one monomial for each term of the weighted gate. -/
theorem length_toGate : (L : List (ℂ × Monomial D A B)) → (toGate L).length = L.length
  | [] => rfl
  | _ :: L => by simp only [toGate, List.length_cons, length_toGate L]

/-- The gate expansion has the absolute values of the coefficients of the weighted gate. -/
theorem map_norm_toGate : (L : List (ℂ × Monomial D A B)) →
    (toGate L).map (fun p ↦ ‖p.1‖) = L.map fun t ↦ ‖t.1‖
  | [] => rfl
  | _ :: L => by simp only [toGate, List.map_cons, map_norm_toGate L]

/-- A term of the gate expansion is the effect chain of a term of the weighted gate. -/
theorem mem_toGate {L : List (ℂ × Monomial D A B)} {p : ℂ × EffectChain (Config A) (Config B)}
    (hp : p ∈ toGate L) : ∃ t ∈ L, p = (t.1, t.2.toEffectChain) := by
  induction L with
  | nil => simp [toGate] at hp
  | cons a L ih =>
      simp only [toGate, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨a, List.mem_cons_self, rfl⟩
      · obtain ⟨t, ht, rfl⟩ := ih hp
        exact ⟨t, List.mem_cons_of_mem _ ht, rfl⟩

/-- The gate of the expansion is the weighted sum of the operators of the monomials. -/
theorem gate_toGate (L : List (ℂ × Monomial D A B)) :
    gate (toGate L) = (L.map fun t ↦ t.1 • t.2.op chainEv).sum := by
  induction L with
  | nil => rfl
  | cons t L ih =>
      simp only [gate, List.map_cons, List.sum_cons, ih, Monomial.eval_toEffectChain]

/-- The matrix of a weighted gate is the gate of its expansion. -/
theorem ev_eq_gate_toGate {X Y : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (g : WeightedGate D X Y) (o : Unit) :
    WeightedGate.ev g o = gate (toGate g.terms) := by
  rw [gate_toGate]; rfl

/-- The effect chains of allowed monomials are allowed. -/
theorem isAllowed_toGate {L : List (ℂ × Monomial D A B)}
    (hL : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed) :
    ∀ p ∈ toGate L, p.2.IsAllowed := by
  intro p hp
  obtain ⟨t, ht, rfl⟩ := mem_toGate hp
  exact t.2.isAllowed_toEffectChain (hL t ht)

variable (m : ℕ)

/-- The output system of the replaced gate: the stacks of all effect occurrences of all
monomials in front of the output system of the gate. -/
@[reducible] def gateOut : List (ℂ × Monomial D A B) → (↥D → Type)
  | [] => B
  | t :: L => stackApp m t.2.chainEffects (gateOut L)

/-- The output systems are finite. -/
instance instFintypeGateOut : (L : List (ℂ × Monomial D A B)) → (s : ↥D) →
    Fintype (gateOut m L s)
  | [], s => inferInstanceAs (Fintype (B s))
  | t :: L, s =>
      haveI := instFintypeGateOut L
      inferInstanceAs (Fintype (stackApp m t.2.chainEffects (gateOut m L) s))

/-- The output systems have decidable equality. -/
instance instDecidableEqGateOut : (L : List (ℂ × Monomial D A B)) → (s : ↥D) →
    DecidableEq (gateOut m L s)
  | [], s => inferInstanceAs (DecidableEq (B s))
  | t :: L, s =>
      haveI := instDecidableEqGateOut L
      inferInstanceAs (DecidableEq (stackApp m t.2.chainEffects (gateOut m L) s))

/-- The identification of the configurations of the output system of the replaced gate with the
output `Config B × inventory` of `replaceGate`. -/
def gateEquiv : (L : List (ℂ × Monomial D A B)) →
    Config (gateOut m L) ≃ Config B × inventory m (toGate L)
  | [] => (Equiv.prodPUnit _).symm
  | t :: L => (t.2.stackEquiv m (gateOut m L)).trans
      (((gateEquiv L).prodCongr (Equiv.refl _)).trans (prodPrependEquiv _ _ _))

/-- A sum against an indicator collapses to the indicated term. -/
private theorem sum_ite_eq_mul {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι) (a : ℂ)
    (f : ι → ℂ) : ∑ j, (if c = j then a else 0) * f j = a * f c := by
  simp [ite_mul]

/-- Preparation of the common garbage vector `Γ_m` by pair sources: the stacks of the effects of
every monomial, in the order of the list. -/
def prepGate : (L : List (ℂ × Monomial D A B)) → Word B (gateOut m L)
  | [] => PartyCircuit.done B
  | t :: L => (prepGate L).comp (prepStack m t.2.chainEffects (gateOut m L))

/-- The preparation of the garbage vector of allowed monomials is an allowed word. -/
theorem isAllowed_prepGate : (L : List (ℂ × Monomial D A B)) →
    (∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed) → (prepGate m L).IsAllowed
  | [], _ => Word.isAllowed_done
  | t :: L, h => Word.IsAllowed.comp
      (isAllowed_prepGate L fun t' ht' ↦ h t' (List.mem_cons_of_mem _ ht'))
      (t.2.isAllowed_prepStack m _ (h t List.mem_cons_self))

/-- **The garbage vector is prepared by pair sources**: read along
`gateEquiv`, the word `prepGate` prepares the common garbage vector `Γ_m`. Source:
`04-compression.tex`, lines 103–112. -/
theorem op_prepGate (L : List (ℂ × Monomial D A B)) :
    (prepGate m L).op =
      reindex (gateEquiv m L).symm (Equiv.refl _)
        (prepMatrix (Equiv.prodComm (Config B) _) (inventoryVector m (toGate L))) := by
  induction L with
  | nil =>
    ext y x
    simp [prepGate, gateEquiv, inventoryVector, one_apply]
  | cons t L ih =>
    change Word.op ((prepGate m L).comp (prepStack m t.2.chainEffects (gateOut m L))) = _
    rw [Word.op_comp, Monomial.op_prepStack, ih, reindex_symm_prepMatrix, reindex_symm_prepMatrix,
      reindex_symm_prepMatrix]
    ext y x
    simp only [prepMatrix_mul_apply, prepMatrix_apply, Equiv.trans_apply, Equiv.prodComm_apply,
      Prod.fst_swap, Prod.snd_swap, gateEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      prodPrependEquiv, Equiv.prodAssoc_apply, inventoryVector, toGate, vecKron]
    split_ifs with h <;> simp [h]

/-- The expansion of the replaced gate into weighted source-only words: the term of a monomial
`c M` with `n` effects and insertion positions `κ` has coefficient `c / m^n`. Source: Lemma 5.1,
`04-compression.tex`, lines 65–67 and 103–125. -/
def wordList : (L : List (ℂ × Monomial D A B)) → List (ℂ × Word A (gateOut m L))
  | [] => []
  | t :: L =>
      (Finset.univ.toList.map fun κ ↦ (t.1 * ((m : ℂ) ^ t.2.toEffectChain.effectCount)⁻¹,
        (t.2.replaceWord m κ).comp (frameStack m t.2.chainEffects (prepGate m L)))) ++
      (wordList L).map fun q ↦ (q.1, q.2.comp (prepStack m t.2.chainEffects (gateOut m L)))

/-- **Each term of the replaced gate is source-only**: the expansion
`termList` of the replaced gate is, term by term, the expansion into the source-only words
`wordList`, read along `gateEquiv`. Source: Lemma 5.1, `04-compression.tex`, lines 65–66 and
103–125. -/
theorem termList_toGate (L : List (ℂ × Monomial D A B)) :
    termList m (toGate L) =
      (wordList m L).map fun q ↦ (q.1, reindex (gateEquiv m L) (Equiv.refl _) q.2.op) := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    simp only [toGate, termList, wordList, List.map_append, List.map_map, ih]
    congr 1
    · refine List.map_congr_left fun κ _ ↦ Prod.ext rfl ?_
      change _ = reindex (gateEquiv m (t :: L)) (Equiv.refl _)
        (Word.op ((t.2.replaceWord m κ).comp (frameStack m t.2.chainEffects (prepGate m L))))
      rw [Word.op_comp, op_frameStack, Monomial.op_replaceWord, op_prepGate,
        reindex_symm_prepMatrix]
      ext r x
      obtain ⟨y, rfl⟩ := (gateEquiv m (t :: L)).surjective r
      simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
        prepMatrix_prodComm_mul_apply]
      conv_rhs => rw [Matrix.mul_apply, ← (stackAppEquiv m t.2.chainEffects B).symm.sum_comp,
        Fintype.sum_prod_type]
      simp only [gateEquiv, Monomial.stackEquiv, prodPrependEquiv, Equiv.trans_apply,
        Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.prodAssoc_apply, Prod.map_fst, Prod.map_snd,
        id_eq, Equiv.coe_prodComm, Prod.map_apply, Prod.swap_prod_mk, Equiv.prodAssoc_symm_apply,
        Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm, submatrix_apply,
        Equiv.apply_symm_apply, kroneckerMap_apply, prepMatrix_apply, Equiv.prodComm_apply,
        Prod.snd_swap, Prod.fst_swap, one_apply, mul_ite, mul_one, mul_zero, Equiv.symm_trans,
        Equiv.coe_trans, Function.comp_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
      refine Eq.trans ?_ (sum_ite_eq_mul (ι := Config B) _ _ _).symm
      rfl
    · refine List.map_congr_left fun q _ ↦ Prod.ext rfl ?_
      change _ = reindex (gateEquiv m (t :: L)) (Equiv.refl _)
        (Word.op (q.2.comp (prepStack m t.2.chainEffects (gateOut m L))))
      rw [Word.op_comp, Monomial.op_prepStack]
      ext r x
      obtain ⟨y, rfl⟩ := (gateEquiv m (t :: L)).surjective r
      simp only [gateEquiv, Monomial.stackEquiv, prodPrependEquiv, reindex_apply,
        submatrix_apply, mul_apply, Equiv.trans_apply]
      simp only [Equiv.symm_trans, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodComm_symm,
        Equiv.coe_trans, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_prodComm,
        Function.comp_apply, Equiv.prodAssoc_apply, Prod.map_fst, Prod.map_snd, id_eq,
        Prod.map_apply, Prod.swap_prod_mk, submatrix_apply, Equiv.prodAssoc_symm_apply,
        Prod.mk.eta, prepMatrix_prodComm_mul_apply, Equiv.symm_apply_apply, Equiv.symm_symm,
        Equiv.trans_apply, Equiv.refl_apply, prepMatrix_apply, Equiv.prodComm_apply,
        Prod.snd_swap, Prod.fst_swap]
      refine Eq.trans ?_ (sum_ite_eq_mul (ι := Config (gateOut m L)) _ _ _).symm
      rfl

/-- The words of the expansion of the replaced gate of allowed monomials are allowed. -/
theorem isAllowed_wordList : (L : List (ℂ × Monomial D A B)) →
    (∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed) →
      ∀ q ∈ wordList m L, q.2.IsAllowed
  | [], _ => fun _ h ↦ absurd h List.not_mem_nil
  | t :: L, h => fun q hq ↦ by
    have ht := h t List.mem_cons_self
    have hL : ∀ t' ∈ L, t'.2.IsAllowed chainEv ChainGate.IsAllowed :=
      fun t' ht' ↦ h t' (List.mem_cons_of_mem _ ht')
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨κ, -, rfl⟩ := List.mem_map.mp hq
      exact Word.IsAllowed.comp (t.2.isAllowed_replaceWord m ht κ)
        (isAllowed_frameStack m _ _ (isAllowed_prepGate m L hL))
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
      exact Word.IsAllowed.comp (isAllowed_wordList L hL q' hq') (t.2.isAllowed_prepStack m _ ht)

/-- **Every term of the replaced gate is source-only**: read along `gateEquiv`, each term of
the expansion `termList` is the operator of an allowed source-only word. Source: Lemma 5.1,
`04-compression.tex`, lines 65–66. -/
theorem isSourceOnly_termList (L : List (ℂ × Monomial D A B))
    (hL : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed) :
    ∀ q ∈ termList m (toGate L),
      IsSourceOnly (reindex (gateEquiv m L).symm (Equiv.refl _) q.2) := by
  intro q hq
  rw [termList_toGate, List.mem_map] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  refine ⟨w.2, isAllowed_wordList m L hL w hw, ?_⟩
  simp only [reindex_apply, submatrix_submatrix, Equiv.symm_symm, Equiv.symm_comp_self,
    Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, submatrix_id_id]

/-- **Ownership of the additional registers**: at a party that is no endpoint of an effect of
any monomial, the output system of the replaced gate has the basis of `B`. Source: Lemma 5.1,
`04-compression.tex`, lines 67–68 and 100–103. -/
theorem gateOut_of_forall_ne {s : ↥D} : (L : List (ℂ × Monomial D A B)) →
    (∀ t ∈ L, ∀ e ∈ t.2.effectParties, s ≠ e.1 ∧ s ≠ e.2) →
    gateOut m L s = B s
  | [], _ => rfl
  | t :: L, h =>
      (t.2.stackApp_of_notMem_effectParties m _ (h t List.mem_cons_self)).trans
        (gateOut_of_forall_ne L fun t' ht' ↦ h t' (List.mem_cons_of_mem _ ht'))

/-- **Dimensions of the additional registers**: at a party `s`, the dimension of the output
system of the replaced gate is that of `B` multiplied, for every effect of every monomial, by
`|α|^m` if `s` is its first endpoint and by `|β|^m` if `s` is its second endpoint. Source:
Lemma 5.1, `04-compression.tex`, lines 67–68 and 100–103. -/
theorem card_gateOut (L : List (ℂ × Monomial D A B)) (s : ↥D) :
    Fintype.card (gateOut m L s) = Fintype.card (B s) *
      (L.map fun t ↦ (t.2.effects.map fun e ↦
        (if s = e.left then Fintype.card e.leftBasis ^ m else 1) *
          (if s = e.right then Fintype.card e.rightBasis ^ m else 1)).prod).prod := by
  induction L with
  | nil => simp [gateOut]
  | cons t L ih =>
    change Fintype.card (stackApp m t.2.chainEffects (gateOut m L) s) = _
    rw [card_stackApp, ih, t.2.chainEffects_eq, List.map_cons, List.prod_cons]
    ring

/-! ### Lemma 5.1 on parties -/

/-- **Elimination of normalized pair effects** (Lemma 5.1 `lem:effects`). Let
`G = ∑_ξ c_ξ M_ξ` be a gate expansion into `K` allowed monomials on the parties of `D`, each with
at most `r` pair effects, and let `m ≥ 1`. Then, with the replaced gate `G'_m = replaceGate` and
the common garbage vector `Γ_m = inventoryVector`:

* `Γ_m` is normalized and is prepared by the allowed source-only word `prepGate`;
* `‖G'_m - G ⊗ |Γ_m⟩‖ ≤ (r / √m) ∑_ξ |c_ξ|`;
* read along `gateEquiv`, `G'_m` is the weighted sum of the allowed source-only words of
  `wordList`; equivalently, every term of `termList` is source-only;
* there are at most `K m^r` such words, with absolute coefficient sum `∑_ξ |c_ξ|`;
* at every party that is no endpoint of an effect, the output system of `G'_m` is that of `G`:
  the additional registers are owned by the endpoint parties of the effects.

The clause that all sources on one pair of parties combine into one is not stated here. The
hypothesis that `G` is a contraction is not needed.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`,
`04-compression.tex`, lines 53–127. -/
theorem partyPairEffectElimination {m r : ℕ} (hm : m ≠ 0) (L : List (ℂ × Monomial D A B))
    (hL : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed ∧ t.2.effectCount ≤ r) :
    ‖inventoryVector m (toGate L)‖ = 1 ∧
    (prepGate m L).op = reindex (gateEquiv m L).symm (Equiv.refl _)
      (prepMatrix (Equiv.prodComm (Config B) _) (inventoryVector m (toGate L))) ∧
    (prepGate m L).IsAllowed ∧
    ‖replaceGate m (toGate L) -
        prepMatrix (Equiv.prodComm (Config B) _) (inventoryVector m (toGate L)) * gate (toGate L)‖ ≤
      r / Real.sqrt m * (L.map fun t ↦ ‖t.1‖).sum ∧
    replaceGate m (toGate L) =
      ((wordList m L).map fun q ↦ q.1 • reindex (gateEquiv m L) (Equiv.refl _) q.2.op).sum ∧
    (∀ q ∈ wordList m L, q.2.IsAllowed) ∧
    (∀ q ∈ termList m (toGate L),
      IsSourceOnly (reindex (gateEquiv m L).symm (Equiv.refl _) q.2)) ∧
    (wordList m L).length ≤ L.length * m ^ r ∧
    ((wordList m L).map fun q ↦ ‖q.1‖).sum = (L.map fun t ↦ ‖t.1‖).sum ∧
    ∀ s : ↥D, (∀ t ∈ L, ∀ e ∈ t.2.effectParties, s ≠ e.1 ∧ s ≠ e.2) → gateOut m L s = B s := by
  have hA : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed := fun t ht ↦ (hL t ht).1
  have hG : ∀ p ∈ toGate L, p.2.IsAllowed ∧ p.2.effectCount ≤ r := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := mem_toGate hp
    exact ⟨t.2.isAllowed_toEffectChain (hL t ht).1,
      (t.2.effectCount_toEffectChain).trans_le (hL t ht).2⟩
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := pairEffectElimination hm (toGate L) hG
  rw [termList_toGate] at h3 h4 h5
  rw [List.map_map] at h3 h5
  rw [List.length_map, length_toGate] at h4
  rw [map_norm_toGate] at h2 h5
  refine ⟨h1, op_prepGate m L, isAllowed_prepGate m L hA, h2, ?_, isAllowed_wordList m L hA,
    isSourceOnly_termList m L hA, h4, ?_, fun s hs ↦ gateOut_of_forall_ne m L hs⟩
  · rw [h3]; rfl
  · rw [← h5]; rfl

end WeightedGate

/-! ### Rescaling -/

namespace WeightedGate

variable {D : Finset P} {X Y : P → Type}

/-- Common coefficient rescaling of a weighted gate by `(1 + δ)⁻¹`; the monomials, their order
and their local operations are unchanged. Source: proof of Theorem 5.2 `thm:compression`,
`04-compression.tex`, lines 210–212 and 590–598. -/
def rescale (δ : ℝ) (g : WeightedGate D X Y) : WeightedGate D X Y :=
  ⟨g.terms.map fun t ↦ ((((1 + δ)⁻¹ : ℝ) : ℂ) * t.1, t.2)⟩

/-- Rescaling keeps the ordered list of monomials, with all their source and effect
occurrences. -/
theorem monomials_rescale (δ : ℝ) (g : WeightedGate D X Y) :
    (rescale δ g).terms.map Prod.snd = g.terms.map Prod.snd := by
  simp only [rescale, List.map_map, Function.comp_def]

/-- For `δ ≥ 0`, the absolute coefficient sum does not increase under the common
rescaling. -/
theorem sum_norm_rescale_le {δ : ℝ} (hδ : 0 ≤ δ) (g : WeightedGate D X Y) :
    ((rescale δ g).terms.map fun t ↦ ‖t.1‖).sum ≤ (g.terms.map fun t ↦ ‖t.1‖).sum := by
  simp only [rescale, List.map_map, Function.comp_def, norm_mul, List.sum_map_mul_left]
  have hc : ‖(((1 + δ)⁻¹ : ℝ) : ℂ)‖ ≤ 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (norm_inv_one_add_smul_le_one (A := (1 : ℂ)) hδ
        (by simpa only [norm_one] using (le_add_of_nonneg_right hδ : (1 : ℝ) ≤ 1 + δ)))
  exact (mul_le_mul_of_nonneg_right hc
    (List.sum_nonneg (fun x hx ↦ by
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
      exact norm_nonneg q.1))).trans_eq (one_mul _)

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

/-- The matrix of the rescaled gate is `(1 + δ)⁻¹` times the matrix of the gate. -/
theorem ev_rescale (δ : ℝ) (g : WeightedGate D X Y) (o : Unit) :
    WeightedGate.ev (rescale δ g) o = (((1 + δ)⁻¹ : ℝ) : ℂ) • WeightedGate.ev g o := by
  simp only [WeightedGate.ev, rescale, List.map_map, Function.comp_def, mul_smul]
  rw [List.smul_sum, List.map_map]
  rfl

/-- The gate of the expansion of the rescaled gate is `(1 + δ)⁻¹` times the gate of the
expansion. -/
theorem gate_toGate_rescale (δ : ℝ) (g : WeightedGate D X Y) :
    GateExpansion.gate (toGate (rescale δ g).terms) =
      (((1 + δ)⁻¹ : ℝ) : ℂ) • GateExpansion.gate (toGate g.terms) := by
  rw [← ev_eq_gate_toGate _ (), ← ev_eq_gate_toGate _ (), ev_rescale]

/-- The rescaled gate of an allowed weighted gate is allowed. -/
theorem isAllowed_rescale (δ : ℝ) {g : WeightedGate D X Y} (h : WeightedGate.IsAllowed g) :
    WeightedGate.IsAllowed (rescale δ g) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact h u hu

end WeightedGate

end QuantumCircuit.Party
