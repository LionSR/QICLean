/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.PreparedSourceGate
import QICLean.Circuit.Party.Monomial.WeightedGate

/-!
# The source-only replacement of one gate

Lemma 5.1 (`WeightedGate.partyPairEffectElimination`) turns a gate expansion
`G = ∑_ξ c_ξ M_ξ` into allowed monomials on a cell into a weighted sum of source-only words
with stacks of `m` pair registers per pair effect; the common source preparation
(`Word.exists_preparedSourceGate`) turns that sum into one prepared gate, and the
common rescaling `(1 + δ)⁻¹` makes it a contraction within `2δ` of `G` followed by the
preparation of the stacks (`exists_prepared_effectReplacement`). The stacks of the gate are its
auxiliary factors, party by party (`WeightedGate.auxFactor`, `auxFactorEquiv`), whose
configurations are the inventory of the replaced gate (`auxFactorConfigEquiv`).

## Main definitions

* `QuantumCircuit.Party.stackAux`, `stackAppSiteEquiv`, `stackAuxConfigEquiv` — the stacks of a
  list of pair effects, party by party.
* `QuantumCircuit.Party.WeightedGate.auxFactor`, `auxFactorEquiv`, `auxFactorConfigEquiv`,
  `replacementCoefficients`.

## Main results

* `QuantumCircuit.Party.WeightedGate.exists_prepared_effectReplacement` (`_native`,
  `_uniform`, `_relabel`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 199–212; Lemma 5.1, lines 53–127.
-/

noncomputable section

open Matrix ManyBody EuclideanSpace
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

open GateExpansion

/-! ### The stacks of a list of pair effects, party by party -/

section StackAux

variable {Q : Type} [Fintype Q] [DecidableEq Q] (m : ℕ)

/-- The stack factors of a list of pair effects at a party: for each effect `e` the fresh factor
`Fin m → α` at its first endpoint, `Fin m → β` at its second endpoint, `Unit` elsewhere. -/
def stackAux : List (PairSource Q) → Q → Type
  | [], _ => Unit
  | e :: es, s => pairFactor e.distinct (Fin m → e.leftBasis) (Fin m → e.rightBasis) s ×
      stackAux es s

/-- The stack factors are finite. -/
instance instFintypeStackAux : (es : List (PairSource Q)) → (s : Q) → Fintype (stackAux m es s)
  | [], _ => inferInstanceAs (Fintype Unit)
  | e :: es, s =>
    haveI := instFintypeStackAux es s
    inferInstanceAs (Fintype (pairFactor e.distinct (Fin m → e.leftBasis)
      (Fin m → e.rightBasis) s × stackAux m es s))

/-- The stack factors have decidable equality. -/
instance instDecidableEqStackAux : (es : List (PairSource Q)) → (s : Q) →
    DecidableEq (stackAux m es s)
  | [], _ => inferInstanceAs (DecidableEq Unit)
  | e :: es, s =>
    haveI := instDecidableEqStackAux es s
    inferInstanceAs (DecidableEq (pairFactor e.distinct (Fin m → e.leftBasis)
      (Fin m → e.rightBasis) s × stackAux m es s))

/-- The stacked basis of a party is its stack factors in front of its basis. -/
def stackAppSiteEquiv : (es : List (PairSource Q)) → (T : Q → Type) → (s : Q) →
    stackApp m es T s ≃ stackAux m es s × T s
  | [], T, s => (Equiv.punitProd (T s)).symm
  | e :: es, T, s =>
    (addPairSiteEquiv e.distinct (Fin m → e.leftBasis) (Fin m → e.rightBasis)
      (stackApp m es T) s).trans
      (((Equiv.refl _).prodCongr (stackAppSiteEquiv es T s)).trans (Equiv.prodAssoc _ _ _).symm)

/-- The configurations of the stack factors are the stack configurations of the effects. -/
def stackAuxConfigEquiv : (es : List (PairSource Q)) → Config (stackAux m es) ≃ stackIdx m es
  | [] => ⟨fun _ ↦ (), fun _ _ ↦ (), fun _ ↦ funext fun _ ↦ rfl, fun _ ↦ rfl⟩
  | e :: es =>
    (Equiv.arrowProdEquivProdArrow Q _ _).trans
      (((pairFactorConfigEquiv e.distinct (Fin m → e.leftBasis) (Fin m → e.rightBasis)).trans
        (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ ↦ e.leftBasis)
          (fun _ ↦ e.rightBasis)).symm).prodCongr (stackAuxConfigEquiv es))

omit [Fintype Q] in
/-- The configurations of the stacked system, read party by party: the stacked basis of every party
is its stack factors in front of its basis. -/
theorem stackAppEquiv_apply : (es : List (PairSource Q)) → (T : Q → Type) →
    (y : Config (stackApp m es T)) →
    stackAppEquiv m es T y = (fun s ↦ (stackAppSiteEquiv m es T s (y s)).2,
      stackAuxConfigEquiv m es fun s ↦ (stackAppSiteEquiv m es T s (y s)).1)
  | [], _, _ => rfl
  | e :: es, T, y => by
    have h := stackAppEquiv_apply es T
      ((addPairConfigEquiv (X := stackApp m es T) e.distinct (Fin m → e.leftBasis)
        (Fin m → e.rightBasis) y).2)
    change Equiv.prodLeftComm _ _ _ (((Equiv.arrowProdEquivProdArrow (Fin m) _ _).symm
        (addPairConfigEquiv e.distinct (Fin m → e.leftBasis) (Fin m → e.rightBasis) y).1),
      stackAppEquiv m es T (addPairConfigEquiv e.distinct (Fin m → e.leftBasis)
        (Fin m → e.rightBasis) y).2) = _
    rw [h]
    rw [addPairConfigEquiv_eq_siteEquiv]
    rfl

end StackAux

/-! ### The auxiliary factors of one replaced gate -/

namespace WeightedGate

variable {P : Type} [DecidableEq P] {D : Finset P} {A B : ↥D → Type}
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Fintype (B s)] [∀ s, DecidableEq (B s)]
  (m : ℕ)

/-- The auxiliary factors of the replaced gate at a party of the cell: the stack factors of all
effect occurrences of all monomials. -/
def auxFactor : List (ℂ × Monomial D A B) → ↥D → Type
  | [] => fun _ ↦ Unit
  | t :: L => fun s ↦ stackAux m t.2.chainEffects s × auxFactor L s

/-- The auxiliary factors of a replaced gate are finite. -/
instance instFintypeAuxFactor : (L : List (ℂ × Monomial D A B)) → (s : ↥D) →
    Fintype (auxFactor m L s)
  | [], _ => inferInstanceAs (Fintype Unit)
  | t :: L, s =>
    haveI := instFintypeAuxFactor L s
    inferInstanceAs (Fintype (stackAux m t.2.chainEffects s × auxFactor m L s))

/-- The auxiliary factors of a replaced gate have decidable equality. -/
instance instDecidableEqAuxFactor : (L : List (ℂ × Monomial D A B)) → (s : ↥D) →
    DecidableEq (auxFactor m L s)
  | [], _ => inferInstanceAs (DecidableEq Unit)
  | t :: L, s =>
    haveI := instDecidableEqAuxFactor L s
    inferInstanceAs (DecidableEq (stackAux m t.2.chainEffects s × auxFactor m L s))

/-- The output basis of the replaced gate at a party is its auxiliary factor in front of the output
basis of the gate. -/
def auxFactorEquiv : (L : List (ℂ × Monomial D A B)) → (s : ↥D) →
    gateOut m L s ≃ auxFactor m L s × B s
  | [], s => (Equiv.punitProd (B s)).symm
  | t :: L, s =>
    (stackAppSiteEquiv m t.2.chainEffects (gateOut m L) s).trans
      (((Equiv.refl _).prodCongr (auxFactorEquiv L s)).trans (Equiv.prodAssoc _ _ _).symm)

/-- The configurations of the auxiliary factors are the inventory of the replaced gate. -/
def auxFactorConfigEquiv : (L : List (ℂ × Monomial D A B)) →
    Config (auxFactor m L) ≃ inventory m (toGate L)
  | [] => ⟨fun _ ↦ (), fun _ _ ↦ (), fun _ ↦ funext fun _ ↦ rfl, fun _ ↦ rfl⟩
  | t :: L =>
    (Equiv.arrowProdEquivProdArrow ↥D _ _).trans
      (((stackAuxConfigEquiv m t.2.chainEffects).trans (t.2.chainForm.indexEquiv m).symm).prodCongr
        (auxFactorConfigEquiv L))

/-- One rescaling factor `(1 + δ)⁻¹` for every term of the replaced gate. Source:
`04-compression.tex`, lines 210–212. -/
def replacementCoefficients (δ : ℝ) (L : List (ℂ × Monomial D A B)) :
    Fin (wordList m L).length → ℂ :=
  fun i ↦ (((1 + δ)⁻¹ : ℝ) : ℂ) * ((wordList m L).get i).1

/-- **The output configurations of the replaced gate, read party by party**: at every party the
output basis is its auxiliary factor in front of the basis of the gate. -/
theorem gateEquiv_apply : (L : List (ℂ × Monomial D A B)) → (u : Config (gateOut m L)) →
    gateEquiv m L u = (fun s ↦ (auxFactorEquiv m L s (u s)).2,
      auxFactorConfigEquiv m L fun s ↦ (auxFactorEquiv m L s (u s)).1)
  | [], _ => rfl
  | t :: L, u => by
    have hA := stackAppEquiv_apply m t.2.chainEffects (gateOut m L) u
    have h := gateEquiv_apply L (stackAppEquiv m t.2.chainEffects (gateOut m L) u).1
    change prodPrependEquiv _ _ _ ((gateEquiv m L (stackAppEquiv m t.2.chainEffects
        (gateOut m L) u).1, (t.2.chainForm.indexEquiv m).symm
          (stackAppEquiv m t.2.chainEffects (gateOut m L) u).2)) = _
    rw [h, hA]
    rfl


/-! #### One replaced gate -/

variable {m}

/-- The weighted sum of the source-only words of the replaced gate: read along `gateEquiv` it is the
rescaled replaced gate, it is a contraction, and it is within `2 δ` of the gate followed by the
preparation of the stacks, in both readings. Source: `04-compression.tex`, lines 199–212. -/
private theorem wordSum_spec {r : ℕ} (hm : m ≠ 0) (L : List (ℂ × Monomial D A B))
    (hL : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed ∧ t.2.effectCount ≤ r)
    (hG : ‖gate (toGate L)‖ ≤ 1) {δ : ℝ}
    (hδ : r / Real.sqrt m * (L.map fun t ↦ ‖t.1‖).sum ≤ δ) :
    reindex (gateEquiv m L) (Equiv.refl _)
        (∑ i, replacementCoefficients m δ L i • ((wordList m L).get i).2.op) =
      (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m (toGate L) ∧
    ‖∑ i, replacementCoefficients m δ L i • ((wordList m L).get i).2.op‖ ≤ 1 ∧
    ‖(((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m (toGate L) -
        prepMatrix (Equiv.prodComm (Config B) _) (inventoryVector m (toGate L)) *
          gate (toGate L)‖ ≤ 2 * δ ∧
    ‖(∑ i, replacementCoefficients m δ L i • ((wordList m L).get i).2.op) -
        (prepGate m L).op * gate (toGate L)‖ ≤ 2 * δ := by
  have hLt : ∀ q ∈ toGate L, q.2.IsAllowed ∧ q.2.effectCount ≤ r := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_toGate hq
    exact ⟨t.2.isAllowed_toEffectChain (hL t ht).1,
      t.2.effectCount_toEffectChain.trans_le (hL t ht).2⟩
  have hδt : r / Real.sqrt m * ((toGate L).map fun q ↦ ‖q.1‖).sum ≤ δ := by
    rwa [map_norm_toGate]
  obtain ⟨-, -, hnorm, herror⟩ := GateExpansion.replaceGate_rescaled hm (toGate L) hLt hG hδt
  obtain ⟨-, -, -, -, h5, -⟩ := partyPairEffectElimination hm L hL
  set M := ∑ i, replacementCoefficients m δ L i • ((wordList m L).get i).2.op with hM
  have he : reindex (gateEquiv m L) (Equiv.refl _) M =
      (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m (toGate L) := by
    rw [h5, ← Fin.sum_univ_fun_getElem (wordList m L)
      fun q ↦ q.1 • reindex (gateEquiv m L) (Equiv.refl _) q.2.op, Finset.smul_sum, hM,
      ← coe_reindexLinearEquiv ℂ ℂ, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, coe_reindexLinearEquiv, replacementCoefficients, mul_smul, List.get_eq_getElem]
  have hback : ∀ N : Matrix (Config (gateOut m L)) (Config A) ℂ,
      N = reindex (gateEquiv m L).symm (Equiv.refl _) (reindex (gateEquiv m L) (Equiv.refl _) N) :=
    fun N ↦ by ext; simp
  refine ⟨he, ?_, herror, ?_⟩
  · rw [hback M, he]
    exact (l2_opNorm_reindex_le _ _ _).trans hnorm
  · have hmul : (prepGate m L).op * gate (toGate L) = reindex (gateEquiv m L).symm (Equiv.refl _)
        (prepMatrix (Equiv.prodComm (Config B) _) (inventoryVector m (toGate L)) *
          gate (toGate L)) := by
      rw [op_prepGate]
      ext
      simp [Matrix.mul_apply]
    have hsub : ∀ U V : Matrix (Config B × inventory m (toGate L)) (Config A) ℂ,
        reindex (gateEquiv m L).symm (Equiv.refl _) U -
          reindex (gateEquiv m L).symm (Equiv.refl _) V =
            reindex (gateEquiv m L).symm (Equiv.refl _) (U - V) :=
      fun U V ↦ by ext; simp
    rw [hmul, hback M, he, hsub]
    exact (l2_opNorm_reindex_le _ _ _).trans herror

/-- **The prepared gate of one effect expansion**: read along `gateEquiv`, it is the rescaled
replaced gate `(1 + δ)⁻¹ G'_m`, within `2δ` of the gate `G` followed by the preparation of `Γ_m`.
Source: `04-compression.tex`, lines 199–212. -/
theorem exists_prepared_effectReplacement {r : ℕ} (hm : m ≠ 0) (L : List (ℂ × Monomial D A B))
    (hL : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed ∧ t.2.effectCount ≤ r)
    (hG : ‖gate (toGate L)‖ ≤ 1) {δ : ℝ}
    (hδ : r / Real.sqrt m * (L.map fun t ↦ ‖t.1‖).sum ≤ δ) :
    ∃ G : PreparedSourceGate (replacementCoefficients m δ L) A (gateOut m L),
      reindex (gateEquiv m L) (Equiv.refl _) G.eval =
        (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m (toGate L) ∧
      ‖reindex (gateEquiv m L) (Equiv.refl _) G.eval -
        prepMatrix (Equiv.prodComm (Config B) _) (inventoryVector m (toGate L)) *
          gate (toGate L)‖ ≤ 2 * δ := by
  obtain ⟨he, hn, herr, -⟩ := wordSum_spec hm L hL hG hδ
  obtain ⟨G, hGe⟩ := Word.exists_preparedSourceGate (replacementCoefficients m δ L)
    (fun i ↦ ((wordList m L).get i).2)
    (fun i ↦ isAllowed_wordList m L (fun t ht ↦ (hL t ht).1) _ (List.get_mem _ _)) hn
  exact ⟨G, hGe ▸ he, hGe ▸ he ▸ herr⟩

/-- The prepared gate approximates the gate followed by the preparation word `prepGate` of its
stacks, in the output system of the replaced gate. Source: `04-compression.tex`, lines 199–212. -/
theorem exists_prepared_effectReplacement_native {r : ℕ} (hm : m ≠ 0)
    (L : List (ℂ × Monomial D A B))
    (hL : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed ∧ t.2.effectCount ≤ r)
    (hG : ‖gate (toGate L)‖ ≤ 1) {δ : ℝ}
    (hδ : r / Real.sqrt m * (L.map fun t ↦ ‖t.1‖).sum ≤ δ) :
    ∃ G : PreparedSourceGate (replacementCoefficients m δ L) A (gateOut m L),
      reindex (gateEquiv m L) (Equiv.refl _) G.eval =
        (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate m (toGate L) ∧
      ‖G.eval - (prepGate m L).op * gate (toGate L)‖ ≤ 2 * δ := by
  obtain ⟨he, hn, -, herr⟩ := wordSum_spec hm L hL hG hδ
  obtain ⟨G, hGe⟩ := Word.exists_preparedSourceGate (replacementCoefficients m δ L)
    (fun i ↦ ((wordList m L).get i).2)
    (fun i ↦ isAllowed_wordList m L (fun t ht ↦ (hL t ht).1) _ (List.get_mem _ _)) hn
  exact ⟨G, hGe ▸ he, hGe ▸ herr⟩

/-- The stack length is chosen from the effect and coefficient bounds. Source: `04-compression.tex`,
lines 199–212. -/
theorem exists_prepared_effectReplacement_uniform {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    (L : List (ℂ × Monomial D A B))
    (hL : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed ∧ t.2.effectCount ≤ r)
    (hG : ‖gate (toGate L)‖ ≤ 1) (hS : (L.map fun t ↦ ‖t.1‖).sum ≤ S) :
    ∃ G : PreparedSourceGate (replacementCoefficients (stackLength r S δ) δ L) A
        (gateOut (stackLength r S δ) L),
      reindex (gateEquiv (stackLength r S δ) L) (Equiv.refl _) G.eval =
        (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate (stackLength r S δ) (toGate L) ∧
      ‖G.eval - (prepGate (stackLength r S δ) L).op * gate (toGate L)‖ ≤ 2 * δ := by
  have hsum : 0 ≤ (L.map fun t ↦ ‖t.1‖).sum := List.sum_nonneg fun x hx ↦ by
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  have hle : r / Real.sqrt (stackLength r S δ) * (L.map fun t ↦ ‖t.1‖).sum ≤ δ :=
    (mul_le_mul_of_nonneg_left hS (by positivity)).trans
      (stackLength_spec r (hsum.trans hS) hδ)
  exact exists_prepared_effectReplacement_native (stackLength_ne_zero r S δ) L hL hG hle

/-- The same prepared gate with its output read along basis equivalences `e`, as needed on the
parties of a cell inside a larger system: its matrix is the relabelled weighted sum of the
source-only words, read back along `e` and `gateEquiv` it is the rescaled replaced gate `(1 + δ)⁻¹
G'_m`, and it is within `2δ` of the gate followed by the preparation of the stacks. Source:
`04-compression.tex`, lines 199–212. -/
theorem exists_prepared_effectReplacement_relabel {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    (L : List (ℂ × Monomial D A B))
    (hL : ∀ t ∈ L, t.2.IsAllowed chainEv ChainGate.IsAllowed ∧ t.2.effectCount ≤ r)
    (hG : ‖gate (toGate L)‖ ≤ 1) (hS : (L.map fun t ↦ ‖t.1‖).sum ≤ S) {B' : ↥D → Type}
    [∀ s, Fintype (B' s)] [∀ s, DecidableEq (B' s)]
    (e : ∀ s, B' s ≃ gateOut (stackLength r S δ) L s) :
    ∃ G : PreparedSourceGate (replacementCoefficients (stackLength r S δ) δ L) A B',
      G.eval = Word.op (PartyCircuit.relabel e) *
        ∑ i, replacementCoefficients (stackLength r S δ) δ L i •
          ((wordList (stackLength r S δ) L).get i).2.op ∧
      reindex (gateEquiv (stackLength r S δ) L) (Equiv.refl _)
          (reindex (Equiv.piCongrRight e) (Equiv.refl _) G.eval) =
        (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate (stackLength r S δ) (toGate L) ∧
      ‖reindex (Equiv.piCongrRight e) (Equiv.refl _) G.eval -
        (prepGate (stackLength r S δ) L).op * gate (toGate L)‖ ≤ 2 * δ := by
  have hsum : 0 ≤ (L.map fun t ↦ ‖t.1‖).sum := List.sum_nonneg fun x hx ↦ by
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact norm_nonneg _
  have hle : r / Real.sqrt (stackLength r S δ) * (L.map fun t ↦ ‖t.1‖).sum ≤ δ :=
    (mul_le_mul_of_nonneg_left hS (by positivity)).trans
      (stackLength_spec r (hsum.trans hS) hδ)
  obtain ⟨he, hn, -, herr⟩ := wordSum_spec (stackLength_ne_zero r S δ) L hL hG hle
  set M := ∑ i, replacementCoefficients (stackLength r S δ) δ L i •
    ((wordList (stackLength r S δ) L).get i).2.op with hM
  have hrel : Word.op (PartyCircuit.relabel e) * M = M.submatrix (Equiv.piCongrRight e) id :=
    PartyCircuit.op_relabel_mul _ e M
  have hnM : ‖Word.op (PartyCircuit.relabel e) * M‖ ≤ 1 := by
    rw [hrel]
    exact (l2_opNorm_reindex_le (Equiv.piCongrRight e).symm (Equiv.refl _) M).trans hn
  have hsumrel : ∑ i, replacementCoefficients (stackLength r S δ) δ L i •
      Word.op (((wordList (stackLength r S δ) L).get i).2.comp (PartyCircuit.relabel e)) =
        Word.op (PartyCircuit.relabel e) * M := by
    rw [hM, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Word.op_comp, Matrix.mul_smul]
  obtain ⟨G, hGe⟩ := Word.exists_preparedSourceGate
    (replacementCoefficients (stackLength r S δ) δ L)
    (fun i ↦ ((wordList (stackLength r S δ) L).get i).2.comp (PartyCircuit.relabel e))
    (fun i ↦ Word.IsAllowed.comp
      (isAllowed_wordList _ L (fun t ht ↦ (hL t ht).1) _ (List.get_mem _ _))
      (Word.isAllowed_relabel e))
    (hsumrel ▸ hnM)
  have hG' : G.eval = Word.op (PartyCircuit.relabel e) * M := hGe.trans hsumrel
  have hre : reindex (Equiv.piCongrRight e) (Equiv.refl _) G.eval = M := by
    rw [hG', hrel]
    ext
    simp
  exact ⟨G, hG', hre ▸ he, hre ▸ herr⟩

end WeightedGate

end QuantumCircuit.Party
