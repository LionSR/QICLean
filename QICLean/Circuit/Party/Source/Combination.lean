/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Word
import QICLean.Analysis.TensorProduct.CyclicInsertion
import QICLean.Analysis.Norm.KroneckerOperatorNorm
import QICLean.Analysis.Norm.L2OpNormReindex

/-!
# Combining and expanding pair sources on one pair of parties

Two pair sources `η'` and then `η` prepared on the same pair of parties, followed by merging the
two fresh factors of each party into one, are a single pair source of the combined vector
`η ⊗ η'` (`EuclideanSpace.pairCombine`), whose norm is `‖η‖ ‖η'‖` (`Word.op_combineSources`).
Conversely the combined source, followed by splitting the merged factors, is the two sources
(`Word.op_expandCombinedPair`). A source with its endpoints exchanged is the same source up to a
relabelling of the bases (`Word.op_relabel_sourceAt_reverse`), and two sources commute up to a
relabelling (`Word.op_relabel_sourceAt_swap`).

Merging two factors of a party, or exchanging them, is a relabelling of the basis of that party
(`PartyCircuit.relabel`): the bases are read through `addPairSiteEquiv`, as the fresh factors in
front of the existing basis, and the relabellings regroup the factors by `Equiv.prodAssoc` and
`Equiv.prodComm`.

## Main definitions

* `QuantumCircuit.Party.addPairAssocEquiv`, `QuantumCircuit.Party.addPairCommEquiv`,
  `QuantumCircuit.Party.addPairSwapEquiv` — relabellings of two pairs of fresh factors.
* `QuantumCircuit.Party.Word.combineSources`, `QuantumCircuit.Party.Word.expandCombinedPair`.

## Main results

* `QuantumCircuit.Party.Word.op_combineSources`, `QuantumCircuit.Party.Word.op_expandCombinedPair`
  — combining two sources on one pair, and splitting the combined source.
* `QuantumCircuit.Party.Word.op_relabel_sourceAt_reverse`,
  `QuantumCircuit.Party.Word.op_relabel_sourceAt_swap` — reversed and exchanged sources.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 68–70 and 125–127; Theorem 5.2, `eq:compression-source-gate`,
  lines 246–251.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type}

/-! ### Relabellings of `addPair` -/

section equivs

variable [DecidableEq P] {X : P → Type} {p q : P} (hpq : p ≠ q)

/-- The fresh factors of two pairs on the same endpoints, merged: `α × α'` at `p`, `β × β'` at
`q`, one basis vector elsewhere. -/
def pairFactorProdEquiv (α β α' β' : Type) (s : P) :
    pairFactor hpq α β s × pairFactor hpq α' β' s ≃ pairFactor hpq (α × α') (β × β') s :=
  if hp : s = p then
    ((Equiv.cast (show pairFactor hpq α β s = α by simp [pairFactor, hp])).prodCongr
      (Equiv.cast (show pairFactor hpq α' β' s = α' by simp [pairFactor, hp]))).trans
      (Equiv.cast (show (α × α') = pairFactor hpq (α × α') (β × β') s by simp [pairFactor, hp]))
  else if hq : s = q then
    ((Equiv.cast (show pairFactor hpq α β s = β by simp [pairFactor, hq, hpq.symm])).prodCongr
      (Equiv.cast (show pairFactor hpq α' β' s = β' by simp [pairFactor, hq, hpq.symm]))).trans
      (Equiv.cast (show (β × β') = pairFactor hpq (α × α') (β × β') s by
        simp [pairFactor, hq, hpq.symm]))
  else
    ((Equiv.cast (show pairFactor hpq α β s = Unit by simp [pairFactor, hq, hp])).prodCongr
      (Equiv.cast (show pairFactor hpq α' β' s = Unit by simp [pairFactor, hq, hp]))).trans
      ((Equiv.prodPUnit Unit).trans
        (Equiv.cast (show Unit = pairFactor hpq (α × α') (β × β') s by simp [pairFactor, hq, hp])))

/-- The configurations of the merged fresh factors are the pairs of the configurations of the
two fresh factors. -/
theorem pairFactorConfigEquiv_prod (α β α' β' : Type) (a : Config (pairFactor hpq α β))
    (b : Config (pairFactor hpq α' β')) :
    pairFactorConfigEquiv hpq (α × α') (β × β')
        (fun s ↦ pairFactorProdEquiv hpq α β α' β' s (a s, b s)) =
      (((pairFactorConfigEquiv hpq α β a).1, (pairFactorConfigEquiv hpq α' β' b).1),
        ((pairFactorConfigEquiv hpq α β a).2, (pairFactorConfigEquiv hpq α' β' b).2)) := by
  simp [pairFactorConfigEquiv, pairFactorProdEquiv, hpq.symm]

/-- Two fresh factors at each endpoint, merged: `α × (α' × X p) ≃ (α × α') × X p`, read through
`addPairSiteEquiv` at every party. -/
def addPairAssocEquiv (α β α' β' : Type) (s : P) :
    addPair (addPair X hpq α' β') hpq α β s ≃ addPair X hpq (α × α') (β × β') s :=
  (addPairSiteEquiv hpq α β (addPair X hpq α' β') s).trans <|
    ((Equiv.refl _).prodCongr (addPairSiteEquiv hpq α' β' X s)).trans <|
      (Equiv.prodAssoc _ _ _).symm.trans <|
        ((pairFactorProdEquiv hpq α β α' β' s).prodCongr (Equiv.refl _)).trans
          (addPairSiteEquiv hpq (α × α') (β × β') X s).symm

/-- The configurations of the merged pair, read along `addPairAssocEquiv`: the fresh parts of the
two pairs, merged, and the existing part. -/
theorem addPairConfigEquiv_addPairAssocEquiv (α β α' β' : Type)
    (z : Config (addPair (addPair X hpq α' β') hpq α β)) :
    addPairConfigEquiv hpq (α × α') (β × β')
        (Equiv.piCongrRight (addPairAssocEquiv hpq α β α' β') z) =
      ((((addPairConfigEquiv hpq α β z).1.1,
          (addPairConfigEquiv hpq α' β' (addPairConfigEquiv hpq α β z).2).1.1),
        ((addPairConfigEquiv hpq α β z).1.2,
          (addPairConfigEquiv hpq α' β' (addPairConfigEquiv hpq α β z).2).1.2)),
        (addPairConfigEquiv hpq α' β' (addPairConfigEquiv hpq α β z).2).2) := by
  rw [addPairConfigEquiv_eq_siteEquiv, addPairConfigEquiv_eq_siteEquiv,
    addPairConfigEquiv_eq_siteEquiv]
  refine Prod.ext ?_ (funext fun s ↦ ?_)
  · simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst]
    rw [← pairFactorConfigEquiv_prod]
    congr 1
    funext s
    simp [addPairAssocEquiv]
  · simp [addPairAssocEquiv]

/-- Exchanging the endpoints of `addPair` changes nothing. -/
theorem addPair_comm (α β : Type) : addPair X hpq.symm β α = addPair X hpq α β := by
  funext s
  unfold addPair
  split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; subst_vars; exact hpq rfl)

/-- The identification of `addPair` with the endpoints exchanged. -/
def addPairCommEquiv (α β : Type) (s : P) : addPair X hpq α β s ≃ addPair X hpq.symm β α s :=
  Equiv.cast (congrFun (addPair_comm hpq α β) s).symm

/-- Two sources prepared in either order give the same bases up to exchanging the fresh factors
at the common endpoints: both bases are the two fresh factors and the existing basis
(`addPairSiteEquiv`), in the two orders. -/
def addPairSwapEquiv {p' q' : P} (hpq' : p' ≠ q') (α β α' β' : Type) (s : P) :
    addPair (addPair X hpq α β) hpq' α' β' s ≃ addPair (addPair X hpq' α' β') hpq α β s :=
  (addPairSiteEquiv hpq' α' β' (addPair X hpq α β) s).trans <|
    ((Equiv.refl _).prodCongr (addPairSiteEquiv hpq α β X s)).trans <|
      (((Equiv.prodAssoc _ _ _).symm.trans ((Equiv.prodComm _ _).prodCongr (Equiv.refl _))).trans
        (Equiv.prodAssoc _ _ _)).trans <|
        ((Equiv.refl _).prodCongr (addPairSiteEquiv hpq' α' β' X s).symm).trans
          (addPairSiteEquiv hpq α β (addPair X hpq' α' β') s).symm

end equivs

/-! ### Combining and expanding -/

section combine

variable [DecidableEq P] {X : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  {p q : P} (hpq : p ≠ q) (α β α' β' : Type) [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β']

/-- Two pair sources on the same pair of parties (first `η'`, then `η`), followed by merging the
two fresh factors of each endpoint. Source: Lemma 5.1,
`04-compression.tex`, lines 125–127. -/
def Word.combineSources (η : EuclideanSpace ℂ (α × β))
    (η' : EuclideanSpace ℂ (α' × β')) (X : P → Type) [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] : Word X (addPair X hpq (α × α') (β × β')) :=
  ((Word.sourceAt hpq α' β' η' X).comp
      (Word.sourceAt hpq α β η (addPair X hpq α' β'))).comp
    (PartyCircuit.relabel fun s ↦ (addPairAssocEquiv hpq α β α' β' s).symm)

/-- Combining two normalized sources is allowed. -/
theorem Word.isAllowed_combineSources {η : EuclideanSpace ℂ (α × β)}
    {η' : EuclideanSpace ℂ (α' × β')} (hη : ‖η‖ = 1) (hη' : ‖η'‖ = 1) :
    (Word.combineSources hpq α β α' β' η η' X).IsAllowed :=
  ⟨⟨Word.isAllowed_sourceAt hpq α' β' hη' X, Word.isAllowed_sourceAt hpq α β hη _⟩,
    Word.isAllowed_relabel _⟩

/-- The sources of the combination are the two sources, the later one first. -/
@[simp] theorem Word.sources_combineSources (η : EuclideanSpace ℂ (α × β))
    (η' : EuclideanSpace ℂ (α' × β')) :
    (Word.combineSources hpq α β α' β' η η' X).sources =
      [(SourceGate.ofAddPair hpq α β η (addPair X hpq α' β')).toPairSource,
        (SourceGate.ofAddPair hpq α' β' η' X).toPairSource] :=
  rfl

variable [Fintype P]

omit [Fintype P] in
/-- Split the merged fresh factors of a combined pair source. Source:
Lemma 5.1, `04-compression.tex`, lines 125–127. -/
def Word.expandCombinedPair (X : P → Type) [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] :
    Word (addPair X hpq (α × α') (β × β')) (addPair (addPair X hpq α' β') hpq α β) :=
  PartyCircuit.relabel (addPairAssocEquiv hpq α β α' β')

omit [Fintype P] in
/-- The expansion uses only local relabellings. -/
theorem Word.isAllowed_expandCombinedPair :
    (Word.expandCombinedPair hpq α β α' β' X).IsAllowed :=
  Word.isAllowed_relabel _

omit [Fintype P] in
/-- The expansion has no pair source. -/
@[simp] theorem Word.sources_expandCombinedPair :
    (Word.expandCombinedPair hpq α β α' β' X).sources = [] :=
  rfl

/-- Expanding the combined source recovers the two original pair sources. Source: Lemma 5.1,
`04-compression.tex`, lines 125–127. -/
theorem Word.op_expandCombinedPair (η : EuclideanSpace ℂ (α × β))
    (η' : EuclideanSpace ℂ (α' × β')) :
    (Word.expandCombinedPair hpq α β α' β' X).op *
        (Word.sourceAt hpq (α × α') (β × β') (EuclideanSpace.pairCombine η η') X).op =
      Word.op ((Word.sourceAt hpq α' β' η' X).comp
        (Word.sourceAt hpq α β η (addPair X hpq α' β'))) := by
  rw [Word.op_comp, Word.op_sourceAt, Word.op_sourceAt, Word.op_sourceAt,
    Word.expandCombinedPair]
  unfold Word.op
  rw [PartyCircuit.op_relabel_mul]
  ext z x
  simp only [submatrix_apply, id, prepMatrix_apply, prepMatrix_mul_apply,
    addPairConfigEquiv_addPairAssocEquiv]
  split_ifs <;> simp [EuclideanSpace.pairCombine]

/-- **Combining pair sources.** Two pair sources `η` and `η'` on the same pair of parties,
followed by merging the fresh factors of each party, are the single pair source of the combined
vector `η ⊗ η'`, whose norm is `‖η‖ ‖η'‖`. Source: Lemma 5.1, `04-compression.tex`,
lines 68–70 and 125–127. -/
theorem Word.op_combineSources (η : EuclideanSpace ℂ (α × β))
    (η' : EuclideanSpace ℂ (α' × β')) :
    (Word.combineSources hpq α β α' β' η η' X).op =
        (Word.sourceAt hpq (α × α') (β × β') (EuclideanSpace.pairCombine η η') X).op ∧
      ‖EuclideanSpace.pairCombine η η'‖ = ‖η‖ * ‖η'‖ :=
  ⟨by
    rw [Word.combineSources, Word.op_comp, ← Word.op_expandCombinedPair, Word.expandCombinedPair]
    unfold Word.op
    rw [PartyCircuit.op_relabel_mul, PartyCircuit.op_relabel_mul, submatrix_submatrix]
    ext y x
    simp only [submatrix_apply]
    congr 1
    funext s
    exact Equiv.apply_symm_apply (addPairAssocEquiv hpq α β α' β' s) (y s),
    EuclideanSpace.norm_pairCombine η η'⟩

omit [Fintype P] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] in
/-- The configurations of `addPair` with the endpoints exchanged are those of `addPair` with the
two fresh factors exchanged. -/
theorem addPairConfigEquiv_comm :
    (Equiv.piCongrRight (addPairCommEquiv (X := X) hpq α β)).trans
        (addPairConfigEquiv (X := X) hpq.symm β α) =
      (addPairConfigEquiv (X := X) hpq α β).trans
        ((Equiv.prodComm α β).prodCongr (Equiv.refl _)) := by
  ext z : 1
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun s ↦ ?_)
  · simp [addPairCommEquiv, addPairLeft, addPairRight]
  · simp [addPairCommEquiv, addPairLeft, addPairRight]
  · by_cases hp : s = p
    · subst hp
      simp [addPairConfigEquiv_apply_snd_left, addPairConfigEquiv_apply_snd_right,
        addPairCommEquiv, addPairLeft, addPairRight]
    by_cases hq : s = q
    · subst hq
      simp [addPairCommEquiv, addPairLeft, addPairRight]
    simp [addPairConfigEquiv_apply_snd_of_ne _ _ _ _ hp hq,
      addPairConfigEquiv_apply_snd_of_ne _ _ _ _ hq hp, addPairCommEquiv]

/-- A source with exchanged endpoints and the vector with exchanged factors
(`EuclideanSpace.pairSwap`) is the same source, up to the
identification `addPairCommEquiv` of the bases. Source:
Lemma 5.1, `04-compression.tex`, lines 68–70 and 125–127. -/
theorem Word.op_relabel_sourceAt_reverse (η : EuclideanSpace ℂ (α × β)) :
    Word.op (PartyCircuit.relabel (G := SourceGate) (addPairCommEquiv (X := X) hpq α β)) *
        (Word.sourceAt hpq.symm β α (EuclideanSpace.pairSwap η) X).op =
      (Word.sourceAt hpq α β η X).op := by
  rw [Word.op_sourceAt, Word.op_sourceAt, PartyCircuit.op_relabel_mul]
  ext y x
  have h := congrArg (· y) (addPairConfigEquiv_comm (X := X) hpq α β)
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply] at h
  simp only [submatrix_apply, prepMatrix_apply, id, h]
  simp

/-- **Two sources commute** up to the relabelling `addPairSwapEquiv`. Source: Theorem 5.2,
`eq:compression-source-gate`, `04-compression.tex`, lines 246–251. -/
theorem Word.op_relabel_sourceAt_swap {p' q' : P} (hpq' : p' ≠ q') (η : EuclideanSpace ℂ (α × β))
    (η' : EuclideanSpace ℂ (α' × β')) :
    Word.op (PartyCircuit.relabel (G := SourceGate)
        (addPairSwapEquiv (X := X) hpq' hpq α' β' α β)) *
        (Word.sourceAt hpq' α' β' η' (addPair X hpq α β)).op * (Word.sourceAt hpq α β η X).op =
      (Word.sourceAt hpq α β η (addPair X hpq' α' β')).op * (Word.sourceAt hpq' α' β' η' X).op := by
  rw [Matrix.mul_assoc, Word.op_sourceAt, Word.op_sourceAt, Word.op_sourceAt, Word.op_sourceAt,
    PartyCircuit.op_relabel_mul]
  ext y x
  simp only [submatrix_apply, id, prepMatrix_mul_apply]
  simp only [addPairConfigEquiv_eq_siteEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply, Equiv.piCongrRight_apply, Equiv.arrowProdEquivProdArrow_apply,
    prepMatrix_apply, addPairSwapEquiv, Equiv.apply_symm_apply, Pi.map_apply, Equiv.coe_trans,
    Function.comp_apply, Equiv.prodAssoc_apply, Equiv.prodAssoc_symm_apply,
    Equiv.prodComm_apply, Prod.swap_prod_mk]
  split_ifs <;> ring

end combine

end QuantumCircuit.Party
