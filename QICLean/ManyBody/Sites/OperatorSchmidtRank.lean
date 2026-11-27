/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidt.Basic
import QICLean.ManyBody.Sites.SupportedDecomposition
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic

/-!
# Operator Schmidt rank from designated supports

For a finite tensor product with arbitrary local dimensions, an operator
supported on X has operator Schmidt rank across A bounded by the square of
the dimension of the configurations on either X ∩ A or X \ A. In uniform positive
local dimension q, the two-sided bound is at most q to the cardinality of X.
An operator supported entirely on either side of the cut has rank at most one.
The support-square and one-sided statements include
empty configuration spaces and empty sets of sites.

The sharp count follows from the matrix-unit decomposition in the
OpenAI area-law manuscript, 02-initial.tex, lines 126–133.
These support estimates are used for words of local operators in LVV,
arXiv:1307.5143v1, equation e:decomp, lines 584–588, and AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 646–657. No assumption about a state,
a spectral gap, positivity, or normalization is required here.

## Main results

* `Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_le`,
  `Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_finset_le`: operator Schmidt rank across
  two finite partitions.
-/

section OperatorSchmidtRank

open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace Entropy

private theorem operatorSchmidtRank_zero
    {α β : Type*} [Fintype α] [Finite β] :
    Matrix.operatorSchmidtRank (0 : Matrix (α × β) (α × β) ℂ) = 0 := by
  exact Nat.eq_zero_of_le_zero
    (Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      ⟨Fin.elim0, Fin.elim0, by simp⟩)

/-- The designated-support matrix-unit count, expressed as operator Schmidt
rank. Supporting algebra for LVV, arXiv:1307.5143v1, equation e:decomp,
lines 584–588, and AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 646–657.
The existing decomposition is proved in the two-dimensional area-law
manuscript, 02-initial.tex, lines 126–133. -/
theorem _root_.ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le
    {V : Type*} [Finite V] [DecidableEq V] {n : V → ℕ}
    {A X : Finset V}
    {T : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ}
    (hT : ManyBody.IsSupportedOn T X) :
    Matrix.operatorSchmidtRank (ManyBody.cutOperator A T) ≤
      (∏ v ∈ X ∩ A, n v) ^ 2 := by
  let := Fintype.ofFinite V
  by_cases hconfig : Nonempty (∀ v, Fin (n v))
  case neg =>
    have : IsEmpty (∀ v, Fin (n v)) := ⟨fun σ => hconfig ⟨σ⟩⟩
    have hzero : T = 0 := Subsingleton.elim _ _
    simp [hzero, ManyBody.cutOperator, operatorSchmidtRank_zero]
  obtain ⟨σ₀⟩ := hconfig
  simpa only [ManyBody.card_innerConfig] using
    (hT.hasProductDecomposition_inner (B := A) σ₀ (le_rfl : ‖T‖ ≤ ‖T‖)).operatorSchmidtRank_le

/-- A supported operator acting on only one side of a cut has operator
Schmidt rank at most one. LVV, arXiv:1307.5143v1, lines 584–588;
AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 646–653. -/
theorem _root_.ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one
    {V : Type*} [Finite V] [DecidableEq V] {n : V → ℕ}
    {A X : Finset V}
    {T : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ}
    (hT : ManyBody.IsSupportedOn T X) (hside : X ⊆ A ∨ Disjoint X A) :
    Matrix.operatorSchmidtRank (ManyBody.cutOperator A T) ≤ 1 := by
  let := Fintype.ofFinite V
  by_cases hconfig : Nonempty (∀ v, Fin (n v))
  case neg =>
    have : IsEmpty (∀ v, Fin (n v)) := ⟨fun σ => hconfig ⟨σ⟩⟩
    have hzero : T = 0 := Subsingleton.elim _ _
    simp [hzero, ManyBody.cutOperator, operatorSchmidtRank_zero]
  obtain ⟨σ₀⟩ := hconfig
  have hone : Matrix.IsOneSided (ManyBody.cutOperator A T) := hside.elim
    (fun hleft => hT.isOneSided_of_subset hleft ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) A) σ₀).2)
    (fun hright => hT.isOneSided_of_disjoint hright
        ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) A) σ₀).1)
  rcases hone with ⟨U, hU⟩ | ⟨W, hW⟩
  · exact Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      ⟨(fun _ : Fin 1 => U), (fun _ : Fin 1 => 1), by simpa using hU⟩
  · exact Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      ⟨(fun _ : Fin 1 => 1), (fun _ : Fin 1 => W), by simpa using hW⟩

/-- Exchanging a finite region and its complement preserves the operator Schmidt rank in cut
coordinates. Supporting the two-sided local support bound for ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, lines 1971–2013. The local dimensions may vanish. -/
theorem operatorSchmidtRank_cutOperator_compl_eq
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (A : Finset V) (T : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ) :
    Matrix.operatorSchmidtRank (ManyBody.cutOperator Aᶜ T) =
      Matrix.operatorSchmidtRank (ManyBody.cutOperator A T) := by
  classical
  let eL : ((v : {v : V // v ∉ A}) → Fin (n v)) ≃
      ((v : {v : V // v ∈ Aᶜ}) → Fin (n v)) :=
    Equiv.piCongrLeft' (fun v : {v : V // v ∉ A} ↦ Fin (n v))
    (Finset.complSubtypeEquiv A)
  let eR : ((v : {v : V // v ∈ A}) → Fin (n v)) ≃
      ((v : {v : V // v ∉ Aᶜ}) → Fin (n v)) :=
    Equiv.piCongrLeft' (fun v : {v : V // v ∈ A} ↦ Fin (n v))
    (Equiv.subtypeEquivRight (fun v : V ↦
      (show v ∈ A ↔ v ∉ Aᶜ by simp only [Finset.mem_compl, not_not])))
  have he : ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) A).trans (Equiv.prodComm _ _)).trans
      (eL.prodCongr eR) =
      ManyBody.cutEquiv (fun v ↦ Fin (n v)) Aᶜ := by
    apply Equiv.ext
    intro σ
    exact Prod.ext (funext fun _ ↦ rfl) (funext fun _ ↦ rfl)
  have hm : ManyBody.cutOperator Aᶜ T =
      ((ManyBody.cutOperator A T).reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)).reindex
        (eL.prodCongr eR) (eL.prodCongr eR) := by
    change T.reindex (ManyBody.cutEquiv (fun v ↦ Fin (n v)) Aᶜ)
        (ManyBody.cutEquiv (fun v ↦ Fin (n v)) Aᶜ) =
      T.reindex
          (((ManyBody.cutEquiv (fun v ↦ Fin (n v)) A).trans (Equiv.prodComm _ _)).trans
          (eL.prodCongr eR))
        (((ManyBody.cutEquiv (fun v ↦ Fin (n v)) A).trans (Equiv.prodComm _ _)).trans
            (eL.prodCongr eR))
    rw [he]
  rw [hm, Matrix.operatorSchmidtRank_reindex_prodCongr,
    Matrix.operatorSchmidtRank_reindex_prodComm]

/-- A supported operator has operator Schmidt rank bounded by the square of the configuration
dimension on either part of its designated support. Supporting the crossing-interval estimate
for ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. Empty regions and zero local
dimensions are included, and no spectral, positivity or state premise is needed. -/
theorem _root_.ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_min
    {V : Type*} [Finite V] [DecidableEq V] {n : V → ℕ} {A X : Finset V}
    {T : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ} (hT : ManyBody.IsSupportedOn T X) :
    Matrix.operatorSchmidtRank (ManyBody.cutOperator A T) ≤
      min ((∏ v ∈ X ∩ A, n v) ^ 2) ((∏ v ∈ X \ A, n v) ^ 2) := by
  let := Fintype.ofFinite V
  refine le_min hT.operatorSchmidtRank_cutOperator_le ?_
  have hc := hT.operatorSchmidtRank_cutOperator_le (A := Aᶜ)
  rw [operatorSchmidtRank_cutOperator_compl_eq] at hc
  simpa only [Finset.sdiff_eq_inter_compl] using hc

/-- On a uniform finite tensor product with positive local dimension, an operator supported on
`X` has operator Schmidt rank at most `q ^ X.card` at every cut. This combines the two actual
support-square bounds, including local dimension one. Supporting ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, lines 1971–2013. -/
theorem _root_.ManyBody.IsSupportedOn.operatorSchmidtRank_cutOperator_le_pow_card
    {V : Type*} [Finite V] [DecidableEq V] {q : ℕ} (hq : 1 ≤ q) {A X : Finset V}
    {T : Matrix ((_ : V) → Fin q) ((_ : V) → Fin q) ℂ}
    (hT : ManyBody.IsSupportedOn T X) :
    Matrix.operatorSchmidtRank (ManyBody.cutOperator A T) ≤ q ^ X.card := by
  have hm := hT.operatorSchmidtRank_cutOperator_le_min (A := A)
  simp only [Finset.prod_const, ← pow_mul] at hm
  have hc := Finset.card_inter_add_card_sdiff X A
  rcases le_total (X ∩ A).card (X \ A).card with hle | hle
  · exact hm.trans ((min_le_left _ _).trans (Nat.pow_le_pow_right hq (by omega)))
  · exact hm.trans ((min_le_right _ _).trans (Nat.pow_le_pow_right hq (by omega)))

end Entropy

end OperatorSchmidtRank

section OperatorSchmidtPartition

/-!
## Operator Schmidt rank across two finite partitions

For an operator whose basis is indexed by functions from a finite set of
sites to a finite local alphabet, changing the partition increases operator
Schmidt rank by at most the squared configuration dimensions of the two
exchanged regions. The common region and the common exterior contribute no
additional factor.

The proof compares the four restrictions of a function and applies the
four-factor interchange estimate. Empty site sets and empty alphabets are
included; the empty region has one configuration even for an empty alphabet.

This is supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7,
lines 1331–1333.
-/

open scoped symmDiff

/-- Changing a finite tensor partition costs only the squared dimensions of
the two exchanged regions. Supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1331–1333.
Empty site sets and empty local alphabets are included. -/
theorem Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_le
    {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (M : Matrix (V → A) (V → A) ℂ) (p q : V → Prop)
    [DecidablePred p] [DecidablePred q] :
    Matrix.operatorSchmidtRank
        (M.reindex (Equiv.piEquivPiSubtypeProd q (fun _ ↦ A))
          (Equiv.piEquivPiSubtypeProd q (fun _ ↦ A))) ≤
      Fintype.card ({v : V // p v ∧ ¬q v} → A) ^ 2 *
        Fintype.card ({v : V // ¬p v ∧ q v} → A) ^ 2 *
        Matrix.operatorSchmidtRank
          (M.reindex (Equiv.piEquivPiSubtypeProd p (fun _ ↦ A))
            (Equiv.piEquivPiSubtypeProd p (fun _ ↦ A))) := by
  classical
  let split (r s : V → Prop) : ({v : V // r v} → A) ≃
      ({v : V // r v ∧ s v} → A) × ({v : V // r v ∧ ¬s v} → A) :=
    (Equiv.piEquivPiSubtypeProd (fun v : {v : V // r v} ↦ s v.val)
      (fun _ ↦ A)).trans
      ((Equiv.arrowCongr (Equiv.subtypeSubtypeEquivSubtypeInter r s)
          (Equiv.refl A)).prodCongr
        (Equiv.arrowCongr (Equiv.subtypeSubtypeEquivSubtypeInter r (fun v ↦ ¬s v))
          (Equiv.refl A)))
  let comm (r s : V → Prop) : ({v : V // r v ∧ s v} → A) ≃
      ({v : V // s v ∧ r v} → A) :=
    Equiv.arrowCongr (Equiv.subtypeEquivRight (fun _ ↦ and_comm)) (Equiv.refl A)
  let eP := (split p q).prodCongr (split (fun v ↦ ¬p v) q)
  let eQL := (split q p).trans
    ((comm q p).prodCongr (comm q (fun v ↦ ¬p v)))
  let eQR := (split (fun v ↦ ¬q v) p).trans
    ((comm (fun v ↦ ¬q v) p).prodCongr (comm (fun v ↦ ¬q v) (fun v ↦ ¬p v)))
  have hcoord :
      ((Equiv.piEquivPiSubtypeProd p (fun _ ↦ A)).trans eP).trans
          (Equiv.prodProdProdComm _ _ _ _) =
        (Equiv.piEquivPiSubtypeProd q (fun _ ↦ A)).trans (eQL.prodCongr eQR) :=
    Equiv.ext (fun _ ↦ rfl)
  rw [← Matrix.operatorSchmidtRank_reindex_prodCongr
    (M.reindex (Equiv.piEquivPiSubtypeProd q (fun _ ↦ A))
      (Equiv.piEquivPiSubtypeProd q (fun _ ↦ A))) eQL eQR]
  rw [← Matrix.operatorSchmidtRank_reindex_prodCongr
    (M.reindex (Equiv.piEquivPiSubtypeProd p (fun _ ↦ A))
      (Equiv.piEquivPiSubtypeProd p (fun _ ↦ A)))
    (split p q) (split (fun v ↦ ¬p v) q)]
  change Matrix.operatorSchmidtRank
      (M.reindex
        ((Equiv.piEquivPiSubtypeProd q (fun _ ↦ A)).trans (eQL.prodCongr eQR))
        ((Equiv.piEquivPiSubtypeProd q (fun _ ↦ A)).trans (eQL.prodCongr eQR))) ≤ _
  rw [← hcoord]
  exact Matrix.operatorSchmidtRank_reindex_prodProdProdComm_le
    (M.reindex ((Equiv.piEquivPiSubtypeProd p (fun _ ↦ A)).trans eP)
      ((Equiv.piEquivPiSubtypeProd p (fun _ ↦ A)).trans eP))

/-- The squared dimensions of the two exchanged configuration spaces.
This is the cardinality factor used in ALVV, arXiv:1602.08828v2,
Proposition 5.7, lines 1331–1333, including zero local dimension. -/
private theorem exchanged_configuration_card_sq
    {V : Type*} [Fintype V] [DecidableEq V] (S T : Finset V) (q : ℕ) :
    Fintype.card ({v : V // v ∈ S ∧ v ∉ T} → Fin q) ^ 2 *
      Fintype.card ({v : V // v ∉ S ∧ v ∈ T} → Fin q) ^ 2 =
        q ^ (2 * (S ∆ T).card) := by
  classical
  have hST : Fintype.card {v : V // v ∈ S ∧ v ∉ T} = (S \ T).card :=
    Fintype.card_of_subtype (S \ T) (fun _ ↦ Finset.mem_sdiff)
  have hTS : Fintype.card {v : V // v ∉ S ∧ v ∈ T} = (T \ S).card :=
    Fintype.card_of_subtype (T \ S) (fun _ ↦ Finset.mem_sdiff.trans and_comm)
  have hcard : (S ∆ T).card = (S \ T).card + (T \ S).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  simp only [Fintype.card_fun, Fintype.card_fin, hST, hTS, hcard]
  rw [← mul_pow, ← pow_add, ← pow_mul, Nat.mul_comm]

/-- Changing a finite region multiplies operator Schmidt rank by at most
q to twice the number of changed sites. Supporting algebra for ALVV,
arXiv:1602.08828v2, Proposition 5.7, lines 1331–1333.
The identity of configuration cardinalities includes q = 0. -/
theorem Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_finset_le
    {V : Type*} [Finite V] [DecidableEq V]
    (q : ℕ) (S T : Finset V) (M : Matrix (V → Fin q) (V → Fin q) ℂ) :
    Matrix.operatorSchmidtRank
        (M.reindex (Equiv.piEquivPiSubtypeProd (fun v ↦ v ∈ T) (fun _ ↦ Fin q))
          (Equiv.piEquivPiSubtypeProd (fun v ↦ v ∈ T) (fun _ ↦ Fin q))) ≤
      q ^ (2 * (S ∆ T).card) * Matrix.operatorSchmidtRank
        (M.reindex (Equiv.piEquivPiSubtypeProd (fun v ↦ v ∈ S) (fun _ ↦ Fin q))
          (Equiv.piEquivPiSubtypeProd (fun v ↦ v ∈ S) (fun _ ↦ Fin q))) := by
  let := Fintype.ofFinite V
  have h := Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_le M
    (fun v ↦ v ∈ S) (fun v ↦ v ∈ T)
  rw [exchanged_configuration_card_sq] at h
  simpa only [Matrix.operatorSchmidtRank_eq_finrank_operatorBlockSpan] using h

end OperatorSchmidtPartition
