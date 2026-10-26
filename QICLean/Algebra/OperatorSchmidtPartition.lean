/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic
import QICLean.Algebra.OperatorSchmidtReindex

/-!
# Operator Schmidt rank across two finite partitions

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
