/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceReplacement.PreparedMatrix
import QICLean.Circuit.Party.Monomial.Stack
import QICLean.Circuit.Party.Syntax.CoarsenLocal

/-!
# Products of local operators on source endpoints

A source slot provides a basis at each of two parties. A product of operators
on the endpoints of all slots is represented by a word of local operations.
The word leaves the underlying system untouched. In source coordinates each
matrix entry is the product of the entries of the endpoint operators and the
identity entry of the underlying system.

Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 279–340 and 565–588.
Adapted from TNLean, `TNLean/Lattice/Compression/EndpointOperatorWord.lean` at
`2417e0a2e4d8a1dc2db0a14e0c9cae4ca735829e`, using the configuration bases of slots.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

private def endpointFactors {p q : P} (hpq : p ≠ q) {A B : Type}
    (L : Matrix A A ℂ) (R : Matrix B B ℂ) (r : P) :
    Matrix (pairFactor hpq A B r) (pairFactor hpq A B r) ℂ :=
  fun x y ↦
    if hrp : r = p then
      L (cast (by subst r; simp [pairFactor]) x) (cast (by subst r; simp [pairFactor]) y)
    else if hrq : r = q then
      R (cast (by subst r; simp [pairFactor, hpq.symm]) x)
        (cast (by subst r; simp [pairFactor, hpq.symm]) y)
    else 1

private theorem piKronecker_endpointFactors {p q : P} (hpq : p ≠ q) {A B : Type}
    (L : Matrix A A ℂ) (R : Matrix B B ℂ) :
    piKronecker (endpointFactors hpq L R) =
      reindex (pairFactorConfigEquiv hpq A B).symm (pairFactorConfigEquiv hpq A B).symm
        (L ⊗ₖ R) := by
  ext x y
  simp only [piKronecker_apply, reindex_apply, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p),
    ← Finset.mul_prod_erase (Finset.univ.erase p) _ (by simp [hpq.symm] : q ∈ _)]
  have hrest :
      (∏ r ∈ (Finset.univ.erase p).erase q, endpointFactors hpq L R r (x r) (y r)) = 1 := by
    apply Finset.prod_eq_one
    intro r hr
    have hrq := (Finset.mem_erase.mp hr).1
    have hrp := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
    simp [endpointFactors, hrp, hrq]
  rw [hrest]
  simp [endpointFactors, pairFactorConfigEquiv, hpq.symm]

private noncomputable def endpointPairWord {p q : P} (hpq : p ≠ q) {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (Z : P → Type)
    [∀ r, Fintype (Z r)] [∀ r, DecidableEq (Z r)]
    (L : Matrix A A ℂ) (R : Matrix B B ℂ) :
    Word (addPair Z hpq A B) (addPair Z hpq A B) :=
  PartyCircuit.localOps fun r ↦
    reindex (addPairSiteEquiv hpq A B Z r).symm (addPairSiteEquiv hpq A B Z r).symm
      (endpointFactors hpq L R r ⊗ₖ (1 : Matrix (Z r) (Z r) ℂ))

private theorem op_endpointPairWord {p q : P} (hpq : p ≠ q) {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (Z : P → Type)
    [∀ r, Fintype (Z r)] [∀ r, DecidableEq (Z r)]
    (L : Matrix A A ℂ) (R : Matrix B B ℂ) :
    (endpointPairWord hpq Z L R).op =
      reindex (addPairConfigEquiv (X := Z) hpq A B).symm
        (addPairConfigEquiv (X := Z) hpq A B).symm
        ((L ⊗ₖ R) ⊗ₖ (1 : Matrix (Config Z) (Config Z) ℂ)) := by
  rw [endpointPairWord, Word.op, PartyCircuit.op_localOps]
  ext y x
  rw [addPairConfigEquiv_eq_siteEquiv]
  simp only [piKronecker_apply, reindex_apply, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    Equiv.piCongrRight_apply, Equiv.arrowProdEquivProdArrow_apply, Finset.prod_mul_distrib]
  have hf := congrFun (congrFun (piKronecker_endpointFactors hpq L R)
    (fun r ↦ (addPairSiteEquiv hpq A B Z r (y r)).1))
      (fun r ↦ (addPairSiteEquiv hpq A B Z r (x r)).1)
  simp only [piKronecker_apply, reindex_apply, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply] at hf
  rw [hf]
  congr 1
  simp only [one_apply, Finset.prod_boole, Finset.mem_univ, forall_const, funext_iff, Pi.map_apply]

namespace SourceInventory

/-- The word applying the two given operators at each source slot, leaving the base system
unchanged. Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 565–588. -/
noncomputable def endpointWord (Z : P → Type) [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] :
    (R : SourceInventory P) → (B : SlotBases R.length) →
    (∀ i, Matrix (B.left i) (B.left i) ℂ) → (∀ i, Matrix (B.right i) (B.right i) ℂ) →
      Word (slotSystem R B Z) (slotSystem R B Z)
  | [], _, _, _ => .done Z
  | r :: R, B, L, M =>
    (endpointPairWord r.distinct (slotSystem R B.tail Z) (L 0) (M 0)).comp
      (PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0)
        (endpointWord Z R B.tail (fun i ↦ L i.succ) (fun i ↦ M i.succ)))

omit [Fintype P] in
/-- An endpoint word creates no pair sources. -/
theorem sources_endpointWord (Z : P → Type) [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)]
    (R : SourceInventory P) (B : SlotBases R.length) (L : ∀ i, Matrix (B.left i) (B.left i) ℂ)
    (M : ∀ i, Matrix (B.right i) (B.right i) ℂ) :
    (endpointWord Z R B L M).sources = [] := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    rw [endpointWord]
    erw [Word.sources_comp, PartyCircuit.liftPair, Word.sources_comp,
      Word.sources_comp, Word.sources_relabel, Word.sources_frame, ih]
    rfl

omit [Fintype P] in
private theorem partyOp_liftPair_eq_one
    {a b : P} (hab : a ≠ b) (A B : Type)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {X : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (w : Word X X) (p : P) (h : w.partyOp p = 1) :
    (PartyCircuit.liftPair hab A B w).partyOp p = 1 := by
  rw [PartyCircuit.liftPair, PartyCircuit.partyOp_comp, PartyCircuit.partyOp_comp,
    PartyCircuit.partyOp_frame, h, one_kronecker_one, Matrix.mul_one]
  simp only [PartyCircuit.relabel, PartyCircuit.partyOp_localOps,
    ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
    Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

omit [Fintype P] in
/-- The endpoint word acts as the identity at a party for which all its
endpoint matrices are identities. -/
theorem partyOp_endpointWord_eq_one (Z : P → Type) [∀ p, Fintype (Z p)]
    [∀ p, DecidableEq (Z p)] (R : SourceInventory P) (B : SlotBases R.length)
    (L : ∀ i, Matrix (B.left i) (B.left i) ℂ)
    (M : ∀ i, Matrix (B.right i) (B.right i) ℂ) (p : P)
    (hL : ∀ i, (R.get i).left = p → L i = 1) (hM : ∀ i, (R.get i).right = p → M i = 1) :
    (endpointWord Z R B L M).partyOp p = 1 := by
  induction R with
  | nil => exact PartyCircuit.partyOp_done _
  | cons r R ih =>
    have htail := ih B.tail (fun i ↦ L i.succ) (fun i ↦ M i.succ)
      (fun i ↦ hL i.succ) (fun i ↦ hM i.succ)
    have hhead : endpointFactors r.distinct (L 0) (M 0) p = 1 := by
      ext x y
      by_cases hl : p = r.left
      · simp [endpointFactors, hl, hL 0 hl.symm, one_apply, cast_inj]
      by_cases hr : p = r.right
      · simp [endpointFactors, hr, r.distinct.symm, hM 0 hr.symm, one_apply, cast_inj]
      · have hU : pairFactor r.distinct (B.left 0) (B.right 0) p = Unit := by
          simp [pairFactor, hl, hr]
        have hxy := (Equiv.cast hU).subsingleton.elim x y
        simp [endpointFactors, hl, hr, one_apply, hxy]
    change (PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0)
      (endpointWord Z R B.tail (fun i ↦ L i.succ) (fun i ↦ M i.succ))).partyOp p *
      (endpointPairWord r.distinct (slotSystem R B.tail Z) (L 0) (M 0)).partyOp p = 1
    have h := partyOp_liftPair_eq_one r.distinct (B.left 0) (B.right 0) _ p htail
    rw [h, Matrix.one_mul]
    simp [endpointPairWord, hhead]

/-- The entries of the endpoint word are the product of the endpoint entries, times the
identity on the underlying configuration. -/
theorem op_endpointWord (Z : P → Type) [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)]
    (R : SourceInventory P) (B : SlotBases R.length) (L : ∀ i, Matrix (B.left i) (B.left i) ℂ)
    (M : ∀ i, Matrix (B.right i) (B.right i) ℂ) :
    (endpointWord Z R B L M).op =
      reindex (slotColumnEquiv R B Z).symm (slotColumnEquiv R B Z).symm
        (piKronecker (fun i ↦ L i ⊗ₖ M i) ⊗ₖ (1 : Matrix (Config Z) (Config Z) ℂ)) := by
  induction R with
  | nil =>
    ext y x
    change PartyCircuit.op SourceGate.ev (PartyCircuit.done Z) y x = _
    rw [PartyCircuit.op_done]
    let : IsEmpty (Fin ([] : SourceInventory P).length) := Fin.isEmpty'
    simp [slotColumnEquiv, reindex_apply, submatrix_apply, kroneckerMap_apply, piKronecker_apply,
      Equiv.uniqueProd]
    rfl
  | cons r R ih =>
    rw [endpointWord]
    erw [Word.op_comp, op_endpointPairWord]
    change (PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0)
      (endpointWord Z R B.tail (fun i ↦ L i.succ) (fun i ↦ M i.succ))).op SourceGate.ev * _ = _
    erw [PartyCircuit.op_liftPair _ _ _ _ SourceGate.isCompatible_frame]
    change reindex _ _ (_ ⊗ₖ (endpointWord Z R B.tail (fun i ↦ L i.succ)
      (fun i ↦ M i.succ)).op) * _ = _
    erw [reindexLinearEquiv_mul ℂ ℂ, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    erw [ih, coe_reindexLinearEquiv]
    ext y x
    erw [reindex_apply]
    simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
      piKronecker_apply, slotColumnEquiv_cons_apply]
    erw [Fin.prod_univ_succ]
    simp only [mul_assoc]
    rfl


/-- Taking a weighted sum of endpoint matrices independently at every slot is the
corresponding weighted sum of endpoint words. Each summand chooses one term in
each slot, with coefficient the product of the coefficients of those choices. -/
theorem sum_op_endpointWord (Z : P → Type) [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)]
    (R : SourceInventory P) (B : SlotBases R.length)
    {J : Fin R.length → Type} [∀ i, Fintype (J i)] (c : ∀ i, J i → ℂ)
    (L : ∀ i, J i → Matrix (B.left i) (B.left i) ℂ)
    (M : ∀ i, J i → Matrix (B.right i) (B.right i) ℂ) :
    (∑ a : ∀ i, J i, (∏ i, c i (a i)) •
      (endpointWord Z R B (fun i ↦ L i (a i)) (fun i ↦ M i (a i))).op) =
      reindex (slotColumnEquiv R B Z).symm (slotColumnEquiv R B Z).symm
        (piKronecker (fun i ↦ ∑ j, c i j • (L i j ⊗ₖ M i j)) ⊗ₖ
          (1 : Matrix (Config Z) (Config Z) ℂ)) := by
  ext y x
  simp only [op_endpointWord, reindex_apply, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply, piKronecker_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_univ_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [Finset.prod_mul_distrib, mul_assoc]

end SourceInventory

end QuantumCircuit.Party
