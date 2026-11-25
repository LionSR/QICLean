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
identity entry of the underlying system. At one party, read in the party coordinates
`SourceInventory.slotSiteEquiv`, the word is the Kronecker product over the slots of the
endpoint operator at that party, the identity of a one-element factor at a slot without an
endpoint there; it therefore depends only on the endpoint operators at that party. The
inventory, the bases and the operators are arbitrary.

## Main definitions

* `QuantumCircuit.Party.SourceInventory.endpointWord`.

## Main results

* `QuantumCircuit.Party.SourceInventory.op_endpointWord`,
  `QuantumCircuit.Party.SourceInventory.sum_op_endpointWord`,
  `QuantumCircuit.Party.SourceInventory.op_endpointWord_mulVec_slotVector`,
  `QuantumCircuit.Party.SourceInventory.op_endpointWord_mulVec_slotVector_tmul`.
* `QuantumCircuit.Party.SourceInventory.partyOp_endpointWord`,
  `QuantumCircuit.Party.SourceInventory.partyOp_endpointWord_congr`,
  `QuantumCircuit.Party.SourceInventory.partyOp_endpointWord_eq_one`.

Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 279–340 and 565–588.
Adapted from TNLean, `TNLean/Lattice/Compression/EndpointOperatorWord.lean` at
`2417e0a2e4d8a1dc2db0a14e0c9cae4ca735829e`, using the configuration bases of slots.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

omit [Fintype P] in
/-- The fresh-factor maps of a pair at a party depend only on the map at that party. -/
private theorem pairFactorMatrix_congr {p q : P} (hpq : p ≠ q) {A B : Type}
    {L L' : Matrix A A ℂ} {R R' : Matrix B B ℂ} {r : P} (hL : p = r → L = L')
    (hR : q = r → R = R') : pairFactorMatrix hpq L R r = pairFactorMatrix hpq L' R' r := by
  unfold pairFactorMatrix
  split_ifs with hp hq
  · rw [hL hp.symm]
  · rw [hR hq.symm]
  · rfl

omit [Fintype P] in
/-- The fresh-factor maps of two identities are identities. -/
private theorem pairFactorMatrix_one_one {p q : P} (hpq : p ≠ q) (A B : Type) [DecidableEq A]
    [DecidableEq B] (r : P) :
    pairFactorMatrix hpq (1 : Matrix A A ℂ) (1 : Matrix B B ℂ) r = 1 := by
  unfold pairFactorMatrix
  split_ifs <;> rw [reindex_apply, submatrix_one_equiv]

/-- The operator of the word applying `L` and `R` at the two endpoints of one pair. -/
private theorem op_mapPair {p q : P} (hpq : p ≠ q) {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (Z : P → Type)
    [∀ r, Fintype (Z r)] [∀ r, DecidableEq (Z r)]
    (L : Matrix A A ℂ) (R : Matrix B B ℂ) :
    (Word.mapPair hpq L R Z).op =
      reindex (addPairConfigEquiv (X := Z) hpq A B).symm
        (addPairConfigEquiv (X := Z) hpq A B).symm
        ((L ⊗ₖ R) ⊗ₖ (1 : Matrix (Config Z) (Config Z) ℂ)) := by
  rw [Word.mapPair, Word.op, PartyCircuit.op_localOps, piKronecker_pairMapMatrix]

namespace SourceInventory

/-- The word applying the two given operators at each source slot, leaving the base system
unchanged. Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 565–588. -/
noncomputable def endpointWord (Z : P → Type) [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] :
    (R : SourceInventory P) → (B : SlotBases R.length) →
    (∀ i, Matrix (B.left i) (B.left i) ℂ) → (∀ i, Matrix (B.right i) (B.right i) ℂ) →
      Word (slotSystem R B Z) (slotSystem R B Z)
  | [], _, _, _ => .done Z
  | r :: R, B, L, M =>
    (Word.mapPair r.distinct (L 0) (M 0) (slotSystem R B.tail Z)).comp
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
/-- Lifting a word whose operation at a party is the identity beside a fresh pair keeps the
identity at that party. -/
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
endpoint matrices are identities. Source: Theorem 5.2, `04-compression.tex`, lines 565–579. -/
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
    have hhead : pairFactorMatrix r.distinct (L 0) (M 0) p = 1 :=
      (pairFactorMatrix_congr r.distinct (hL 0) (hM 0)).trans
        (pairFactorMatrix_one_one r.distinct _ _ p)
    change (PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0)
      (endpointWord Z R B.tail (fun i ↦ L i.succ) (fun i ↦ M i.succ))).partyOp p *
      (Word.mapPair r.distinct (L 0) (M 0) (slotSystem R B.tail Z)).partyOp p = 1
    have h := partyOp_liftPair_eq_one r.distinct (B.left 0) (B.right 0) _ p htail
    rw [h, Matrix.one_mul]
    simp [Word.mapPair, pairMapMatrix, hhead]

/-- The entries of the endpoint word are the product of the endpoint entries, times the
identity on the underlying configuration. Source: Theorem 5.2, `04-compression.tex`,
lines 565–579. -/
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
    erw [Word.op_comp, op_mapPair]
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
each slot, with coefficient the product of the coefficients of those choices. Source: Theorem 5.2,
`04-compression.tex`, lines 279–340 and 565–579. -/
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

omit [Fintype P] in
/-- **The endpoint word acts at each party by the endpoint operators of the slots at that
party, in the order of the slots, and by the identity on the underlying basis.** In the party
coordinates of the slot system, its party operation is the Kronecker product over the slots of
the endpoint matrix of the slot at the party — `L i` at the left endpoint, `M i` at the right
endpoint, the identity of the one-element factor at a party that is no endpoint — tensored with
the identity. The inventory and the matrices are arbitrary, including the empty inventory, empty
bases and zero matrices. Source: Theorem 5.2, `04-compression.tex`, lines 279–309, 409–434 and
565–588. -/
theorem partyOp_endpointWord (Z : P → Type) [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)]
    (R : SourceInventory P) (B : SlotBases R.length) (L : ∀ i, Matrix (B.left i) (B.left i) ℂ)
    (M : ∀ i, Matrix (B.right i) (B.right i) ℂ) (p : P) :
    (endpointWord Z R B L M).partyOp p =
      reindex (slotSiteEquiv R B Z p).symm (slotSiteEquiv R B Z p).symm
        (piKronecker (fun i ↦ pairFactorMatrix (R.get i).distinct (L i) (M i) p) ⊗ₖ
          (1 : Matrix (Z p) (Z p) ℂ)) := by
  induction R with
  | nil =>
    ext y x
    change (1 : Matrix (Z p) (Z p) ℂ) y x = _
    let : IsEmpty (Fin ([] : SourceInventory P).length) := Fin.isEmpty'
    simp only [reindex_apply, submatrix_apply, kroneckerMap_apply, piKronecker_apply,
      Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    rfl
  | cons r R ih =>
    rw [endpointWord]
    change (PartyCircuit.liftPair r.distinct (B.left 0) (B.right 0)
      (endpointWord Z R B.tail (fun i ↦ L i.succ) (fun i ↦ M i.succ))).partyOp p *
      (Word.mapPair r.distinct (L 0) (M 0) (slotSystem R B.tail Z)).partyOp p = _
    have htail := ih B.tail (fun i ↦ L i.succ) (fun i ↦ M i.succ)
    rw [PartyCircuit.liftPair, PartyCircuit.partyOp_comp, PartyCircuit.partyOp_comp,
      PartyCircuit.partyOp_frame]
    erw [htail]
    simp only [Word.mapPair, pairMapMatrix, PartyCircuit.relabel,
      PartyCircuit.partyOp_localOps]
    rw [PEquiv.toMatrix_toPEquiv_mul, Matrix.mul_assoc, PEquiv.toMatrix_toPEquiv_mul]
    ext y x
    change _ = (piKronecker (fun i ↦ pairFactorMatrix ((r :: R).get i).distinct (L i) (M i) p) ⊗ₖ
      (1 : Matrix (Z p) (Z p) ℂ)) (slotSiteEquiv (r :: R) B Z p y) (slotSiteEquiv (r :: R) B Z p x)
    erw [slotSiteEquiv_cons_apply r R B Z p y, slotSiteEquiv_cons_apply r R B Z p x]
    rw [kroneckerMap_apply, piKronecker_apply]
    erw [Fin.prod_univ_succ]
    rw [mul_apply, Fintype.sum_prod_type]
    simp only [submatrix_apply, reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply, id,
      kroneckerMap_apply, one_apply, piKronecker_apply, ite_mul,
      one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    by_cases hC : ((slotSiteEquiv R B.tail Z p) ((addPairSiteEquiv r.distinct (B.left 0)
        (B.right 0) (slotSystem R B.tail Z) p) y).2).2 =
        ((slotSiteEquiv R B.tail Z p) ((addPairSiteEquiv r.distinct (B.left 0)
        (B.right 0) (slotSystem R B.tail Z) p) x).2).2
    · simp only [hC, ite_true, Finset.sum_ite_eq, Finset.mem_univ]
      exact mul_comm _ _
    · simp only [hC, ite_false, Finset.sum_const_zero]

omit [Fintype P] in
/-- **The party operation of an endpoint word depends only on the endpoint operators at that
party**: two families of endpoint matrices that agree at every left endpoint and at every right
endpoint equal to `p` give the same operation at `p`. Source: Theorem 5.2,
`04-compression.tex`, lines 279–309, 409–434 and 565–588. -/
theorem partyOp_endpointWord_congr (Z : P → Type) [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)]
    (R : SourceInventory P) (B : SlotBases R.length)
    {L L' : ∀ i, Matrix (B.left i) (B.left i) ℂ} {M M' : ∀ i, Matrix (B.right i) (B.right i) ℂ}
    (p : P) (hL : ∀ i, (R.get i).left = p → L i = L' i)
    (hM : ∀ i, (R.get i).right = p → M i = M' i) :
    (endpointWord Z R B L M).partyOp p = (endpointWord Z R B L' M').partyOp p := by
  rw [partyOp_endpointWord, partyOp_endpointWord]
  exact congrArg (fun K ↦ reindex (slotSiteEquiv R B Z p).symm (slotSiteEquiv R B Z p).symm
    (piKronecker K ⊗ₖ (1 : Matrix (Z p) (Z p) ℂ)))
    (funext fun i ↦ pairFactorMatrix_congr _ (hL i) (hM i))

/-- **The endpoint word acts slot by slot on product vectors**: in the source coordinates, the
product of slot vectors `η i` beside a vector `ψ` of the underlying system goes to the product
of the vectors `(L i ⊗ M i) η i` beside `ψ`. No normalization or nonvanishing is used. Source:
Theorem 5.2, `04-compression.tex`, lines 279–309 and 565–588. -/
theorem op_endpointWord_mulVec_slotVector (Z : P → Type) [∀ p, Fintype (Z p)]
    [∀ p, DecidableEq (Z p)] (R : SourceInventory P) (B : SlotBases R.length)
    (L : ∀ i, Matrix (B.left i) (B.left i) ℂ) (M : ∀ i, Matrix (B.right i) (B.right i) ℂ)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (ψ : Config Z → ℂ) :
    ((endpointWord Z R B L M).op *ᵥ fun z ↦
        slotVector R B η (slotColumnEquiv R B Z z).1 * ψ (slotColumnEquiv R B Z z).2) =
      fun z ↦ slotVector R B (fun i ↦ WithLp.toLp 2 ((L i ⊗ₖ M i) *ᵥ η i))
        (slotColumnEquiv R B Z z).1 * ψ (slotColumnEquiv R B Z z).2 := by
  funext z
  have hK := congrFun (piKronecker_mulVec_prod (fun i ↦ L i ⊗ₖ M i) fun i ↦ η i)
    (slotColumnEquiv R B Z z).1
  refine Eq.trans ?_ (congrArg (· * ψ (slotColumnEquiv R B Z z).2) hK)
  rw [op_endpointWord, mulVec, dotProduct, mulVec, dotProduct, Finset.sum_mul,
    ← (slotColumnEquiv R B Z).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    kroneckerMap_apply, one_apply, slotVector_apply, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- **The endpoint word acts factor by factor on the endpoint vectors**: the product over the
slots of `u i ⊗ v i`, beside a vector of the underlying system, goes to the product of
`L i (u i) ⊗ M i (v i)`. No normalization or nonvanishing is used. Source: Theorem 5.2,
`04-compression.tex`, lines 279–309 and 565–588. -/
theorem op_endpointWord_mulVec_slotVector_tmul (Z : P → Type) [∀ p, Fintype (Z p)]
    [∀ p, DecidableEq (Z p)] (R : SourceInventory P) (B : SlotBases R.length)
    (L : ∀ i, Matrix (B.left i) (B.left i) ℂ) (M : ∀ i, Matrix (B.right i) (B.right i) ℂ)
    (u : ∀ i, B.left i → ℂ) (v : ∀ i, B.right i → ℂ) (ψ : Config Z → ℂ) :
    ((endpointWord Z R B L M).op *ᵥ fun z ↦
        slotVector R B (fun i ↦ WithLp.toLp 2 fun a ↦ u i a.1 * v i a.2)
          (slotColumnEquiv R B Z z).1 * ψ (slotColumnEquiv R B Z z).2) =
      fun z ↦ slotVector R B (fun i ↦ WithLp.toLp 2 fun a ↦ (L i *ᵥ u i) a.1 * (M i *ᵥ v i) a.2)
        (slotColumnEquiv R B Z z).1 * ψ (slotColumnEquiv R B Z z).2 := by
  rw [op_endpointWord_mulVec_slotVector]
  have h (i : Fin R.length) : ((L i ⊗ₖ M i) *ᵥ fun a ↦ u i a.1 * v i a.2) =
      fun a ↦ (L i *ᵥ u i) a.1 * (M i *ᵥ v i) a.2 := by
    funext a
    simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
      Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  exact congrArg (fun η : ∀ i, B.left i × B.right i → ℂ ↦ fun z ↦
    slotVector R B (fun i ↦ WithLp.toLp 2 (η i)) (slotColumnEquiv R B Z z).1 *
      ψ (slotColumnEquiv R B Z z).2) (funext h)

end SourceInventory

end QuantumCircuit.Party
