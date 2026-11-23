/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.Inventory

/-!
# Preparation of all pair sources before the local operations

Every pair source of a word prepares fresh factors, on which the earlier operations do not act.
Its preparation can therefore precede those operations. This gives an exact factorization of
every word into the preparation of its sources followed by a word without sources, its *local
part* (`Word.op_localPart_mul_prepare`, `Word.op_eq_localPart_comp_prepare`).

The local part is a family of party operations `Word.localPartOp`, defined by structural
recursion on the word, with input the system `w.sources.system X` of the source list. The empty
word gives the identity; a pair source gives the relabelling of its output bases into the
canonical form `addPair` (`SourceGate.toAddPair`); a local operation gives its party family; a
composition gives the local part of the later word after the local part of the earlier one run
beside the fresh factors of the later sources (`SourceInventory.liftOps`), read through
`SourceInventory.system_append`. These computation rules hold by `rfl`.

Local maps on the two halves of a fresh source act on its vector (`Word.op_mapPair_source`,
`SourceInventory.Expands.cons_mapL`), and preparing an inventory tensors the product of its
vectors with the input (`SourceInventory.op_prepare_apply`).

## Main definitions

* `QuantumCircuit.Party.SourceInventory.Fresh`, `QuantumCircuit.Party.SourceInventory.freshEquiv`,
  `QuantumCircuit.Party.SourceInventory.vector` — the fresh configurations and the tensor
  product of the source vectors.
* `QuantumCircuit.Party.Word.localPartOp`, `QuantumCircuit.Party.Word.localPart` — the local
  part of a word.
* `QuantumCircuit.Party.pairMapMatrix`, `QuantumCircuit.Party.Word.mapPair` — maps on the two
  halves of a fresh pair.

## Main results

* `QuantumCircuit.Party.SourceInventory.op_prepare_apply`,
  `QuantumCircuit.Party.SourceInventory.op_prepare_append` — the operator of a preparation.
* `QuantumCircuit.Party.Word.op_localPart_mul_prepare`,
  `QuantumCircuit.Party.Word.op_eq_localPart_comp_prepare` — the source-first factorization.
* `QuantumCircuit.Party.Word.norm_localPartOp_le_one`,
  `QuantumCircuit.Party.Word.isAllowed_localPart` — the local part of an allowed word is allowed.
* `QuantumCircuit.Party.Word.op_mapPair_source`,
  `QuantumCircuit.Party.SourceInventory.Expands.cons_mapL` — maps on the halves of a source.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`,
  lines 68–70 and 125–127; source-gate factorization in Theorem 5.2, equation
  `eq:compression-source-gate`, lines 233–251; common private slot spaces, lines 253–267.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type}

namespace SourceInventory

variable [DecidableEq P]

/-! ### The joint vector -/

/-- The configurations of the fresh factors of an inventory: one pair per source, head first. -/
def Fresh : SourceInventory P → Type
  | [] => Unit
  | s :: S => (s.leftBasis × s.rightBasis) × Fresh S

/-- The fresh configurations are finite. -/
@[instance_reducible] def freshFintype : (S : SourceInventory P) → Fintype S.Fresh
  | [] => inferInstanceAs (Fintype Unit)
  | s :: S =>
      letI := freshFintype S
      inferInstanceAs (Fintype ((s.leftBasis × s.rightBasis) × Fresh S))

/-- The fresh configurations have decidable equality. -/
@[instance_reducible] def freshDecidableEq : (S : SourceInventory P) → DecidableEq S.Fresh
  | [] => inferInstanceAs (DecidableEq Unit)
  | s :: S =>
      letI := freshDecidableEq S
      inferInstanceAs (DecidableEq ((s.leftBasis × s.rightBasis) × Fresh S))

/-- The fresh configurations of an inventory are finite. -/
instance (S : SourceInventory P) : Fintype S.Fresh := freshFintype S

/-- The fresh configurations of an inventory have decidable equality. -/
instance (S : SourceInventory P) : DecidableEq S.Fresh := freshDecidableEq S

/-- A configuration of the prepared system is a fresh configuration and one of the input. -/
def freshEquiv : (S : SourceInventory P) → (X : P → Type) →
    Config (S.system X) ≃ S.Fresh × Config X
  | [], _ => (Equiv.punitProd _).symm
  | s :: S, X =>
      (addPairConfigEquiv (X := system S X) s.distinct s.leftBasis s.rightBasis).trans
        (((Equiv.refl _).prodCongr (freshEquiv S X)).trans
          (Equiv.prodAssoc _ _ _).symm)

/-- The coefficients of the tensor product of the source vectors. -/
noncomputable def vectorFun : (S : SourceInventory P) → S.Fresh → ℂ
  | [] => fun _ ↦ 1
  | s :: S => fun f ↦ s.vector f.1 * vectorFun S f.2

/-- The tensor product of the source vectors. Source: Lemma 5.1,
`04-compression.tex`, lines 125–127. -/
noncomputable def vector (S : SourceInventory P) : EuclideanSpace ℂ S.Fresh :=
  WithLp.toLp 2 (vectorFun S)

omit [DecidableEq P] in
/-- The joint vector of normalized sources is normalized. -/
theorem norm_vector {S : SourceInventory P} (hS : S.IsNormalized) : ‖S.vector‖ = 1 := by
  induction S with
  | nil =>
    change ‖(WithLp.toLp 2 fun _ : Unit ↦ (1 : ℂ) : EuclideanSpace ℂ Unit)‖ = 1
    simp [EuclideanSpace.norm_eq]
  | cons s S ih =>
    rw [isNormalized_cons] at hS
    have h : ‖SourceInventory.vector (s :: S)‖ ^ 2 =
        (‖s.vector‖ * ‖SourceInventory.vector S‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq,
        EuclideanSpace.norm_sq_eq, Finset.sum_mul_sum, ← Finset.sum_product',
        Finset.univ_product_univ]
      simp only [vector, vectorFun, PiLp.toLp_apply, norm_mul, mul_pow]
      rfl
    rw [ih hS.2, hS.1, mul_one, one_pow] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- The fresh configuration of a cons inventory: that of the head source and that of the tail. -/
theorem freshEquiv_cons_apply (s : PairSource P) (S : SourceInventory P) (X : P → Type)
    (z : Config (system (s :: S) X)) :
    freshEquiv (s :: S) X z =
      (((addPairConfigEquiv (X := system S X) s.distinct s.leftBasis s.rightBasis z).1,
        (freshEquiv S X (addPairConfigEquiv (X := system S X) s.distinct s.leftBasis
          s.rightBasis z).2).1),
        (freshEquiv S X (addPairConfigEquiv (X := system S X) s.distinct s.leftBasis
          s.rightBasis z).2).2) :=
  rfl

omit [DecidableEq P] in
/-- The joint vector of a cons inventory is the head vector times the joint vector of the tail. -/
theorem vector_cons_apply (s : PairSource P) (S : SourceInventory P)
    (f : (s.leftBasis × s.rightBasis) × S.Fresh) :
    SourceInventory.vector (s :: S) f = s.vector f.1 * SourceInventory.vector S f.2 :=
  rfl

variable [Fintype P] {X : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- **Preparing the sources tensors their joint vector with the input**. Source: Theorem 5.2,
`eq:compression-source-gate`, `04-compression.tex`, lines 233–248. -/
theorem op_prepare_apply (S : SourceInventory P) (z : Config (S.system X)) (x : Config X) :
    (S.prepare X).op z x =
      if (S.freshEquiv X z).2 = x then S.vector (S.freshEquiv X z).1 else 0 := by
  induction S with
  | nil =>
    exact (Matrix.one_apply (n := Config X) (α := ℂ) (i := z) (j := x)).trans rfl
  | cons s S ih =>
    rw [op_prepare_cons, Word.op_sourceAt]
    refine (prepMatrix_mul_apply (addPairConfigEquiv (X := system S X) s.distinct s.leftBasis
      s.rightBasis) s.vector (prepare S X).op z x).trans ?_
    rw [ih, freshEquiv_cons_apply, vector_cons_apply]
    split_ifs <;> simp

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- The relabelling along the identification of equal bases is the identity. -/
private theorem op_relabel_cast_self {Y : P → Type} [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (h : ∀ p, Y p = Y p) :
    Word.op (PartyCircuit.relabel (G := SourceGate) fun p ↦ Equiv.cast (h p)) = 1 := by
  simp only [Word.op, PartyCircuit.op_relabel, Equiv.cast_refl, Equiv.piCongrRight_refl,
    Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- A pair source commutes with the identification of equal systems. -/
private theorem op_relabel_cast_sourceAt {Y Y' : P → Type} [iF : ∀ p, Fintype (Y p)]
    [iD : ∀ p, DecidableEq (Y p)] [iF' : ∀ p, Fintype (Y' p)] [iD' : ∀ p, DecidableEq (Y' p)]
    (h : ∀ p, Y p = Y' p) {p q : P} (hpq : p ≠ q) (α β : Type) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (η : EuclideanSpace ℂ (α × β))
    (h' : ∀ s, addPair Y hpq α β s = addPair Y' hpq α β s) :
    Word.op (PartyCircuit.relabel (G := SourceGate) fun s ↦ Equiv.cast (h' s).symm) *
        (Word.sourceAt hpq α β η Y).op =
      (Word.sourceAt hpq α β η Y').op *
        Word.op (PartyCircuit.relabel (G := SourceGate) fun s ↦ Equiv.cast (h s).symm) := by
  obtain rfl : Y = Y' := funext h
  obtain rfl : iF = iF' := Subsingleton.elim _ _
  obtain rfl : iD = iD' := Subsingleton.elim _ _
  rw [op_relabel_cast_self, op_relabel_cast_self, Matrix.one_mul, Matrix.mul_one]

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- `op_prepare_cons` with the output read in the form `addPair`. -/
private theorem op_prepare_cons' {X : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (s : PairSource P) (S : SourceInventory P) :
    Word.op (Y := addPair (system S X) s.distinct s.leftBasis s.rightBasis) (prepare (s :: S) X) =
      (Word.sourceAt s.distinct s.leftBasis s.rightBasis s.vector (S.system X)).op *
        (prepare S X).op := by
  rw [prepare_cons]
  exact PartyCircuit.op_comp _ _ _

/-- Preparation of a concatenation first prepares the second list and then the first; the
identification of `system (S ++ T) X` with `system S (system T X)` is a relabelling. -/
theorem op_prepare_append (S T : SourceInventory P) :
    Word.op (PartyCircuit.relabel (G := SourceGate)
        fun p ↦ Equiv.cast (congrFun (system_append S T X) p).symm) * (prepare (S ++ T) X).op =
      Word.op ((T.prepare X).comp (S.prepare (T.system X))) := by
  rw [Word.op_comp]
  induction S with
  | nil =>
      change Word.op (PartyCircuit.relabel (G := SourceGate) fun p ↦
          Equiv.cast (rfl : system T X p = system T X p)) * (prepare T X).op =
            (prepare [] (system T X)).op * (prepare T X).op
      rw [op_relabel_cast_self]
      rfl
  | cons s S ih =>
      have h' : ∀ p, addPair (system (S ++ T) X) s.distinct s.leftBasis s.rightBasis p =
          addPair (system S (system T X)) s.distinct s.leftBasis s.rightBasis p :=
        fun p ↦ congrFun (system_append (s :: S) T X) p
      change Word.op (PartyCircuit.relabel (G := SourceGate) fun p ↦ Equiv.cast (h' p).symm) *
          Word.op (Y := addPair (system (S ++ T) X) s.distinct s.leftBasis s.rightBasis)
            (prepare (s :: (S ++ T)) X) =
        Word.op (Y := addPair (system S (system T X)) s.distinct s.leftBasis s.rightBasis)
            (prepare (s :: S) (system T X)) * (prepare T X).op
      rw [op_prepare_cons', op_prepare_cons', ← Matrix.mul_assoc,
        op_relabel_cast_sourceAt (congrFun (system_append S T X)) _ _ _ _ h', Matrix.mul_assoc, ih,
        Matrix.mul_assoc]

end SourceInventory

/-! ### The local part -/

namespace Word

variable [DecidableEq P]

/-- The party operations remaining after all sources of a word have been prepared in fresh
factors, by structural recursion on the word. Source:
Theorem 5.2, `eq:compression-source-gate`, `04-compression.tex`, lines 246–251. -/
def localPartOp : {X Y : P → Type} → [∀ p, DecidableEq (X p)] → (w : Word X Y) →
    ∀ p, Matrix (Y p) (SourceInventory.system (Word.sources w) X p) ℂ
  | _, _, _, PartyCircuit.done X => fun p ↦ (1 : Matrix (X p) (X p) ℂ)
  | _, _, _, PartyCircuit.gate _ _ g => fun p ↦ (g.toAddPair p).toPEquiv.toMatrix
  | _, _, _, PartyCircuit.localOp p hY A => PartyCircuit.localOpFamily p hY A
  | _, _, _, PartyCircuit.localOps A => A
  | X, _, _, PartyCircuit.comp w w' => fun p ↦
      (localPartOp w' p * (Word.sources w').liftOps (localPartOp w) p).submatrix id
        (Equiv.cast (congrFun (SourceInventory.system_append (Word.sources w')
          (Word.sources w) X) p))

variable {X Y Z : P → Type} [∀ p, DecidableEq (X p)]

/-- The local part of the empty word is the identity. -/
@[simp] theorem localPartOp_done (p : P) :
    localPartOp (PartyCircuit.done X : Word X X) p = (1 : Matrix (X p) (X p) ℂ) :=
  rfl

/-- The local part of one pair source relabels its output into the canonical form `addPair`. -/
@[simp] theorem localPartOp_gate [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] {D : Finset P}
    (hY : ∀ s ∉ D, Y s = X s) (g : SourceGate D X Y) (p : P) :
    localPartOp (PartyCircuit.gate D hY g : Word X Y) p = (g.toAddPair p).toPEquiv.toMatrix :=
  rfl

/-- The local part of one local operation is its party family. -/
@[simp] theorem localPartOp_localOp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (q : P)
    (hY : ∀ s ≠ q, Y s = X s) (A : Matrix (Y q) (X q) ℂ) :
    localPartOp (PartyCircuit.localOp q hY A : Word X Y) = PartyCircuit.localOpFamily q hY A :=
  rfl

/-- The local part of local operations at every party is themselves. -/
@[simp] theorem localPartOp_localOps [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (A : ∀ p, Matrix (Y p) (X p) ℂ) :
    localPartOp (PartyCircuit.localOps A : Word X Y) = A :=
  rfl

/-- The local part of a composition: the local part of the first word run beside the fresh
factors of the sources of the second, then the local part of the second, read through
`SourceInventory.system_append`. -/
theorem localPartOp_comp [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (w : Word X Y)
    (w' : Word Y Z) (p : P) :
    localPartOp (PartyCircuit.comp w w') p =
      (w'.localPartOp p * w'.sources.liftOps w.localPartOp p).submatrix id
        (Equiv.cast (congrFun (SourceInventory.system_append w'.sources w.sources X) p)) :=
  rfl

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The local part as a word without sources. Source: Theorem 5.2,
`eq:compression-source-gate`, `04-compression.tex`, lines 246–251. -/
def localPart (w : Word X Y) : Word (w.sources.system X) Y :=
  PartyCircuit.localOps w.localPartOp

/-- The local part contains no pair sources. -/
@[simp] theorem sources_localPart (w : Word X Y) : w.localPart.sources = [] :=
  rfl

variable [Fintype P] [∀ p, Fintype (X p)]

/-- The operator of the local part is the Kronecker product of the party operations. -/
@[simp] theorem op_localPart (w : Word X Y) : w.localPart.op = piKronecker w.localPartOp :=
  PartyCircuit.op_localOps _ _

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- A Kronecker product with its columns read through bijections is the product with the matrix
of the bijection of configurations. -/
private theorem piKronecker_submatrix_cast {A B Z : P → Type} [∀ p, Fintype (B p)]
    [∀ p, DecidableEq (B p)] [∀ p, Fintype (A p)] [∀ p, DecidableEq (A p)]
    (M : ∀ p, Matrix (Z p) (B p) ℂ) (h : ∀ p, A p = B p) :
    piKronecker (fun p ↦ (M p).submatrix id (Equiv.cast (h p))) =
      piKronecker M * (PartyCircuit.relabel (G := SourceGate) fun p ↦ Equiv.cast (h p).symm).op
        SourceGate.ev := by
  rw [PartyCircuit.op_relabel, PEquiv.mul_toMatrix_toPEquiv]
  rfl

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The empty word: the local part is the identity. -/
private theorem piKronecker_localPartOp_mul_prepare_done :
    piKronecker (localPartOp (PartyCircuit.done X : Word X X)) *
      (SourceInventory.prepare (Word.sources (PartyCircuit.done X : Word X X)) X).op =
        Word.op (PartyCircuit.done X : Word X X) :=
  (Matrix.mul_one _).trans piKronecker_one

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- One pair source: its local part relabels the output of the canonical source. -/
private theorem piKronecker_localPartOp_mul_prepare_gate {D : Finset P} [∀ p, Fintype (Y p)]
    [∀ p, DecidableEq (Y p)] (hY : ∀ s ∉ D, Y s = X s) (g : SourceGate D X Y) :
    piKronecker (localPartOp (PartyCircuit.gate D hY g : Word X Y)) *
      (SourceInventory.prepare (Word.sources (PartyCircuit.gate D hY g : Word X Y)) X).op =
        Word.op (PartyCircuit.gate D hY g) := by
  have h := op_source_eq_op_relabel_mul g
  rw [PartyCircuit.relabel, PartyCircuit.op_localOps] at h
  have hp : (SourceInventory.prepare (Word.sources (PartyCircuit.gate D hY g : Word X Y)) X).op =
      (sourceAt g.distinct g.leftBasis g.rightBasis g.vector X).op :=
    (SourceInventory.op_prepare_cons g.toPairSource [] (X := X)).trans (Matrix.mul_one _)
  rw [hp]
  exact h.symm

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The composition step of the source-first factorization, with the inventory of the
composition written as `w'.sources ++ w.sources`. -/
private theorem piKronecker_localPartOp_mul_prepare_comp [∀ p, Fintype (Y p)]
    [∀ p, DecidableEq (Y p)] (w : Word X Y) (w' : Word Y Z)
    (hw : piKronecker w.localPartOp * (w.sources.prepare X).op = w.op)
    (hw' : piKronecker w'.localPartOp * (w'.sources.prepare Y).op = w'.op) :
    piKronecker (fun p ↦ (localPartOp w' p * (Word.sources w').liftOps (localPartOp w) p).submatrix
        id (Equiv.cast (congrFun (SourceInventory.system_append (Word.sources w')
          (Word.sources w) X) p))) *
      (SourceInventory.prepare (Word.sources w' ++ Word.sources w) X).op = w'.op * w.op := by
  have hT := SourceInventory.op_prepare_mul_piKronecker (Word.sources w') (localPartOp w)
    (X := SourceInventory.system (Word.sources w) X)
  have hA := SourceInventory.op_prepare_append (Word.sources w') (Word.sources w) (X := X)
  rw [Word.op_comp] at hA
  rw [piKronecker_submatrix_cast, ← piKronecker_mul, Matrix.mul_assoc, hA, ← Matrix.mul_assoc,
    Matrix.mul_assoc (piKronecker _) (piKronecker _), ← hT, ← Matrix.mul_assoc, hw',
    Matrix.mul_assoc, hw]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **Source-first factorization, party form.** The Kronecker product of the local part after the
preparation of all sources is the operator of the word. -/
theorem piKronecker_localPartOp_mul_prepare : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) →
      piKronecker w.localPartOp * (w.sources.prepare X).op = w.op
  | _, _, _, _, PartyCircuit.done _ => piKronecker_localPartOp_mul_prepare_done
  | _, _, _, _, PartyCircuit.gate _ hY g => piKronecker_localPartOp_mul_prepare_gate hY g
  | _, _, _, _, PartyCircuit.localOp q hY A =>
    (Matrix.mul_one _).trans (PartyCircuit.op_localOp_eq_piKronecker _ q hY A).symm
  | _, _, _, _, PartyCircuit.localOps A =>
    (Matrix.mul_one _).trans (PartyCircuit.op_localOps _ A).symm
  | _, _, _, _, PartyCircuit.comp w w' =>
    (piKronecker_localPartOp_mul_prepare_comp w w' (piKronecker_localPartOp_mul_prepare w)
      (piKronecker_localPartOp_mul_prepare w')).trans (Word.op_comp w w').symm

/-- **Source-first factorization.** Preparing every pair source first and then applying the
local part gives exactly the operator of the word; no normalization or contraction hypothesis
is needed. Source: Theorem 5.2, `eq:compression-source-gate`,
`04-compression.tex`, lines 246–251. -/
theorem op_localPart_mul_prepare (w : Word X Y) :
    w.localPart.op * (w.sources.prepare X).op = w.op := by
  rw [op_localPart]
  exact piKronecker_localPartOp_mul_prepare w

/-- Every word is the preparation of its pair sources followed by a word with no pair sources.
Source: Theorem 5.2, `eq:compression-source-gate`, `04-compression.tex`, lines 246–251. -/
theorem op_eq_localPart_comp_prepare (w : Word X Y) :
    w.op = Word.op ((w.sources.prepare X).comp w.localPart) :=
  (op_localPart_mul_prepare w).symm.trans (Word.op_comp _ _).symm

omit [Fintype P] [∀ p, DecidableEq (Y p)] in
/-- The party operations of the local part of an allowed word are contractions. -/
theorem norm_localPartOp_le_one : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] → {w : Word X Y} → w.IsAllowed → ∀ p,
      ‖w.localPartOp p‖ ≤ 1
  | X, _, iF, _, iF', PartyCircuit.done _, _, p => by
    obtain rfl : iF = iF' := Subsingleton.elim _ _
    exact (IsStarProjection.one (Matrix (X p) (X p) ℂ)).norm_le
  | _, _, _, _, iF, @PartyCircuit.gate _ _ _ _ iF' _ _ _ g, _, p => by
    obtain rfl : iF = iF' := Subsingleton.elim _ _
    exact l2_opNorm_toMatrix_toPEquiv_le (g.toAddPair p)
  | _, _, _, _, iF, @PartyCircuit.localOp _ _ _ _ iF' _ q hY A, hw, p => by
    obtain rfl : iF = iF' := Subsingleton.elim _ _
    exact PartyCircuit.norm_localOpFamily_le_one q hY hw p
  | _, _, _, _, iF, @PartyCircuit.localOps _ _ _ _ iF' _ A, hw, p => by
    obtain rfl : iF = iF' := Subsingleton.elim _ _
    exact hw p
  | X, _, _, _, _, PartyCircuit.comp w w', hw, p => by
    change ‖(localPartOp w' p * (Word.sources w').liftOps (localPartOp w) p).submatrix id
      (Equiv.cast (congrFun (SourceInventory.system_append (Word.sources w') (Word.sources w)
        X) p))‖ ≤ 1
    refine (l2_opNorm_reindex_le (Equiv.refl _)
      (Equiv.cast (congrFun (SourceInventory.system_append (Word.sources w') (Word.sources w)
        X) p)).symm _).trans ((l2_opNorm_mul _ _).trans ?_)
    have h₁ := norm_localPartOp_le_one hw.2 p
    have h₂ := (SourceInventory.norm_liftOps_le (Word.sources w') (localPartOp w) p).trans
      (norm_localPartOp_le_one hw.1 p)
    nlinarith [norm_nonneg (localPartOp w' p),
      norm_nonneg ((Word.sources w').liftOps (localPartOp w) p)]

omit [Fintype P] in
/-- Moving preparations to the beginning preserves allowedness. -/
theorem isAllowed_localPart {w : Word X Y} (hw : w.IsAllowed) : w.localPart.IsAllowed :=
  fun p ↦ norm_localPartOp_le_one hw p

end Word

/-! ### Local maps on the two halves of a fresh source -/

section PairMaps

variable [DecidableEq P] {p q : P} (hpq : p ≠ q) {α β α' β' : Type}

/-- The maps `A` on the fresh factor at `p` and `B` on the fresh factor at `q`, read on the
fresh factors of `addPair` alone (`pairFactor`): the identity of the one basis vector
elsewhere. -/
def pairFactorMatrix (A : Matrix α' α ℂ) (B : Matrix β' β ℂ) (s : P) :
    Matrix (pairFactor hpq α' β' s) (pairFactor hpq α β s) ℂ :=
  if hp : s = p then
    reindex (Equiv.cast (by simp [pairFactor, hp])) (Equiv.cast (by simp [pairFactor, hp])) A
  else if hq : s = q then
    reindex (Equiv.cast (by simp [pairFactor, hq, hpq.symm]))
      (Equiv.cast (by simp [pairFactor, hq, hpq.symm])) B
  else
    reindex (Equiv.cast (by simp [pairFactor, hp, hq])) (Equiv.cast (by simp [pairFactor, hp, hq]))
      (1 : Matrix Unit Unit ℂ)

/-- The product of the fresh-factor maps over all parties is `A ⊗ B`, read along
`pairFactorConfigEquiv`. -/
theorem prod_pairFactorMatrix [Fintype P] (A : Matrix α' α ℂ) (B : Matrix β' β ℂ)
    (a' : Config (pairFactor hpq α' β')) (a : Config (pairFactor hpq α β)) :
    ∏ s, pairFactorMatrix hpq A B s (a' s) (a s) =
      (A ⊗ₖ B) (pairFactorConfigEquiv hpq α' β' a') (pairFactorConfigEquiv hpq α β a) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩),
    Finset.prod_eq_one, mul_one]
  · simp [pairFactorMatrix, hpq.symm, pairFactorConfigEquiv, kroneckerMap_apply]
    rfl
  · intro s hs
    obtain ⟨hsq, hs'⟩ := Finset.mem_erase.mp hs
    obtain ⟨hsp, -⟩ := Finset.mem_erase.mp hs'
    simp [pairFactorMatrix, hsp, hsq]

/-- The fresh-factor maps of two contractions are contractions. -/
theorem norm_pairFactorMatrix_le [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype α'] [Fintype β'] {A : Matrix α' α ℂ} {B : Matrix β' β ℂ} (hA : ‖A‖ ≤ 1)
    (hB : ‖B‖ ≤ 1) (s : P) : ‖pairFactorMatrix hpq A B s‖ ≤ 1 := by
  unfold pairFactorMatrix
  split_ifs
  · exact (l2_opNorm_reindex_le _ _ _).trans hA
  · exact (l2_opNorm_reindex_le _ _ _).trans hB
  · exact (l2_opNorm_reindex_le _ _ _).trans (IsStarProjection.one (Matrix Unit Unit ℂ)).norm_le

variable {X : P → Type} [∀ s, DecidableEq (X s)]

/-- The maps `A` on the fresh factor at `p` and `B` on the fresh factor at `q`, the identity
elsewhere: `pairFactorMatrix ⊗ 1` at every party, read through `addPairSiteEquiv`. -/
def pairMapMatrix (A : Matrix α' α ℂ) (B : Matrix β' β ℂ) (s : P) :
    Matrix (addPair X hpq α' β' s) (addPair X hpq α β s) ℂ :=
  reindex (addPairSiteEquiv hpq α' β' X s).symm (addPairSiteEquiv hpq α β X s).symm
    (pairFactorMatrix hpq A B s ⊗ₖ (1 : Matrix (X s) (X s) ℂ))

/-- The endpoint maps of two contractions are contractions. -/
theorem norm_pairMapMatrix_le [∀ s, Fintype (X s)] [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype α'] [Fintype β'] {A : Matrix α' α ℂ} {B : Matrix β' β ℂ}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (s : P) : ‖pairMapMatrix hpq A B (X := X) s‖ ≤ 1 :=
  (l2_opNorm_reindex_le _ _ _).trans (l2_opNorm_kronecker_le_one
    (norm_pairFactorMatrix_le hpq hA hB s) (IsStarProjection.one (Matrix (X s) (X s) ℂ)).norm_le)

/-- **The product of the endpoint maps over all parties** is `(A ⊗ B) ⊗ 1`, read along
`addPairConfigEquiv`. -/
theorem piKronecker_pairMapMatrix [Fintype P] (A : Matrix α' α ℂ) (B : Matrix β' β ℂ) :
    piKronecker (pairMapMatrix hpq A B (X := X)) =
      reindex (addPairConfigEquiv (X := X) hpq α' β').symm
        (addPairConfigEquiv (X := X) hpq α β).symm
        ((A ⊗ₖ B) ⊗ₖ (1 : Matrix (Config X) (Config X) ℂ)) := by
  ext y z
  rw [addPairConfigEquiv_eq_siteEquiv, addPairConfigEquiv_eq_siteEquiv]
  simp only [piKronecker_apply, pairMapMatrix, reindex_apply, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    Equiv.piCongrRight_apply, Equiv.arrowProdEquivProdArrow_apply, Finset.prod_mul_distrib,
    one_apply, Finset.prod_boole, Finset.mem_univ, forall_const, prod_pairFactorMatrix]
  congr 1
  exact if_congr ⟨fun h ↦ funext h, fun h s ↦ congrFun h s⟩ rfl rfl

variable [∀ s, Fintype (X s)]

/-- Apply one map at each endpoint of a fresh pair, leaving everything else untouched. Source:
`04-compression.tex`, lines 253–267. -/
def Word.mapPair [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype α']
    [DecidableEq α'] [Fintype β'] [DecidableEq β'] (A : Matrix α' α ℂ) (B : Matrix β' β ℂ)
    (X : P → Type)
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] :
    Word (addPair X hpq α β) (addPair X hpq α' β') :=
  PartyCircuit.localOps (pairMapMatrix hpq A B)

/-- Local contractions give an allowed word containing no pair sources. Source:
`04-compression.tex`, lines 253–267. -/
theorem Word.mapPair_spec [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype α']
    [DecidableEq α'] [Fintype β'] [DecidableEq β'] (A : Matrix α' α ℂ) (B : Matrix β' β ℂ)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) :
    (Word.mapPair hpq A B X).IsAllowed ∧ (Word.mapPair hpq A B X).sources = [] :=
  ⟨fun s ↦ norm_pairMapMatrix_le (X := X) hpq hA hB s, rfl⟩

variable [Fintype P]

/-- Applying the endpoint maps after preparation transforms exactly the source vector. Source:
`04-compression.tex`, lines 253–267. -/
theorem Word.op_mapPair_source [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β'] (A : Matrix α' α ℂ)
    (B : Matrix β' β ℂ) (η : EuclideanSpace ℂ (α × β)) :
    (Word.mapPair hpq A B X).op * (Word.sourceAt hpq α β η X).op =
      (Word.sourceAt hpq α' β' (EuclideanSpace.pairMap A B η) X).op := by
  rw [Word.op_sourceAt, Word.op_sourceAt]
  unfold Word.op
  rw [Word.mapPair, PartyCircuit.op_localOps, piKronecker_pairMapMatrix]
  ext y x
  rw [mul_apply, ← (addPairConfigEquiv (X := X) hpq α β).symm.sum_comp, Fintype.sum_prod_type]
  simp [kroneckerMap_apply, one_apply, EuclideanSpace.pairMap, mulVec, dotProduct]

end PairMaps

/-- Apply two local contractions to the first prepared pair, retaining the source tail and all
spectator factors; no normalization is required. Source: Theorem 5.2,
`04-compression.tex`, lines 253–267. -/
theorem SourceInventory.Expands.cons_mapL [Fintype P] [DecidableEq P] (r : PairSource P)
    (α β α' β' : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype α']
    [DecidableEq α'] [Fintype β'] [DecidableEq β'] (A : Matrix α' α ℂ) (B : Matrix β' β ℂ)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (η : EuclideanSpace ℂ (α × β)) (T : SourceInventory P) :
    SourceInventory.Expands
      ({ left := r.left, right := r.right, distinct := r.distinct, leftBasis := α,
          rightBasis := β, vector := η } :: T)
      ({ left := r.left, right := r.right, distinct := r.distinct, leftBasis := α',
          rightBasis := β', vector := EuclideanSpace.pairMap A B η } :: T) := by
  intro X _ _
  obtain ⟨hw, hs⟩ := Word.mapPair_spec r.distinct (X := T.system X) A B hA hB
  refine ⟨Word.mapPair r.distinct A B (T.system X), hw, hs, ?_⟩
  rw [SourceInventory.op_prepare_cons, SourceInventory.op_prepare_cons]
  exact (Matrix.mul_assoc _ _ _).symm.trans
    (congrArg (· * (T.prepare X).op) (Word.op_mapPair_source r.distinct A B η))

end QuantumCircuit.Party
