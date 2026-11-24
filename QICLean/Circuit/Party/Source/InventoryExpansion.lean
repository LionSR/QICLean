/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.Combination
import QICLean.Circuit.Party.Syntax.Local

/-!
# Source inventories: preparation and expansion

A source inventory `S` is prepared on top of a system `X` by the word
`S.prepare X : Word X (S.system X)`, the last source of the list first: the head source of the
list is prepared last, with its fresh factors in front. An inventory `G` *expands* to `S` when,
for every spectator system `X`, an allowed word without pair sources carries the preparation of
`G` to the preparation of `S` (`SourceInventory.Expands`). Expansion is reflexive and
transitive, can be carried out beside a common source, and allows reversing the endpoint order
of a source, splitting a combined source and exchanging two sources; hence it allows every
permutation of the sources (`SourceInventory.Expands.of_perm`).

Every Hilbert space of the source is finite dimensional (`04-compression.tex`, lines 17–19), so
the fresh factors are finite basis types `α`, `β` and the source vectors lie in
`EuclideanSpace ℂ (α × β)`.

## Main definitions

* `QuantumCircuit.Party.PairSource.reverse`, `QuantumCircuit.Party.PairSource.combine`,
  `QuantumCircuit.Party.PairSource.unit` — reversed, combined and scalar sources.
* `QuantumCircuit.Party.SourceInventory.system`, `QuantumCircuit.Party.SourceInventory.prepare`
  — the preparation of an inventory.
* `QuantumCircuit.Party.SourceInventory.systemEquivOfEqNil` — the system prepared by an empty
  inventory.
* `QuantumCircuit.Party.SourceInventory.liftOps` — party operations beside the fresh factors.
* `QuantumCircuit.Party.SourceInventory.Expands` — expansion of one inventory into another.

## Main results

* `QuantumCircuit.Party.SourceInventory.op_prepare_mul_piKronecker` — a preparation commutes
  with party operations on the existing factors.
* `QuantumCircuit.Party.SourceInventory.liftOps_append`,
  `QuantumCircuit.Party.SourceInventory.liftOps_eq_cast` — party operations beside the fresh
  factors of a concatenation, and beside the fresh factors of an identification of equal bases.
* `QuantumCircuit.Party.SourceInventory.isAllowed_prepare_iff` — a preparation is allowed
  exactly when its vectors are normalized.
* `QuantumCircuit.Party.SourceInventory.Expands.cons`, `Expands.reverse`, `Expands.combine`,
  `Expands.swap`, `Expands.of_perm` — the closure properties of expansion.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`,
  lines 68–70 and 125–127; equation `eq:compression-source-gate`, lines 233–267.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type}

namespace PairSource

/-- The same source with its endpoint order reversed. -/
noncomputable def reverse (s : PairSource P) : PairSource P where
  left := s.right
  right := s.left
  distinct := s.distinct.symm
  leftBasis := s.rightBasis
  rightBasis := s.leftBasis
  vector := EuclideanSpace.pairSwap s.vector

/-- Reversing a source keeps its unordered pair of endpoints. -/
@[simp] theorem partyPair_reverse (s : PairSource P) : s.reverse.partyPair = s.partyPair :=
  Sym2.eq_swap

/-- Reversing a source keeps the norm of its vector. -/
@[simp] theorem norm_reverse_vector (s : PairSource P) : ‖s.reverse.vector‖ = ‖s.vector‖ :=
  EuclideanSpace.norm_pairSwap _

/-- Combine two sources with the same ordered endpoints: the bases multiply and the vectors
combine (`EuclideanSpace.pairCombine`). Source: Lemma 5.1, `04-compression.tex`,
lines 125–127. -/
def combine (s t : PairSource P) (_hLeft : s.left = t.left) (_hRight : s.right = t.right) :
    PairSource P where
  left := s.left
  right := s.right
  distinct := s.distinct
  leftBasis := s.leftBasis × t.leftBasis
  rightBasis := s.rightBasis × t.rightBasis
  vector := EuclideanSpace.pairCombine s.vector t.vector

/-- Combining two sources on the same endpoints keeps their unordered pair. -/
@[simp] theorem partyPair_combine (s t : PairSource P) (hLeft : s.left = t.left)
    (hRight : s.right = t.right) : (s.combine t hLeft hRight).partyPair = s.partyPair :=
  rfl

/-- The vector of a combined source has the product of the two norms. -/
@[simp] theorem norm_combine_vector (s t : PairSource P) (hLeft : s.left = t.left)
    (hRight : s.right = t.right) :
    ‖(s.combine t hLeft hRight).vector‖ = ‖s.vector‖ * ‖t.vector‖ :=
  EuclideanSpace.norm_pairCombine _ _

/-- The normalized scalar source on an otherwise unused pair of parties: both fresh bases are
`Unit`. Source: `eq:compression-source-gate`,
`04-compression.tex`, lines 243–245. -/
noncomputable def unit (p q : P) (hpq : p ≠ q) : PairSource P where
  left := p
  right := q
  distinct := hpq
  leftBasis := Unit
  rightBasis := Unit
  vector := EuclideanSpace.single ((), ()) 1

/-- The unit source on `p` and `q` lies on the unordered pair `{p, q}`. -/
@[simp] theorem partyPair_unit (p q : P) (hpq : p ≠ q) :
    (PairSource.unit p q hpq).partyPair = s(p, q) :=
  rfl

/-- The scalar pair vector has norm one. Source: `04-compression.tex`, lines 243–245. -/
@[simp] theorem norm_unit_vector (p q : P) (hpq : p ≠ q) :
    ‖(PairSource.unit p q hpq).vector‖ = 1 :=
  (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Unit × Unit)).1 ((), ())

/-- Both fresh bases of the scalar source have one element. Source: `04-compression.tex`,
lines 243–245. -/
theorem card_unit_bases (p q : P) (hpq : p ≠ q) :
    Fintype.card (PairSource.unit p q hpq).leftBasis = 1 ∧
      Fintype.card (PairSource.unit p q hpq).rightBasis = 1 :=
  ⟨Fintype.card_unit, Fintype.card_unit⟩

end PairSource

namespace SourceInventory

/-! ### Preparation of an inventory -/

variable [DecidableEq P]

/-- The system after preparing the inventory on top of `X`: the fresh factors of the head source
in front. -/
def system : SourceInventory P → (P → Type) → P → Type
  | [], X => X
  | s :: S, X => addPair (system S X) s.distinct s.leftBasis s.rightBasis

/-- Preparing no source leaves the system unchanged. -/
@[simp] theorem system_nil (X : P → Type) : system ([] : SourceInventory P) X = X :=
  rfl

/-- Preparing a cons inventory adds the fresh factors of the head source on top of the system
prepared by the tail. -/
theorem system_cons (s : PairSource P) (S : SourceInventory P) (X : P → Type) :
    system (s :: S) X = addPair (system S X) s.distinct s.leftBasis s.rightBasis :=
  rfl

/-- Preparing a concatenation prepares the second list first, then the first. -/
theorem system_append (S T : SourceInventory P) (X : P → Type) :
    system (S ++ T) X = system S (system T X) := by
  induction S with
  | nil => rfl
  | cons s S ih => simp only [List.cons_append, system_cons, ih]

/-- The system prepared by an empty inventory is the system itself; by cases on the inventory,
so that the identification is the identity on the empty list by `rfl`. -/
def systemEquivOfEqNil : (S : SourceInventory P) → S = [] → (X : P → Type) → ∀ p,
    S.system X p ≃ X p
  | [], _, _, _ => Equiv.refl _
  | _ :: _, h, _, _ => (List.cons_ne_nil _ _ h).elim

/-- On the empty inventory the identification of the prepared system is the identity. -/
@[simp] theorem systemEquivOfEqNil_nil (h : ([] : SourceInventory P) = []) (X : P → Type)
    (p : P) : systemEquivOfEqNil [] h X p = Equiv.refl (X p) :=
  rfl

/-- The finiteness of the bases of a prepared system. -/
@[instance_reducible] def systemFintype : (S : SourceInventory P) → (X : P → Type) →
    (∀ p, Fintype (X p)) → ∀ p, Fintype (system S X p)
  | [], _, h => h
  | s :: S, X, h =>
      letI := systemFintype S X h
      fun p ↦ inferInstanceAs (Fintype (addPair (system S X) s.distinct s.leftBasis
        s.rightBasis p))

/-- The decidable equality of the bases of a prepared system. -/
@[instance_reducible] def systemDecidableEq : (S : SourceInventory P) → (X : P → Type) →
    (∀ p, DecidableEq (X p)) → ∀ p, DecidableEq (system S X p)
  | [], _, h => h
  | s :: S, X, h =>
      letI := systemDecidableEq S X h
      fun p ↦ inferInstanceAs (DecidableEq (addPair (system S X) s.distinct s.leftBasis
        s.rightBasis p))

/-- The bases of a prepared system are finite. -/
instance instFintypeSystem (S : SourceInventory P) (X : P → Type) [h : ∀ p, Fintype (X p)]
    (p : P) : Fintype (S.system X p) :=
  systemFintype S X h p

/-- The bases of a prepared system have decidable equality. -/
instance instDecidableEqSystem (S : SourceInventory P) (X : P → Type)
    [h : ∀ p, DecidableEq (X p)] (p : P) : DecidableEq (S.system X p) :=
  systemDecidableEq S X h p

/-- Preparation of the listed sources on top of `X`, the last source first. Source: Theorem 5.2,
`eq:compression-source-gate`, `04-compression.tex`, lines 233–248. -/
def prepare (S : SourceInventory P) (X : P → Type) [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] : Word X (S.system X) :=
  match S with
  | [] => PartyCircuit.done X
  | s :: S =>
      (prepare S X).comp (Word.sourceAt s.distinct s.leftBasis s.rightBasis s.vector (system S X))

variable {X : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The preparation of a cons inventory: the tail first, then the head source. -/
theorem prepare_cons (s : PairSource P) (S : SourceInventory P) :
    prepare (s :: S) X =
      (prepare S X).comp
        (Word.sourceAt s.distinct s.leftBasis s.rightBasis s.vector (S.system X)) :=
  rfl

/-- The source list of a preparation is the inventory. -/
@[simp] theorem sources_prepare (S : SourceInventory P) : (S.prepare X).sources = S := by
  induction S with
  | nil => rfl
  | cons s S ih =>
      change _ ++ (prepare S X).sources = _
      rw [ih]
      rfl

omit [DecidableEq P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- A cons inventory is normalized when its head vector and its tail are. -/
@[simp] theorem isNormalized_cons (s : PairSource P) (S : SourceInventory P) :
    IsNormalized (s :: S) ↔ ‖s.vector‖ = 1 ∧ S.IsNormalized := by
  simp only [IsNormalized, List.mem_cons, forall_eq_or_imp]

/-- A preparation is allowed exactly when its source vectors are normalized. -/
theorem isAllowed_prepare_iff (S : SourceInventory P) :
    (S.prepare X).IsAllowed ↔ S.IsNormalized := by
  induction S with
  | nil => exact iff_of_true trivial fun _ h ↦ absurd h List.not_mem_nil
  | cons s S ih =>
      change (prepare S X).IsAllowed ∧ (_ ∧ ‖s.vector‖ = 1) ↔ _
      rw [ih, isNormalized_cons]
      exact ⟨fun h ↦ ⟨h.2.2, h.1⟩, fun h ↦
        ⟨h.2, ((SourceGate.norm_ev_le _ ()).trans h.1.le), h.1⟩⟩

/-- The family `A` of party operations run beside the fresh factors of all sources of `S`. -/
def liftOps {X' : P → Type} : (S : SourceInventory P) → (∀ p, Matrix (X' p) (X p) ℂ) →
    ∀ p, Matrix (S.system X' p) (S.system X p) ℂ
  | [], A => A
  | s :: S, A => addPairMatrix s.distinct s.leftBasis s.rightBasis (liftOps S A)

/-- Running beside fresh factors keeps contractions. -/
theorem norm_liftOps_le {X' : P → Type} [∀ p, Fintype (X' p)]
    (S : SourceInventory P) (A : ∀ p, Matrix (X' p) (X p) ℂ) (p : P) :
    ‖S.liftOps A p‖ ≤ ‖A p‖ := by
  induction S with
  | nil => exact le_rfl
  | cons s S ih => exact (norm_addPairMatrix_le _ _ _ _ p).trans ih

section addPair

variable {p q : P} (hpq : p ≠ q) (α β : Type)

/-- A cast of a pair whose first factor is fixed casts the second component. -/
private theorem cast_cast_prod {A T T' U U' : Type} (h : T' = T) (hU' : U' = (A × T'))
    (hU : U = (A × T)) (h' : U' = U) (y : U') :
    cast hU (cast h' y) = ((cast hU' y).1, cast h (cast hU' y).2) := by
  subst hU' hU h
  rfl

/-- The basis of `addPair` at a party, read through an identification of the old bases. -/
private theorem addPairSiteEquiv_cast {Y Y' : P → Type} {s : P} (h : Y' s = Y s)
    (h' : addPair Y' hpq α β s = addPair Y hpq α β s) (y : addPair Y' hpq α β s) :
    addPairSiteEquiv hpq α β Y s (cast h' y) =
      ((addPairSiteEquiv hpq α β Y' s y).1, cast h (addPairSiteEquiv hpq α β Y' s y).2) := by
  unfold addPairSiteEquiv
  split_ifs with hp hq
  · simp only [Equiv.trans_apply, Equiv.cast_apply, Equiv.prodCongr_apply, Prod.map,
      Equiv.refl_apply]
    rw [cast_cast_prod h (by simp [addPair, hp])]
  · simp only [Equiv.trans_apply, Equiv.cast_apply, Equiv.prodCongr_apply, Prod.map,
      Equiv.refl_apply]
    rw [cast_cast_prod h (by simp [addPair, hq, hpq.symm])]
  · simp only [Equiv.trans_apply, Equiv.cast_apply, Equiv.prodCongr_apply, Prod.map,
      Equiv.refl_apply, Equiv.punitProd_symm_apply, cast_cast]

/-- Running the identification of equal bases beside the fresh factors gives the identification
of the equal bases of `addPair`. -/
private theorem addPairMatrix_eq_cast [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {Y Y' : P → Type} [∀ s, DecidableEq (Y s)]
    (C : ∀ s, Matrix (Y' s) (Y s) ℂ) {s : P} (h : Y' s = Y s)
    (hC : C s = (Equiv.cast h).toPEquiv.toMatrix) :
    ∃ h' : addPair Y' hpq α β s = addPair Y hpq α β s,
      addPairMatrix hpq α β C s = (Equiv.cast h').toPEquiv.toMatrix := by
  have h' : addPair Y' hpq α β s = addPair Y hpq α β s := by simp only [addPair, h]
  refine ⟨h', ?_⟩
  rw [addPairMatrix, hC, ← PEquiv.toMatrix_refl, ← Equiv.toPEquiv_refl,
    ← toMatrix_toPEquiv_prodCongr, reindex_apply, Equiv.symm_symm, Equiv.symm_symm,
    toMatrix_toPEquiv_submatrix]
  refine congrArg (fun e ↦ (Equiv.toPEquiv e).toMatrix) (Equiv.ext fun y ↦ ?_)
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_eq, Equiv.cast_apply,
    addPairSiteEquiv_cast hpq α β h h']
  rfl

/-- Party operations read through identifications of equal families, run beside fresh factors. -/
private theorem addPairMatrix_submatrix_cast [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {U U' V V' : P → Type} (hU : U = V) (hU' : U' = V')
    (C : ∀ s, Matrix (V' s) (V s) ℂ) (s : P) :
    addPairMatrix hpq α β (fun t ↦ (C t).submatrix (Equiv.cast (congrFun hU' t))
        (Equiv.cast (congrFun hU t))) s =
      (addPairMatrix hpq α β C s).submatrix
        (Equiv.cast (congrArg (fun T ↦ addPair T hpq α β s) hU'))
        (Equiv.cast (congrArg (fun T ↦ addPair T hpq α β s) hU)) := by
  subst hU hU'
  rfl

end addPair

/-- Running the identification of equal bases of one party beside the fresh factors of an
inventory gives the identification of the equal prepared bases. -/
theorem liftOps_eq_cast {X X' : P → Type} [∀ s, DecidableEq (X s)] (S : SourceInventory P)
    (A : ∀ s, Matrix (X' s) (X s) ℂ) {p : P} (h : X' p = X p)
    (hA : A p = (Equiv.cast h).toPEquiv.toMatrix) :
    ∃ h' : S.system X' p = S.system X p, S.liftOps A p = (Equiv.cast h').toPEquiv.toMatrix := by
  induction S with
  | nil => exact ⟨h, hA⟩
  | cons s S ih =>
    obtain ⟨h₁, e₁⟩ := ih
    exact addPairMatrix_eq_cast s.distinct s.leftBasis s.rightBasis (liftOps S A) h₁ e₁

/-- Running party operations beside the fresh factors of a concatenation is running them beside
the fresh factors of the second list and then of the first, read through `system_append`. -/
theorem liftOps_append {X X' : P → Type} (S T : SourceInventory P)
    (A : ∀ s, Matrix (X' s) (X s) ℂ) (p : P) :
    liftOps (S ++ T) A p =
      (liftOps S (liftOps T A) p).submatrix (Equiv.cast (congrFun (system_append S T X') p))
        (Equiv.cast (congrFun (system_append S T X) p)) := by
  induction S generalizing p with
  | nil => rfl
  | cons s S ih =>
    change addPairMatrix s.distinct s.leftBasis s.rightBasis (liftOps (S ++ T) A) p = _
    rw [show liftOps (S ++ T) A = fun t ↦ (liftOps S (liftOps T A) t).submatrix
      (Equiv.cast (congrFun (system_append S T X') t))
      (Equiv.cast (congrFun (system_append S T X) t)) from funext ih]
    exact addPairMatrix_submatrix_cast s.distinct s.leftBasis s.rightBasis
      (system_append S T X) (system_append S T X') _ p

variable [Fintype P]

/-- The operator of the preparation of a cons inventory. -/
theorem op_prepare_cons (s : PairSource P) (S : SourceInventory P) :
    (prepare (s :: S) X).op =
      (Word.sourceAt s.distinct s.leftBasis s.rightBasis s.vector (S.system X)).op *
        (prepare S X).op := by
  rw [prepare_cons]
  exact PartyCircuit.op_comp _ _ _

/-- **Preparations commute with local operations on the existing factors**. Source: Theorem 5.2,
`eq:compression-source-gate`, `04-compression.tex`, lines 246–248. -/
theorem op_prepare_mul_piKronecker {X' : P → Type} [∀ p, Fintype (X' p)]
    [∀ p, DecidableEq (X' p)] (S : SourceInventory P) (A : ∀ p, Matrix (X' p) (X p) ℂ) :
    (S.prepare X').op * piKronecker A = piKronecker (S.liftOps A) * (S.prepare X).op := by
  induction S with
  | nil => exact (Matrix.one_mul _).trans (Matrix.mul_one _).symm
  | cons s S ih =>
      rw [op_prepare_cons, op_prepare_cons]
      exact (Matrix.mul_assoc _ _ _).trans ((congrArg _ ih).trans
        ((Matrix.mul_assoc _ _ _).symm.trans ((congrArg (· * (prepare S X).op)
          (Word.op_sourceAt_mul_piKronecker s.distinct s.leftBasis s.rightBasis s.vector
            (liftOps S A))).trans (Matrix.mul_assoc _ _ _))))

/-! ### Expansion of inventories -/

/-- A preparation can be expanded into another by allowed operations containing no pair
sources, uniformly over all spectator systems. Source: Lemma 5.1, `04-compression.tex`,
lines 125–127. -/
def Expands (G S : SourceInventory P) : Prop :=
  ∀ (X : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)],
    ∃ w : Word (G.system X) (S.system X),
      w.IsAllowed ∧ w.sources = [] ∧ w.op * (G.prepare X).op = (S.prepare X).op

/-- Expansion with the source-free word replaced by a family of contractions at the parties. -/
theorem expands_iff_exists_piKronecker (G S : SourceInventory P) :
    G.Expands S ↔ ∀ (X : P → Type) [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)],
      ∃ A : ∀ p, Matrix (S.system X p) (G.system X p) ℂ,
        (∀ p, ‖A p‖ ≤ 1) ∧ piKronecker A * (G.prepare X).op = (S.prepare X).op := by
  constructor
  · intro h X _ _
    obtain ⟨w, hw, hs, he⟩ := h X
    obtain ⟨A, hA, hAw⟩ := Word.exists_piKronecker_of_sources_eq_nil hw hs
    exact ⟨A, hA, by rw [← hAw]; exact he⟩
  · intro h X _ _
    obtain ⟨A, hA, he⟩ := h X
    refine ⟨PartyCircuit.localOps A, hA, rfl, ?_⟩
    rw [Word.op, PartyCircuit.op_localOps]
    exact he

namespace Expands

/-- Every inventory expands to itself. -/
@[refl] theorem refl (S : SourceInventory P) : S.Expands S := by
  intro X _ _
  exact ⟨PartyCircuit.done _, trivial, rfl, Matrix.one_mul _⟩

/-- Expansion is transitive. -/
@[trans] theorem trans {G S T : SourceInventory P} (hGS : G.Expands S) (hST : S.Expands T) :
    G.Expands T := by
  intro X _ _
  obtain ⟨w, hw, hs, he⟩ := hGS X
  obtain ⟨w', hw', hs', he'⟩ := hST X
  refine ⟨w.comp w', ⟨hw, hw'⟩, ?_, ?_⟩
  · rw [Word.sources_comp, hs, hs', List.nil_append]
  · rw [Word.op_comp, Matrix.mul_assoc]
    exact (congrArg _ he).trans he'

/-- A common source can be retained while the remaining inventory is expanded. -/
theorem cons (s : PairSource P) {G S : SourceInventory P} (h : G.Expands S) :
    Expands (s :: G) (s :: S) := by
  rw [expands_iff_exists_piKronecker] at h ⊢
  intro X _ _
  obtain ⟨A, hA, he⟩ := h X
  refine ⟨addPairMatrix s.distinct s.leftBasis s.rightBasis A,
    fun p ↦ (norm_addPairMatrix_le _ _ _ A p).trans (hA p), ?_⟩
  rw [op_prepare_cons, op_prepare_cons]
  exact (Matrix.mul_assoc _ _ _).symm.trans
    ((congrArg (· * (G.prepare X).op)
      (Word.op_sourceAt_mul_piKronecker s.distinct s.leftBasis s.rightBasis s.vector A).symm).trans
      ((Matrix.mul_assoc _ _ _).trans (congrArg _ he)))

/-- Reversing the endpoint order changes only the order of the two fresh factors. -/
theorem reverse (s : PairSource P) (T : SourceInventory P) :
    Expands (s.reverse :: T) (s :: T) := by
  intro X _ _
  refine ⟨PartyCircuit.relabel (addPairCommEquiv s.distinct s.leftBasis s.rightBasis),
    Word.isAllowed_relabel _, Word.sources_relabel _, ?_⟩
  rw [op_prepare_cons, op_prepare_cons]
  exact (Matrix.mul_assoc _ _ _).symm.trans (congrArg (· * (T.prepare X).op)
    (Word.op_relabel_sourceAt_reverse s.distinct s.leftBasis s.rightBasis s.vector))

/-- Splitting a combined source recovers the original two source occurrences. -/
theorem combine (s t : PairSource P) (hLeft : s.left = t.left) (hRight : s.right = t.right)
    (T : SourceInventory P) : Expands (s.combine t hLeft hRight :: T) (s :: t :: T) := by
  cases s with
  | mk p q hpq α β η =>
  cases t with
  | mk p' q' hpq' α' β' η' =>
  dsimp only at hLeft hRight
  subst hLeft hRight
  intro X _ _
  refine ⟨Word.expandCombinedPair hpq α β α' β' (T.system X),
    Word.isAllowed_expandCombinedPair _ _ _ _ _, Word.sources_expandCombinedPair _ _ _ _ _, ?_⟩
  rw [op_prepare_cons, op_prepare_cons, op_prepare_cons]
  have h := (Word.op_expandCombinedPair hpq α β α' β' (X := T.system X) η η').trans
    (PartyCircuit.op_comp _ _ _)
  exact (Matrix.mul_assoc _ _ _).symm.trans ((congrArg (· * (T.prepare X).op) h).trans
    (Matrix.mul_assoc _ _ _))

/-- Exchanging two sources changes only their order of preparation. -/
theorem swap (s t : PairSource P) (T : SourceInventory P) :
    Expands (t :: s :: T) (s :: t :: T) := by
  intro X _ _
  refine ⟨PartyCircuit.relabel (addPairSwapEquiv t.distinct s.distinct t.leftBasis t.rightBasis
    s.leftBasis s.rightBasis), Word.isAllowed_relabel _, Word.sources_relabel _, ?_⟩
  rw [op_prepare_cons, op_prepare_cons, op_prepare_cons, op_prepare_cons]
  have h := Word.op_relabel_sourceAt_swap (X := T.system X) s.distinct s.leftBasis s.rightBasis
    t.leftBasis t.rightBasis t.distinct s.vector t.vector
  exact ((Matrix.mul_assoc _ _ _).symm.trans ((Matrix.mul_assoc _ _ _).symm.trans
    ((congrArg (· * (T.prepare X).op) h).trans (Matrix.mul_assoc _ _ _))))

/-- A permutation of whole sources preserves their preparation up to allowed exchanges, for
every spectator system. -/
theorem of_perm {S T : SourceInventory P} (h : S.Perm T) : S.Expands T := by
  induction h with
  | nil => exact Expands.refl []
  | cons s _ ih => exact Expands.cons s ih
  | swap s t T => exact Expands.swap s t T
  | trans _ _ ih ih' => exact ih.trans ih'

end Expands

end SourceInventory

end QuantumCircuit.Party

/-! ### Party operations beside fresh factors, at a party outside every source -/

namespace QuantumCircuit.Party

namespace SourceInventory

variable {P : Type} [DecidableEq P]

/-- **At a party that is no endpoint of the sources of an inventory**, party operations run
beside their fresh factors are the operations, read through identifications of equal bases. -/
theorem liftOps_apply_of_forall_ne {X X' : P → Type} (A : ∀ s, Matrix (X' s) (X s) ℂ) {p : P} :
    (S : SourceInventory P) → (∀ s ∈ S, s.left ≠ p ∧ s.right ≠ p) →
      ∃ (h₁ : S.system X' p = X' p) (h₂ : S.system X p = X p),
        S.liftOps A p = (A p).submatrix (Equiv.cast h₁) (Equiv.cast h₂)
  | [], _ => ⟨rfl, rfl, rfl⟩
  | s :: S, hS => by
    obtain ⟨h₁, h₂, e⟩ := liftOps_apply_of_forall_ne A S fun t ht ↦ hS t (List.mem_cons_of_mem _ ht)
    have hl := (hS s List.mem_cons_self).1.symm
    have hr := (hS s List.mem_cons_self).2.symm
    refine ⟨(addPair_of_ne s.distinct s.leftBasis s.rightBasis hl hr).trans h₁,
      (addPair_of_ne s.distinct s.leftBasis s.rightBasis hl hr).trans h₂, ?_⟩
    have hA : addPairMatrix s.distinct s.leftBasis s.rightBasis (liftOps S A) p =
        (liftOps S A p).submatrix (Equiv.cast (addPair_of_ne s.distinct _ _ hl hr))
          (Equiv.cast (addPair_of_ne s.distinct _ _ hl hr)) := by
      ext y x
      simp [addPairMatrix, addPairSiteEquiv, hl, hr, kroneckerMap_apply]
    change addPairMatrix s.distinct s.leftBasis s.rightBasis (liftOps S A) p = _
    rw [hA, e]
    ext y x
    exact congrArg₂ (A p) (cast_cast _ _ y) (cast_cast _ _ x)

end SourceInventory

end QuantumCircuit.Party
