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
* `QuantumCircuit.Party.SourceInventory.liftOps` — party operations beside the fresh factors.
* `QuantumCircuit.Party.SourceInventory.Expands` — expansion of one inventory into another.

## Main results

* `QuantumCircuit.Party.SourceInventory.op_prepare_mul_piKronecker` — a preparation commutes
  with party operations on the existing factors.
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
