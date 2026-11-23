/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.PartyMaps
import QICLean.Circuit.Party.Syntax.OnCell

/-!
# Source-prepared gates

A *prepared source gate* records the common source data of a weighted family of words: the
slots (one source on every unordered pair of distinct parties), their bases, the normalized
vectors of every branch, and the remaining source-free words; its operator is the weighted sum
of the branches (`PreparedSourceGate.eval`). Every weighted family of allowed words whose sum is
a contraction has one (`Word.exists_preparedSourceGate`). A *prepared gate*
(`PreparedGate D X Y`) is such a gate on the parties of a cell `D`.

The two conditions of a prepared source gate, that its remaining words are allowed and that its
operator is a contraction, read the finiteness instances of the systems; they are stated for
every choice of these instances, all choices being equal, so that every prepared gate carries
its bound.

Prepared gates run beside spectator factors (`GateFrame PreparedGate`): the slots and vectors
stay, the remaining words are framed, and a framed gate acts as `1 ⊗ eval`
(`PreparedSourceGate.eval_frame`); the slot preparation commutes with framing
(`PreparedSourceGate.prepareSlots_frame`).

## Main definitions

* `QuantumCircuit.Party.PreparedSourceGate`, `QuantumCircuit.Party.PreparedSourceGate.branchWord`,
  `QuantumCircuit.Party.PreparedSourceGate.eval` — prepared source gates and their operator.
* `QuantumCircuit.Party.PreparedGate`, `QuantumCircuit.Party.PreparedGate.ev`,
  `QuantumCircuit.Party.PreparedGate.IsTouched` — prepared gates on cells.
* `QuantumCircuit.Party.PreparedSourceGate.frame` — a prepared source gate beside spectator
  factors.

## Main results

* `QuantumCircuit.Party.Word.exists_preparedSourceGate`,
  `QuantumCircuit.Party.Word.exists_finite_source_gate` — every weighted family of allowed
  words is a prepared source gate.
* `QuantumCircuit.Party.PreparedSourceGate.norm_eval_le_one` — prepared gates are contractions.
* `QuantumCircuit.Party.PreparedSourceGate.prepareSlots_frame`,
  `QuantumCircuit.Party.PreparedSourceGate.eval_frame`,
  `QuantumCircuit.Party.PreparedGate.isCompatible_frame` — framing.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 21–36, 133–151 and 233–267 (equation `eq:compression-source-gate`).
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Prepared source gates -/

/-- The common source data of a weighted family of words, with the scalar coefficients `c` fixed as
a parameter. The last two conditions, that the remaining words are allowed and that the weighted sum
is a contraction, read the finiteness of the bases of the systems; they are stated for every choice
of these finiteness data, all choices being equal. Source: Theorem 5.2,
`eq:compression-source-gate`, `04-compression.tex`, lines 233–267. -/
structure PreparedSourceGate [Fintype P] {ι : Type} [Fintype ι] (c : ι → ℂ) (X Y : P → Type) :
    Type 1 where
  /-- The ordered pair positions of the gate. -/
  slots : SourceInventory P
  /-- Each unordered distinct party pair occurs once. -/
  pair_nodup : (slots.map PairSource.partyPair).Nodup
  /-- The positions include every unordered pair of distinct parties. -/
  pair_complete : ∀ k, k ∈ slots.map PairSource.partyPair ↔ ¬ k.IsDiag
  /-- The bases of the two halves of every slot. -/
  bases : SourceInventory.SlotBases slots.length
  /-- The prepared source vector at each slot and branch label. -/
  vector : ι → ∀ i, EuclideanSpace ℂ (bases.left i × bases.right i)
  /-- Each branch source is normalized. -/
  vector_norm : ∀ ξ i, ‖vector ξ i‖ = 1
  /-- The remaining operations, on the slot system. -/
  remaining : ι → Word (SourceInventory.slotSystem slots bases X) Y
  /-- All sources are in the recorded preparation. -/
  remaining_sources : ∀ ξ, (remaining ξ).sources = []
  /-- The remaining operations are allowed. -/
  remaining_allowed : ∀ [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (ξ : ι),
    (remaining ξ).IsAllowed
  /-- The weighted gate is a contraction. -/
  contraction : ∀ [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)],
    ‖∑ ξ, c ξ • Word.op ((SourceInventory.prepareSlots slots bases (vector ξ) X).comp
      (remaining ξ))‖ ≤ 1

/-- A slot preparation with normalized vectors is allowed. -/
theorem SourceInventory.isAllowed_prepareSlots {X : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] (R : SourceInventory P) (B : SourceInventory.SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (hη : ∀ i, ‖η i‖ = 1) :
    (SourceInventory.prepareSlots R B η X).IsAllowed := by
  induction R with
  | nil => trivial
  | cons r R ih =>
      exact ⟨ih B.tail (fun i ↦ η i.succ) (fun i ↦ hη i.succ),
        Word.isAllowed_sourceAt r.distinct (B.left 0) (B.right 0) (hη 0) _⟩

namespace PreparedSourceGate

variable [Fintype P] {ι : Type} [Fintype ι] {c : ι → ℂ} {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The branch of a label, with its source preparation. Source:
`eq:compression-source-gate`, `04-compression.tex`, lines 233–251. -/
def branchWord (G : PreparedSourceGate c X Y) (ξ : ι) : Word X Y :=
  (SourceInventory.prepareSlots G.slots G.bases (G.vector ξ) X).comp (G.remaining ξ)

/-- The operator of the gate: the weighted sum of its branches. Source:
`eq:compression-source-gate`, `04-compression.tex`, lines 233–251. -/
noncomputable def eval (G : PreparedSourceGate c X Y) : Matrix (Config Y) (Config X) ℂ :=
  ∑ ξ, c ξ • (G.branchWord ξ).op

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The sources of a branch are the slots with the branch vectors.
Source: `04-compression.tex`, lines 253–267 and 342–355. -/
theorem sources_branchWord (G : PreparedSourceGate c X Y) (ξ : ι) :
    (G.branchWord ξ).sources = SourceInventory.ofSlots G.slots G.bases (G.vector ξ) := by
  rw [branchWord, Word.sources_comp, G.remaining_sources, SourceInventory.sources_prepareSlots,
    List.nil_append]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- Prepared branches are allowed. Source: `04-compression.tex`, lines 233–267. -/
theorem isAllowed_branchWord (G : PreparedSourceGate c X Y) (ξ : ι) :
    (G.branchWord ξ).IsAllowed :=
  ⟨SourceInventory.isAllowed_prepareSlots _ _ _ (G.vector_norm ξ), G.remaining_allowed ξ⟩

omit [∀ p, DecidableEq (Y p)] in
/-- A prepared gate is a contraction.
Source: `eq:compression-source-gate`, `04-compression.tex`, lines 233–251. -/
theorem norm_eval_le_one (G : PreparedSourceGate c X Y) : ‖G.eval‖ ≤ 1 :=
  G.contraction

end PreparedSourceGate

/-- Construct common source slots from allowed words, keeping the scalar coefficients and the
exact weighted operator. Source: Theorem 5.2, `eq:compression-source-gate`,
`04-compression.tex`, lines 233–267. -/
theorem Word.exists_preparedSourceGate [Fintype P] {ι : Type} [Fintype ι] {X Y : P → Type}
    [iFX : ∀ p, Fintype (X p)] [iDX : ∀ p, DecidableEq (X p)] [iFY : ∀ p, Fintype (Y p)]
    (c : ι → ℂ) (w : ι → Word X Y) (hw : ∀ ξ, (w ξ).IsAllowed)
    (hG : ‖∑ ξ, c ξ • (w ξ).op‖ ≤ 1) :
    ∃ G : PreparedSourceGate c X Y, G.eval = ∑ ξ, c ξ • (w ξ).op := by
  obtain ⟨R, hR, hRK, B, η, hη, v, hv, hvs, he⟩ := Word.exists_common_source_preparation w hw
  have hsum : ∑ ξ, c ξ • Word.op ((SourceInventory.prepareSlots R B (η ξ) X).comp (v ξ)) =
      ∑ ξ, c ξ • (w ξ).op := by
    refine Finset.sum_congr rfl fun ξ _ ↦ ?_
    rw [he ξ]
    exact congrArg _ (Word.op_comp _ _)
  refine ⟨
    { slots := R, pair_nodup := hR, pair_complete := hRK, bases := B, vector := η,
      vector_norm := hη, remaining := v, remaining_sources := hvs,
      remaining_allowed := @fun iF iD ξ ↦ ?_, contraction := @fun iF iD iF' ↦ ?_ }, hsum⟩
  · obtain rfl : iF = iFX := Subsingleton.elim _ _
    obtain rfl : iD = iDX := Subsingleton.elim _ _
    exact hv ξ
  · obtain rfl : iF = iFX := Subsingleton.elim _ _
    obtain rfl : iD = iDX := Subsingleton.elim _ _
    obtain rfl : iF' = iFY := Subsingleton.elim _ _
    exact hsum ▸ hG

/-- A weighted family of allowed words is, in common slot bases, a weighted sum of preparations
followed by one contraction at each party. Source: Theorem 5.2, `eq:compression-source-gate`,
`04-compression.tex`, lines 233–267. -/
theorem Word.exists_finite_source_gate [Fintype P] {ι : Type} [Fintype ι] {X Y : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
    (c : ι → ℂ) (w : ι → Word X Y) (hw : ∀ ξ, (w ξ).IsAllowed) :
    ∃ R : SourceInventory P, (R.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ R.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      ∃ (B : SourceInventory.SlotBases R.length)
        (η : ι → ∀ i, EuclideanSpace ℂ (B.left i × B.right i)),
        (∀ ξ i, ‖η ξ i‖ = 1) ∧
        ∃ A : ι → ∀ p, Matrix (Y p) (SourceInventory.slotSystem R B X p) ℂ,
          (∀ ξ p, ‖A ξ p‖ ≤ 1) ∧
          ∑ ξ, c ξ • (w ξ).op =
            ∑ ξ, c ξ • (piKronecker (A ξ) * (SourceInventory.prepareSlots R B (η ξ) X).op) := by
  obtain ⟨R, hR, hRK, B, η, hη, A, hA, he⟩ := Word.exists_common_prepared_localOps w hw
  exact ⟨R, hR, hRK, B, η, hη, A, hA, Finset.sum_congr rfl fun ξ _ ↦ by rw [he ξ]⟩

/-! ### Prepared gates on cells -/

/-- A source-prepared gate on the cell `D`: a prepared source gate on the parties of `D`, with its
labels and coefficients, carrying its own contraction bound. Source: Theorem 5.2,
`04-compression.tex`, lines 133–151 and 233–267. -/
structure PreparedGate (D : Finset P) (X Y : P → Type) : Type 1 where
  /-- The branch labels. -/
  ι : Type
  [fintypeι : Fintype ι]
  /-- The coefficients. -/
  coeff : ι → ℂ
  /-- The prepared source gate on the parties of the cell. -/
  gate : PreparedSourceGate coeff (fun s : ↥D ↦ X s) (fun s : ↥D ↦ Y s)

attribute [instance] PreparedGate.fintypeι

/-- A prepared gate has one outcome. -/
instance : GateFamily (S := P) PreparedGate where
  Outcome _ := Unit
  fintype _ := inferInstance

/-- Prepared gates have one outcome each. -/
instance : GateFamily.UniqueOutcome (S := P) PreparedGate where
  nonempty_unique := fun _ _ _ _ ↦ ⟨inferInstanceAs (Unique Unit)⟩

/-- The interpretation of prepared gates: the operator of the prepared source gate on the cell.
Source: `04-compression.tex`, lines 21–36 and 233–267. -/
noncomputable def PreparedGate.ev : Interpretation (S := P) PreparedGate :=
  fun g _ ↦ g.gate.eval

/-- Every prepared gate is a contraction. -/
theorem PreparedGate.norm_ev_le_one {D : Finset P} {X Y : P → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (g : PreparedGate D X Y) (o : Unit) : ‖PreparedGate.ev g o‖ ≤ 1 :=
  g.gate.norm_eval_le_one

/-- A cell meets the affected parties `A`. Source:
Theorem 5.2, `04-compression.tex`, lines 356–364. -/
def PreparedGate.IsTouched (A : P → Bool) (D : Finset P) : Prop := ∃ p ∈ D, A p = true

/-- Whether a cell meets the affected parties is decidable. -/
instance (A : P → Bool) (D : Finset P) : Decidable (PreparedGate.IsTouched A D) := by
  unfold PreparedGate.IsTouched; infer_instance

/-! ### Prepared gates beside spectator factors -/

/-- A fresh pair of factors in front of a system framed by spectator factors: the basis of `s`
in `addPair Z'`, with `Z' s ≃ W s × Z s`, is the spectator factor in front of the basis of `s` in
`addPair Z`. -/
def addPairFrameEquiv {W Z Z' : P → Type} {p q : P} (hpq : p ≠ q) (α β : Type)
    (F : ∀ s, Z' s ≃ W s × Z s) (s : P) :
    addPair Z' hpq α β s ≃ W s × addPair Z hpq α β s :=
  (addPairSiteEquiv hpq α β Z' s).trans <|
    ((Equiv.refl _).prodCongr (F s)).trans <|
      (Equiv.prodLeftComm _ _ _).trans
        ((Equiv.refl _).prodCongr (addPairSiteEquiv hpq α β Z s).symm)

/-- The configurations of `addPair` read along `addPairFrameEquiv`. -/
theorem addPairConfigEquiv_addPairFrameEquiv {W Z Z' : P → Type} {p q : P} (hpq : p ≠ q)
    (α β : Type) (F : ∀ s, Z' s ≃ W s × Z s) (y : Config fun s ↦ W s × addPair Z hpq α β s) :
    addPairConfigEquiv hpq α β
        (Equiv.piCongrRight (fun s ↦ (addPairFrameEquiv hpq α β F s).symm) y) =
      ((addPairConfigEquiv hpq α β fun s ↦ (y s).2).1,
        Equiv.piCongrRight (fun s ↦ (F s).symm)
          fun s ↦ ((y s).1, (addPairConfigEquiv hpq α β fun s ↦ (y s).2).2 s)) := by
  rw [addPairConfigEquiv_eq_siteEquiv, addPairConfigEquiv_eq_siteEquiv]
  refine Prod.ext ?_ (funext fun s ↦ ?_)
  · simp [addPairFrameEquiv, Equiv.prodLeftComm]
  · simp [addPairFrameEquiv, Equiv.prodLeftComm]

/-- **A pair source commutes with framing**, one source at a time: the source on the framed system,
read along `addPairFrameEquiv`, is `1 ⊗` the source, after reading the input along `F`. -/
theorem op_relabel_sourceAt_frame [Fintype P] {W Z Z' : P → Type} [∀ s, Fintype (W s)]
    [∀ s, DecidableEq (W s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    [∀ s, Fintype (Z' s)] [∀ s, DecidableEq (Z' s)] {p q : P} (hpq : p ≠ q) (α β : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (η : EuclideanSpace ℂ (α × β))
    (F : ∀ s, Z' s ≃ W s × Z s) :
    Word.op (PartyCircuit.relabel (G := SourceGate) fun s ↦ (addPairFrameEquiv hpq α β F s).symm) *
        (Word.sourceAt hpq α β η Z').op =
      reindex (Equiv.arrowProdEquivProdArrow P W (addPair Z hpq α β)).symm
          (Equiv.arrowProdEquivProdArrow P W Z).symm
          ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ (Word.sourceAt hpq α β η Z).op) *
        Word.op (PartyCircuit.relabel (G := SourceGate) fun s ↦ (F s).symm) := by
  rw [Word.op_sourceAt, Word.op_sourceAt]
  unfold Word.op
  rw [PartyCircuit.op_relabel_mul, PartyCircuit.op_relabel, PEquiv.mul_toMatrix_toPEquiv]
  ext y x
  simp only [submatrix_apply, id, prepMatrix_apply, reindex_apply, Equiv.symm_symm,
    kroneckerMap_apply, one_apply, Equiv.arrowProdEquivProdArrow_apply,
    addPairConfigEquiv_addPairFrameEquiv]
  simp only [← Equiv.eq_symm_apply]
  generalize (Equiv.piCongrRight fun s ↦ (F s).symm).symm x = z
  generalize addPairConfigEquiv hpq α β (fun s ↦ (y s).2) = a
  have key : ((fun s ↦ ((y s).1, a.2 s)) = z) ↔
      (fun c ↦ (y c).1) = (fun c ↦ (z c).1) ∧ a.2 = fun c ↦ (z c).2 := by
    simp only [funext_iff, Prod.ext_iff, forall_and]
  simp only [key, ite_and]
  split_ifs <;> simp

/-- The induction step of `PreparedSourceGate.prepareSlots_frame`: one more source. -/
theorem op_relabel_comp_sourceAt_frame [Fintype P] {W X Z Z' : P → Type} [∀ s, Fintype (W s)]
    [∀ s, DecidableEq (W s)] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    [∀ s, Fintype (Z' s)] [∀ s, DecidableEq (Z' s)] {p q : P} (hpq : p ≠ q) (α β : Type)
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (η : EuclideanSpace ℂ (α × β))
    (F : ∀ s, Z' s ≃ W s × Z s) (v' : Word (fun s ↦ W s × X s) Z') (v : Word X Z)
    (hv : Word.op (PartyCircuit.relabel (G := SourceGate) fun s ↦ (F s).symm) * v'.op =
      reindex (Equiv.arrowProdEquivProdArrow P W Z).symm (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ v.op)) :
    Word.op (PartyCircuit.relabel (G := SourceGate) fun s ↦ (addPairFrameEquiv hpq α β F s).symm) *
        Word.op (v'.comp (Word.sourceAt hpq α β η Z')) =
      reindex (Equiv.arrowProdEquivProdArrow P W (addPair Z hpq α β)).symm
        (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ Word.op (v.comp (Word.sourceAt hpq α β η Z))) := by
  rw [Word.op_comp, Word.op_comp, ← Matrix.mul_assoc, op_relabel_sourceAt_frame, Matrix.mul_assoc,
    hv, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv, ← mul_kronecker_mul,
    Matrix.one_mul]

/-- The base case of `PreparedSourceGate.prepareSlots_frame`: no source. -/
theorem op_relabel_refl_frame [Fintype P] {W X : P → Type} [∀ s, Fintype (W s)]
    [∀ s, DecidableEq (W s)] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] :
    Word.op (PartyCircuit.relabel (G := SourceGate) fun s ↦ (Equiv.refl (W s × X s)).symm) *
        Word.op (PartyCircuit.done fun s ↦ W s × X s) =
      reindex (Equiv.arrowProdEquivProdArrow P W X).symm (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ Word.op (PartyCircuit.done X)) := by
  unfold Word.op
  rw [PartyCircuit.op_done, PartyCircuit.op_done, Matrix.mul_one, PartyCircuit.op_relabel,
    one_kronecker_one, reindex_apply, submatrix_one_equiv]
  simp

/-- The slot system of spectator-framed bases is the spectator factor in front of the slot
system. -/
def SourceInventory.slotSystemFrameEquiv (W X : P → Type) : (R : SourceInventory P) →
    (B : SourceInventory.SlotBases R.length) → ∀ p,
      SourceInventory.slotSystem R B (fun p ↦ W p × X p) p ≃
        W p × SourceInventory.slotSystem R B X p
  | [], _, _ => Equiv.refl _
  | r :: R, B, p => addPairFrameEquiv r.distinct (B.left 0) (B.right 0)
    (slotSystemFrameEquiv W X R B.tail) p

namespace PreparedSourceGate

variable [Fintype P] {ι : Type} [Fintype ι] {c : ι → ℂ} {X Y : P → Type}
  (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- The remaining word of a branch beside spectator factors: the framed word, after the
identification of the framed slot system. -/
def frameRemaining [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] (G : PreparedSourceGate c X Y)
    (ξ : ι) : Word (SourceInventory.slotSystem G.slots G.bases (fun p ↦ W p × X p))
      (fun p ↦ W p × Y p) :=
  (PartyCircuit.relabel fun p ↦
      (SourceInventory.slotSystemFrameEquiv W X G.slots G.bases p).symm).comp
    ((G.remaining ξ).frame W)

/-- **A slot preparation commutes with framing**: preparing the slots beside spectator factors,
read in front of the slot system, is `1 ⊗` the preparation. -/
theorem prepareSlots_frame [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (R : SourceInventory P) (B : SourceInventory.SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) :
    Word.op (PartyCircuit.relabel (G := SourceGate) fun p ↦
        (SourceInventory.slotSystemFrameEquiv W X R B p).symm) *
        (SourceInventory.prepareSlots R B η (fun p ↦ W p × X p)).op =
      reindex (Equiv.arrowProdEquivProdArrow P W (SourceInventory.slotSystem R B X)).symm
        (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ (SourceInventory.prepareSlots R B η X).op) := by
  induction R with
  | nil => exact op_relabel_refl_frame
  | cons r R ih =>
    exact op_relabel_comp_sourceAt_frame r.distinct (B.left 0) (B.right 0) (η 0) _ _ _
      (ih B.tail fun i ↦ η i.succ)

/-- A framed branch is `1 ⊗` the branch: the slot preparation beside spectator factors followed by
the framed remaining word. -/
theorem op_prepareSlots_comp_frameRemaining [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (G : PreparedSourceGate c X Y) (ξ : ι) :
    Word.op ((SourceInventory.prepareSlots G.slots G.bases (G.vector ξ)
        (fun p ↦ W p × X p)).comp (G.frameRemaining W ξ)) =
      reindex (Equiv.arrowProdEquivProdArrow P W Y).symm
        (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ (G.branchWord ξ).op) := by
  rw [Word.op_comp, frameRemaining, Word.op_comp, Word.op_frame, Matrix.mul_assoc,
    prepareSlots_frame, branchWord, Word.op_comp, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]

/-- **A framed prepared gate acts as `1 ⊗ eval`.** The weighted sum of the framed branches is
the identity on the spectator factors times the weighted sum of the branches. -/
theorem sum_frameRemaining [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (G : PreparedSourceGate c X Y) :
    ∑ ξ, c ξ • Word.op ((SourceInventory.prepareSlots G.slots G.bases (G.vector ξ)
        (fun p ↦ W p × X p)).comp (G.frameRemaining W ξ)) =
      reindex (Equiv.arrowProdEquivProdArrow P W Y).symm
        (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ G.eval) := by
  simp only [op_prepareSlots_comp_frameRemaining, eval, reindex_apply]
  ext y x
  simp only [Matrix.sum_apply, Matrix.smul_apply, submatrix_apply, kroneckerMap_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

/-- A prepared source gate beside spectator factors: the same slots and vectors, every remaining
word framed (the factor of the spectator stays in front of the fresh factors). -/
def frame [iFX : ∀ p, Fintype (X p)] [iDX : ∀ p, DecidableEq (X p)] [iFY : ∀ p, Fintype (Y p)]
    (G : PreparedSourceGate c X Y) :
    PreparedSourceGate c (fun p ↦ W p × X p) (fun p ↦ W p × Y p) where
  slots := G.slots
  pair_nodup := G.pair_nodup
  pair_complete := G.pair_complete
  bases := G.bases
  vector := G.vector
  vector_norm := G.vector_norm
  remaining := G.frameRemaining W
  remaining_sources ξ := by
    rw [frameRemaining, Word.sources_comp, Word.sources_frame, G.remaining_sources]
    rfl
  remaining_allowed := @fun iF iD ξ ↦ by
    obtain rfl : iF = fun p ↦ instFintypeProd (W p) (X p) := Subsingleton.elim _ _
    obtain rfl : iD = fun p ↦ instDecidableEqProd := Subsingleton.elim _ _
    exact ⟨Word.isAllowed_relabel _, Word.isAllowed_frame W (G.remaining_allowed ξ)⟩
  contraction := @fun iF iD iF' ↦ by
    obtain rfl : iF = fun p ↦ instFintypeProd (W p) (X p) := Subsingleton.elim _ _
    obtain rfl : iD = fun p ↦ instDecidableEqProd := Subsingleton.elim _ _
    obtain rfl : iF' = fun p ↦ instFintypeProd (W p) (Y p) := Subsingleton.elim _ _
    rw [sum_frameRemaining]
    exact (l2_opNorm_reindex_le _ _ _).trans
      ((l2_opNorm_one_kronecker_le _).trans G.norm_eval_le_one)

/-- The operator of a framed prepared source gate is `1 ⊗ eval`. -/
theorem eval_frame [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
    (G : PreparedSourceGate c X Y) :
    (G.frame W).eval =
      reindex (Equiv.arrowProdEquivProdArrow P W Y).symm
        (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ G.eval) :=
  G.sum_frameRemaining W

/-- The operator of a branch of a framed prepared source gate is `1 ⊗` the operator of the
branch. -/
theorem op_branchWord_frame [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
    (G : PreparedSourceGate c X Y) (ξ : ι) :
    ((G.frame W).branchWord ξ).op =
      reindex (Equiv.arrowProdEquivProdArrow P W Y).symm
        (Equiv.arrowProdEquivProdArrow P W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ (G.branchWord ξ).op) :=
  G.op_prepareSlots_comp_frameRemaining W ξ

end PreparedSourceGate

/-- Prepared gates run beside spectator factors, the factors of their cell: the slots, vectors,
labels and coefficients stay, and the remaining words are framed. -/
instance : GateFrame (P := P) PreparedGate where
  frame D _ _ W _ _ _ _ _ _ g :=
    { ι := g.ι, coeff := g.coeff, gate := g.gate.frame fun s : ↥D ↦ W s }
  outcomeEquiv _ _ _ _ _ _ _ _ _ _ _ := Equiv.refl Unit

/-- A framed prepared gate has the labels and coefficients of the gate. -/
@[simp] theorem PreparedGate.ι_frame {D : Finset P} {X Y : P → Type} (W : P → Type)
    [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (g : PreparedGate D X Y) :
    (GateFrame.frame W g).ι = g.ι :=
  rfl

/-- The coefficients of a framed prepared gate. -/
@[simp] theorem PreparedGate.coeff_frame {D : Finset P} {X Y : P → Type} (W : P → Type)
    [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (g : PreparedGate D X Y) :
    (GateFrame.frame W g).coeff = g.coeff :=
  rfl

/-- The interpretation of prepared gates is compatible with framing. -/
theorem PreparedGate.isCompatible_frame :
    GateFrame.IsCompatible (P := P) PreparedGate PreparedGate.ev :=
  fun D _ _ W _ _ _ _ _ _ g _ ↦ g.gate.eval_frame fun s : ↥D ↦ W s

end QuantumCircuit.Party
