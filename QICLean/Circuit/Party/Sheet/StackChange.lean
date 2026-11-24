/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Norm.MatrixToEuclidean
import QICLean.Circuit.Party.Original.FromWord
import QICLean.Circuit.Party.Syntax.UsesOnly
import QICLean.Circuit.Party.Sheet.Stack

/-!
# Bounded changes of the sheet stack

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript every change of the memory
is a bounded number of gates: each change of the schedule has at most one nonprivate gate, whose
participants are parties its event uses, whose monomial expansion has polynomially many
monomials with polynomially bounded coefficients and a bounded number of pair effects, and which
takes the reference vector of the sheets within `C L⁻²⁰` of the next reference vector
(`06-geometry.tex`, lines 25–41 and 572–583). Item 3 of Theorem 5.2 asks in addition for a
constant bounding the number of pair sources in each monomial of every gate
(`04-compression.tex`, lines 143–147).

This file packages these properties into predicates and proves that the operations of the
schedule preserve them, for sheets of an arbitrary type, each sheet `F` with a system `sys F` and
a reference vector `ref F` of norm at most one.

* `OriginalCircuit.IsBoundedChange`: an original circuit with at most one nonprivate gate,
  participants in a set `S`, expansion and monomial bounds, and an error at most `ε` from a
  vector `x` to a vector `y`.
* `HasBoundedChange`, `HasSourceBoundedChange`: a bounded change between two lists of sheets,
  followed by the same idle system, from the reference vector of the first list to that of the
  second; the second also bounds the pair sources of every monomial.

Their closure properties are: weaker bounds; reorderings of the sheets, before or after a
change, and identity changes; a change of one sheet or of two adjacent sheets, lifted to the
whole stack; and the activation of an auxiliary sheet. The words of the births
(`Word.isBoundedChange_toOriginalCircuit`), the words without gates of the exchanges
(`Word.isBoundedChange_toOriginalCircuit_of_sourceCount_eq_zero`) and the chains of the deaths
(`Monomial.isBoundedChange_toOriginalCircuit`) are bounded changes.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 25–41 (statement) and 572–583 (bounded gates and the precision of
  each change); original circuits, `04-compression.tex`, lines 21–43, 143–147 and 199–208.
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Bounded changes of original circuits -/

namespace OriginalCircuit

variable {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [Fintype P]

/-- An original circuit does not increase the norm of a vector. -/
theorem norm_toEuclideanLin_op_le [∀ p, Fintype (Y p)] (w : OriginalCircuit X Y)
    (v : EuclideanSpace ℂ (Config X)) : ‖toEuclideanLin w.op v‖ ≤ ‖v‖ :=
  norm_toEuclideanLin_apply_le_of_norm_le_one w.norm_op_le_one v

/-- **A bounded change.** The original circuit `c` has at most one nonprivate gate, all its
participants lie in `S`, every monomial of its expansion has at most `r` pair effects, its
coefficient sum and its number of monomials are at most `K`, and it takes `x` within `ε` of `y`.

Source: Proposition 7.1 `prop:protocol`, item 2 and the reference vectors,
`06-geometry.tex`, lines 25–41, and the gate count of each change, lines 572–583; original
circuits, `04-compression.tex`, lines 199–208. -/
structure IsBoundedChange [∀ p, Fintype (Y p)] (c : OriginalCircuit X Y) (S : Set P) (r K : ℕ)
    (ε : ℝ) (x : EuclideanSpace ℂ (Config X)) (y : EuclideanSpace ℂ (Config Y)) : Prop where
  /-- At most one nonprivate gate. -/
  nonprivateCount_le : c.nonprivateCount ≤ 1
  /-- The participants of the gate lie in `S`. -/
  participants_subset : ∀ g, (↑(c.participants g) : Set P) ⊆ S
  /-- At most `r` pair effects per monomial and coefficient sum at most `K`. -/
  isExpansionBounded : c.IsExpansionBounded r K
  /-- At most `K` monomials. -/
  isMonomialBounded : c.IsMonomialBounded K
  /-- The error on the reference vector. -/
  norm_op_sub_le : ‖toEuclideanLin c.op x - y‖ ≤ ε

namespace IsBoundedChange

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] [∀ p, Fintype (Z p)]
  {c : OriginalCircuit X Y} {S S' : Set P} {r r' K K' : ℕ} {ε ε' : ℝ}
  {x : EuclideanSpace ℂ (Config X)} {y : EuclideanSpace ℂ (Config Y)}

omit [∀ p, DecidableEq (Y p)] in
/-- A bounded change stays bounded under weaker bounds. -/
theorem mono (h : c.IsBoundedChange S r K ε x y) (hS : S ⊆ S') (hr : r ≤ r') (hK : K ≤ K')
    (hε : ε ≤ ε') : c.IsBoundedChange S' r' K' ε' x y where
  nonprivateCount_le := h.nonprivateCount_le
  participants_subset g := (h.participants_subset g).trans hS
  isExpansionBounded := c.isExpansionBounded_mono h.isExpansionBounded hr (by exact_mod_cast hK)
  isMonomialBounded := c.isMonomialBounded_mono h.isMonomialBounded hK
  norm_op_sub_le := h.norm_op_sub_le.trans hε

/-- A bounded change followed by a circuit without nonprivate gates is a bounded change to the
image of the target. -/
theorem comp_right (h : c.IsBoundedChange S r K ε x y) (e : OriginalCircuit Y Z)
    (he0 : e.nonprivateCount = 0) :
    (c.comp e).IsBoundedChange S r K ε x (toEuclideanLin e.op y) where
  nonprivateCount_le := by
    rw [nonprivateCount_comp, he0, add_zero]
    exact h.nonprivateCount_le
  participants_subset g := by
    rcases g with g | g
    · exact h.participants_subset g
    · exact forall_participants_of_nonprivateCount_eq_zero (Q := fun D ↦ (↑D : Set P) ⊆ S) he0 g
  isExpansionBounded :=
    ⟨h.isExpansionBounded, isExpansionBounded_of_nonprivateCount_eq_zero he0 r K⟩
  isMonomialBounded := ⟨h.isMonomialBounded, isMonomialBounded_of_nonprivateCount_eq_zero he0 K⟩
  norm_op_sub_le := by
    rw [op_comp, toEuclideanLin_mul_apply, ← map_sub]
    exact (e.norm_toEuclideanLin_op_le _).trans h.norm_op_sub_le

omit [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Y p)] in
/-- A circuit without nonprivate gates followed by a bounded change is a bounded change from any
preimage of the source. -/
theorem comp_left {W : P → Type} [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]
    {x' : EuclideanSpace ℂ (Config W)} (e : OriginalCircuit W X) (he0 : e.nonprivateCount = 0)
    (hx : toEuclideanLin e.op x' = x) (h : c.IsBoundedChange S r K ε x y) :
    (e.comp c).IsBoundedChange S r K ε x' y where
  nonprivateCount_le := by
    rw [nonprivateCount_comp, he0, zero_add]
    exact h.nonprivateCount_le
  participants_subset g := by
    rcases g with g | g
    · exact forall_participants_of_nonprivateCount_eq_zero (Q := fun D ↦ (↑D : Set P) ⊆ S) he0 g
    · exact h.participants_subset g
  isExpansionBounded :=
    ⟨isExpansionBounded_of_nonprivateCount_eq_zero he0 r K, h.isExpansionBounded⟩
  isMonomialBounded := ⟨isMonomialBounded_of_nonprivateCount_eq_zero he0 K, h.isMonomialBounded⟩
  norm_op_sub_le := by
    rw [op_comp, toEuclideanLin_mul_apply, hx]
    exact h.norm_op_sub_le

end IsBoundedChange

/-- **A change without nonprivate gate.** A circuit without nonprivate gates is a bounded change
from `x` to its image, for every set of participants and all bounds. -/
theorem isBoundedChange_of_nonprivateCount_eq_zero [∀ p, Fintype (Y p)]
    {c : OriginalCircuit X Y} (h0 : c.nonprivateCount = 0) (S : Set P) (r K : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) (x : EuclideanSpace ℂ (Config X)) :
    c.IsBoundedChange S r K ε x (toEuclideanLin c.op x) where
  nonprivateCount_le := h0.trans_le zero_le_one
  participants_subset :=
    forall_participants_of_nonprivateCount_eq_zero (Q := fun D ↦ (↑D : Set P) ⊆ S) h0
  isExpansionBounded := isExpansionBounded_of_nonprivateCount_eq_zero h0 r K
  isMonomialBounded := isMonomialBounded_of_nonprivateCount_eq_zero h0 K
  norm_op_sub_le := by rw [sub_self, norm_zero]; exact hε

end OriginalCircuit

/-! ### Words and chains of pair resources -/

section Resources

variable [Fintype P] {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  [∀ p, Fintype (Y p)] {S : Set P} {r K : ℕ} {ε : ℝ} {x : EuclideanSpace ℂ (Config X)}
  {y : EuclideanSpace ℂ (Config Y)}

/-- **A word with at most one pair source.** An allowed word using only the parties of `S`, with
at most one pair source, is a bounded change for every `r` and every `K ≥ 1`, with its own error.
These are the words of the births of Lemma 6.5. Source: `05-frames.tex`, lines 396–447, and
`06-geometry.tex`, lines 357–445 and 572–583. -/
theorem Word.isBoundedChange_toOriginalCircuit {w : Word X Y} (hw : w.IsAllowed)
    (hS : w.UsesOnly S) (hsrc : w.sourceCount ≤ 1) (hK : 1 ≤ K)
    (herr : ‖toEuclideanLin w.op x - y‖ ≤ ε) :
    (w.toOriginalCircuit hw).IsBoundedChange S r K ε x y where
  nonprivateCount_le := (w.nonprivateCount_toOriginalCircuit hw).trans_le hsrc
  participants_subset := w.participants_toOriginalCircuit_subset hw hS
  isExpansionBounded := Word.isExpansionBounded_toOriginalCircuit w hw r (by exact_mod_cast hK)
  isMonomialBounded := Word.isMonomialBounded_toOriginalCircuit w hw hK
  norm_op_sub_le := by rwa [w.op_toOriginalCircuit hw]

/-- **A word without pair sources.** An allowed word without pair sources is a bounded change
for every set of participants, every `r` and every `K`, with its own error; it has no nonprivate
gate. These are the words of the two-sheet exchanges of Lemma 6.6, a relabelling of the bases of
the parties followed by private corrections. Source: `05-frames.tex`, lines 474–478, and
`06-geometry.tex`, lines 572–583. -/
theorem Word.isBoundedChange_toOriginalCircuit_of_sourceCount_eq_zero {w : Word X Y}
    (hw : w.IsAllowed) (h0 : w.sourceCount = 0) (S : Set P) (r K : ℕ)
    (herr : ‖toEuclideanLin w.op x - y‖ ≤ ε) :
    (w.toOriginalCircuit hw).IsBoundedChange S r K ε x y where
  nonprivateCount_le :=
    (Word.nonprivateCount_toOriginalCircuit_of_sourceCount_eq_zero w hw h0).trans_le zero_le_one
  participants_subset := OriginalCircuit.forall_participants_of_nonprivateCount_eq_zero
    (Q := fun D ↦ (↑D : Set P) ⊆ S)
    (Word.nonprivateCount_toOriginalCircuit_of_sourceCount_eq_zero w hw h0)
  isExpansionBounded := Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero w hw h0 _ _
  isMonomialBounded := Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero w hw h0 _
  norm_op_sub_le := by rwa [w.op_toOriginalCircuit hw]

/-- **A chain with one pair resource.** An allowed circuit of local contractions, pair sources
and pair effects on all parties, using only the parties of `S`, with at most one gate (as the
chains of the deaths of Lemma 6.5: no pair source and at most one pair effect), is a bounded
change for every `r ≥ 1` and every `K ≥ 1`, with its own error. Source: `05-frames.tex`,
lines 439–446, and `06-geometry.tex`, lines 357–387 and 572–583. -/
theorem Monomial.isBoundedChange_toOriginalCircuit {M : PartyCircuit (ChainGate (P := P)) X Y}
    (hM : M.IsAllowed chainEv ChainGate.IsAllowed) (hS : M.UsesOnly S) (hgates : M.numGates ≤ 1)
    (hr : 1 ≤ r) (hK : 1 ≤ K) (herr : ‖toEuclideanLin (M.op chainEv) x - y‖ ≤ ε) :
    (Monomial.toOriginalCircuit M hM).IsBoundedChange S r K ε x y where
  nonprivateCount_le :=
    (Monomial.nonprivateCount_toOriginalCircuit_eq_numGates M hM).trans_le hgates
  participants_subset := Monomial.participants_toOriginalCircuit_subset M hM hS.forallGate_subset
  isExpansionBounded :=
    Monomial.isExpansionBounded_toOriginalCircuit M hM hr (by exact_mod_cast hK)
  isMonomialBounded := Monomial.isMonomialBounded_toOriginalCircuit M hM hK
  norm_op_sub_le := by rwa [Monomial.op_toOriginalCircuit M hM]

end Resources

/-! ### Bounded changes of the sheet stack -/

section Stack

variable {κ : Type*} [Fintype P] {sys : κ → P → Type} [∀ F p, Fintype (sys F p)]
  [∀ F p, DecidableEq (sys F p)] (ref : ∀ F, EuclideanSpace ℂ (Config (sys F)))
  {W : P → Type} [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- **A bounded change of the sheets.** There is an original circuit from the system of the
sheets `Fs`, followed by the idle system `W`, to that of `Fs'`, followed by `W`, that is a
bounded change, in the sense of `OriginalCircuit.IsBoundedChange`, from the reference vector of
`Fs` with idle vector `ξ` to that of `Fs'`.

Source: Proposition 7.1 `prop:protocol`, items 2 and 4,
`06-geometry.tex`, lines 25–41, and lines 572–583. -/
def HasBoundedChange (Fs Fs' : List κ) (ξ : EuclideanSpace ℂ (Config W)) (S : Set P) (r K : ℕ)
    (ε : ℝ) : Prop :=
  ∃ c : OriginalCircuit (stackSystem sys Fs W) (stackSystem sys Fs' W),
    c.IsBoundedChange S r K ε (stackVec ref Fs ξ) (stackVec ref Fs' ξ)

/-- **A bounded change of the sheets with bounded pair sources**: a bounded change by a circuit
with at most `rs` pair sources in each monomial.

Source: Proposition 7.1 `prop:protocol`, items 2 and 4, `06-geometry.tex`,
lines 25–41 and 572–583; Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
def HasSourceBoundedChange (Fs Fs' : List κ) (ξ : EuclideanSpace ℂ (Config W)) (S : Set P)
    (r K rs : ℕ) (ε : ℝ) : Prop :=
  ∃ c : OriginalCircuit (stackSystem sys Fs W) (stackSystem sys Fs' W),
    c.IsBoundedChange S r K ε (stackVec ref Fs ξ) (stackVec ref Fs' ξ) ∧ c.IsSourceBounded rs

variable {ref} {Fs Fs' Gs : List κ} {ξ : EuclideanSpace ℂ (Config W)} {S S' : Set P}
  {r r' K K' rs rs' : ℕ} {ε ε' : ℝ}

/-- A bounded change of the sheets with bounded pair sources is a bounded change. -/
theorem HasSourceBoundedChange.hasBoundedChange
    (h : HasSourceBoundedChange ref Fs Fs' ξ S r K rs ε) : HasBoundedChange ref Fs Fs' ξ S r K ε :=
  let ⟨c, hc, _⟩ := h
  ⟨c, hc⟩

/-- A bounded change of the sheets stays bounded under weaker bounds. -/
theorem HasBoundedChange.mono (h : HasBoundedChange ref Fs Fs' ξ S r K ε) (hS : S ⊆ S')
    (hr : r ≤ r') (hK : K ≤ K') (hε : ε ≤ ε') : HasBoundedChange ref Fs Fs' ξ S' r' K' ε' :=
  let ⟨c, hc⟩ := h
  ⟨c, hc.mono hS hr hK hε⟩

/-- A bounded change with bounded pair sources stays so under weaker bounds. -/
theorem HasSourceBoundedChange.mono (h : HasSourceBoundedChange ref Fs Fs' ξ S r K rs ε)
    (hS : S ⊆ S') (hr : r ≤ r') (hK : K ≤ K') (hrs : rs ≤ rs') (hε : ε ≤ ε') :
    HasSourceBoundedChange ref Fs Fs' ξ S' r' K' rs' ε' :=
  let ⟨c, hc, hs⟩ := h
  ⟨c, hc.mono hS hr hK hε, hs.mono hrs⟩

/-- **Reordering the sheets is a bounded change** without nonprivate gates, without error and
without pair sources. -/
theorem hasSourceBoundedChange_of_perm (h : Fs.Perm Fs') (ξ : EuclideanSpace ℂ (Config W))
    (S : Set P) (r K rs : ℕ) (hε : 0 ≤ ε) : HasSourceBoundedChange ref Fs Fs' ξ S r K rs ε := by
  obtain ⟨e, he⟩ := exists_relabel_stackVec_of_perm W ref h
  refine ⟨OriginalCircuit.relabel e, ?_, OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero
    rfl rs⟩
  simpa [he] using OriginalCircuit.isBoundedChange_of_nonprivateCount_eq_zero
    (c := OriginalCircuit.relabel e) rfl S r K hε (stackVec ref Fs ξ)

/-- **Reordering the sheets is a bounded change** without nonprivate gates and without
error. -/
theorem hasBoundedChange_of_perm (h : Fs.Perm Fs') (ξ : EuclideanSpace ℂ (Config W)) (S : Set P)
    (r K : ℕ) (hε : 0 ≤ ε) : HasBoundedChange ref Fs Fs' ξ S r K ε :=
  (hasSourceBoundedChange_of_perm h ξ S r K 0 hε).hasBoundedChange

variable (ref) in
/-- The identity change of the sheets. -/
theorem hasSourceBoundedChange_refl (Fs : List κ) (ξ : EuclideanSpace ℂ (Config W)) (S : Set P)
    (r K rs : ℕ) (hε : 0 ≤ ε) : HasSourceBoundedChange ref Fs Fs ξ S r K rs ε :=
  hasSourceBoundedChange_of_perm (List.Perm.refl Fs) ξ S r K rs hε

variable (ref) in
/-- The identity change of the sheets. -/
theorem hasBoundedChange_refl (Fs : List κ) (ξ : EuclideanSpace ℂ (Config W)) (S : Set P)
    (r K : ℕ) (hε : 0 ≤ ε) : HasBoundedChange ref Fs Fs ξ S r K ε :=
  hasBoundedChange_of_perm (List.Perm.refl Fs) ξ S r K hε

/-- A reordering of the sheets followed by a bounded change is a bounded change. -/
theorem HasSourceBoundedChange.perm_left (hp : Fs.Perm Gs)
    (h : HasSourceBoundedChange ref Gs Fs' ξ S r K rs ε) :
    HasSourceBoundedChange ref Fs Fs' ξ S r K rs ε := by
  obtain ⟨e, he⟩ := exists_relabel_stackVec_of_perm W ref hp
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨(OriginalCircuit.relabel e).comp c, hc.comp_left _ rfl (he ξ),
    OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero rfl rs, hs⟩

/-- A reordering of the sheets followed by a bounded change is a bounded change. -/
theorem HasBoundedChange.perm_left (hp : Fs.Perm Gs) (h : HasBoundedChange ref Gs Fs' ξ S r K ε) :
    HasBoundedChange ref Fs Fs' ξ S r K ε := by
  obtain ⟨e, he⟩ := exists_relabel_stackVec_of_perm W ref hp
  obtain ⟨c, hc⟩ := h
  exact ⟨(OriginalCircuit.relabel e).comp c, hc.comp_left _ rfl (he ξ)⟩

/-- A bounded change followed by a reordering of the sheets is a bounded change. -/
theorem HasSourceBoundedChange.perm_right (h : HasSourceBoundedChange ref Fs Gs ξ S r K rs ε)
    (hp : Gs.Perm Fs') : HasSourceBoundedChange ref Fs Fs' ξ S r K rs ε := by
  obtain ⟨e, he⟩ := exists_relabel_stackVec_of_perm W ref hp
  obtain ⟨c, hc, hs⟩ := h
  exact ⟨c.comp (OriginalCircuit.relabel e), by
    simpa [he] using hc.comp_right (OriginalCircuit.relabel e) rfl,
    hs, OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero rfl rs⟩

/-- A bounded change followed by a reordering of the sheets is a bounded change. -/
theorem HasBoundedChange.perm_right (h : HasBoundedChange ref Fs Gs ξ S r K ε)
    (hp : Gs.Perm Fs') : HasBoundedChange ref Fs Fs' ξ S r K ε := by
  obtain ⟨e, he⟩ := exists_relabel_stackVec_of_perm W ref hp
  obtain ⟨c, hc⟩ := h
  exact ⟨c.comp (OriginalCircuit.relabel e), by
    simpa [he] using hc.comp_right (OriginalCircuit.relabel e) rfl⟩

/-- The lift of a bounded change of one sheet to the stack. -/
theorem isBoundedChange_liftOne {F F' : κ} (pre post : List κ)
    {c : OriginalCircuit (sys F) (sys F')} (hc : c.IsBoundedChange S r K ε (ref F) (ref F'))
    (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    (liftOne sys W post c pre).IsBoundedChange S r K ε (stackVec ref (pre ++ F :: post) ξ)
      (stackVec ref (pre ++ F' :: post) ξ) where
  nonprivateCount_le := (nonprivateCount_liftOne sys W post c pre).trans_le hc.nonprivateCount_le
  participants_subset :=
    forall_participants_liftOne (Q := fun D ↦ (↑D : Set P) ⊆ S) sys W post c
      hc.participants_subset pre
  isExpansionBounded := isExpansionBounded_liftOne sys W post c hc.isExpansionBounded pre
  isMonomialBounded := isMonomialBounded_liftOne sys W post c hc.isMonomialBounded pre
  norm_op_sub_le := (norm_op_liftOne_stackVec_sub_le W post c href hξ pre).trans
    hc.norm_op_sub_le

/-- **A change of one sheet, on the whole stack.** A bounded change of the sheet `F` into `F'`,
from `ref F` to `ref F'`, is a bounded change of the stack `pre ++ F :: post` into
`pre ++ F' :: post`, with the same participants, bounds and error, when every reference vector
and the idle vector have norm at most one.

Source: `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem hasBoundedChange_liftOne {F F' : κ} (pre post : List κ)
    {c : OriginalCircuit (sys F) (sys F')} (hc : c.IsBoundedChange S r K ε (ref F) (ref F'))
    (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasBoundedChange ref (pre ++ F :: post) (pre ++ F' :: post) ξ S r K ε :=
  ⟨liftOne sys W post c pre, isBoundedChange_liftOne pre post hc href hξ⟩

/-- **A change of one sheet, on the whole stack**, with at most `rs` pair sources in each
monomial. Source: `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem hasSourceBoundedChange_liftOne {F F' : κ} (pre post : List κ)
    {c : OriginalCircuit (sys F) (sys F')} (hc : c.IsBoundedChange S r K ε (ref F) (ref F'))
    (hs : c.IsSourceBounded rs) (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange ref (pre ++ F :: post) (pre ++ F' :: post) ξ S r K rs ε :=
  ⟨liftOne sys W post c pre, isBoundedChange_liftOne pre post hc href hξ,
    isSourceBounded_liftOne sys W post c hs pre⟩

/-- The lift of a bounded change of two adjacent sheets to the stack. -/
theorem isBoundedChange_liftTwo {F₁ F₂ F₁' F₂' : κ} (pre post : List κ)
    {c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p)}
    (hc : c.IsBoundedChange S r K ε (prodVec (ref F₁) (ref F₂)) (prodVec (ref F₁') (ref F₂')))
    (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    (liftTwo sys W post c pre).IsBoundedChange S r K ε
      (stackVec ref (pre ++ F₁ :: F₂ :: post) ξ) (stackVec ref (pre ++ F₁' :: F₂' :: post) ξ) where
  nonprivateCount_le := (nonprivateCount_liftTwo sys W post c pre).trans_le hc.nonprivateCount_le
  participants_subset :=
    forall_participants_liftTwo (Q := fun D ↦ (↑D : Set P) ⊆ S) sys W post c
      hc.participants_subset pre
  isExpansionBounded := isExpansionBounded_liftTwo sys W post c hc.isExpansionBounded pre
  isMonomialBounded := isMonomialBounded_liftTwo sys W post c hc.isMonomialBounded pre
  norm_op_sub_le := (norm_op_liftTwo_stackVec_sub_le W post c href hξ pre).trans
    hc.norm_op_sub_le

/-- **A change of two adjacent sheets, on the whole stack.** A bounded change of the sheets
`F₁, F₂` into `F₁', F₂'`, from `ref F₁ ⊗ ref F₂` to `ref F₁' ⊗ ref F₂'`, is a bounded change of
the stack `pre ++ F₁ :: F₂ :: post` into `pre ++ F₁' :: F₂' :: post`.

Source: `06-geometry.tex`, lines 39–41, 389–430 and 574–583. -/
theorem hasBoundedChange_liftTwo {F₁ F₂ F₁' F₂' : κ} (pre post : List κ)
    {c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p)}
    (hc : c.IsBoundedChange S r K ε (prodVec (ref F₁) (ref F₂)) (prodVec (ref F₁') (ref F₂')))
    (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasBoundedChange ref (pre ++ F₁ :: F₂ :: post) (pre ++ F₁' :: F₂' :: post) ξ S r K ε :=
  ⟨liftTwo sys W post c pre, isBoundedChange_liftTwo pre post hc href hξ⟩

/-- **A change of two adjacent sheets, on the whole stack**, with at most `rs` pair sources in
each monomial. Source: `06-geometry.tex`, lines 39–41, 389–430 and
574–583. -/
theorem hasSourceBoundedChange_liftTwo {F₁ F₂ F₁' F₂' : κ} (pre post : List κ)
    {c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p)}
    (hc : c.IsBoundedChange S r K ε (prodVec (ref F₁) (ref F₂)) (prodVec (ref F₁') (ref F₂')))
    (hs : c.IsSourceBounded rs) (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange ref (pre ++ F₁ :: F₂ :: post) (pre ++ F₁' :: F₂' :: post) ξ S r K rs
      ε :=
  ⟨liftTwo sys W post c pre, isBoundedChange_liftTwo pre post hc href hξ,
    isSourceBounded_liftTwo sys W post c hs pre⟩

/-- **Activating an auxiliary sheet.** If the sheets `Fs` are a reordering of
`pre ++ F₁ :: F₂ :: post`, for instance with an idle auxiliary copy `F₂` moved next to the main
sheet `F₁`, then a bounded change of the two adjacent sheets is a bounded change of `Fs`.

Source: `06-geometry.tex`, lines 183–186, 389–430 and 658–667. -/
theorem hasBoundedChange_activate {F₁ F₂ F₁' F₂' : κ} {pre post : List κ}
    (hp : Fs.Perm (pre ++ F₁ :: F₂ :: post))
    {c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p)}
    (hc : c.IsBoundedChange S r K ε (prodVec (ref F₁) (ref F₂)) (prodVec (ref F₁') (ref F₂')))
    (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasBoundedChange ref Fs (pre ++ F₁' :: F₂' :: post) ξ S r K ε :=
  (hasBoundedChange_liftTwo pre post hc href hξ).perm_left hp

/-- **Activating an auxiliary sheet**, with at most `rs` pair sources in each monomial.
Source: `06-geometry.tex`, lines 183–186, 389–430 and 658–667. -/
theorem hasSourceBoundedChange_activate {F₁ F₂ F₁' F₂' : κ} {pre post : List κ}
    (hp : Fs.Perm (pre ++ F₁ :: F₂ :: post))
    {c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p)}
    (hc : c.IsBoundedChange S r K ε (prodVec (ref F₁) (ref F₂)) (prodVec (ref F₁') (ref F₂')))
    (hs : c.IsSourceBounded rs) (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange ref Fs (pre ++ F₁' :: F₂' :: post) ξ S r K rs ε :=
  (hasSourceBoundedChange_liftTwo pre post hc hs href hξ).perm_left hp

/-- **A one-sheet change after a reordering.** If the sheets `Fs` are a reordering of
`pre ++ F :: post`, a bounded change of `F` is a bounded change of `Fs`. -/
theorem hasBoundedChange_perm_liftOne {F F' : κ} {pre post : List κ}
    (hp : Fs.Perm (pre ++ F :: post)) {c : OriginalCircuit (sys F) (sys F')}
    (hc : c.IsBoundedChange S r K ε (ref F) (ref F')) (href : ∀ F, ‖ref F‖ ≤ 1)
    (hξ : ‖ξ‖ ≤ 1) : HasBoundedChange ref Fs (pre ++ F' :: post) ξ S r K ε :=
  (hasBoundedChange_liftOne pre post hc href hξ).perm_left hp

/-- **A one-sheet change after a reordering**, with at most `rs` pair sources in each
monomial. -/
theorem hasSourceBoundedChange_perm_liftOne {F F' : κ} {pre post : List κ}
    (hp : Fs.Perm (pre ++ F :: post)) {c : OriginalCircuit (sys F) (sys F')}
    (hc : c.IsBoundedChange S r K ε (ref F) (ref F')) (hs : c.IsSourceBounded rs)
    (href : ∀ F, ‖ref F‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    HasSourceBoundedChange ref Fs (pre ++ F' :: post) ξ S r K rs ε :=
  (hasSourceBoundedChange_liftOne pre post hc hs href hξ).perm_left hp

omit [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)] in
variable (ref) in
/-- **An unchanged sheet.** If the sheet does not change, the empty circuit is a bounded change
of the sheet for every set of participants and all bounds.

Source: `06-geometry.tex`, lines 432–438 and 529–541. -/
theorem exists_isBoundedChange_of_eq {F F' : κ} (h : F = F') (S : Set P) (r K : ℕ)
    (hε : 0 ≤ ε) :
    ∃ c : OriginalCircuit (sys F) (sys F'), c.IsBoundedChange S r K ε (ref F) (ref F') := by
  subst h
  refine ⟨OriginalCircuit.done _, ?_⟩
  simpa using OriginalCircuit.isBoundedChange_of_nonprivateCount_eq_zero
    (c := OriginalCircuit.done (sys F)) rfl S r K hε (ref F)

end Stack

end QuantumCircuit.Party
