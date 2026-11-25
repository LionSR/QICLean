/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Residual
import QICLean.Circuit.Party.Source.LocalPartCoarsen
import QICLean.Circuit.Party.Source.ZeroPartyGate

/-!
# The exterior scalar of the expansion along all parties

At a gate with an empty cell, the partial expansion keeps the sum of the coefficients of the
gate; the product of these sums over the circuit is `SourceCircuit.emptyGateScalar`, of modulus at
most one. When every party is affected, no party goes to the exterior party `none`, so its
bases have one configuration and every operation there is a scalar. The local part of a branch,
its residual in the common slots, the private preparation of a product input and the prepared
source word act at `none` by `emptyGateScalar` (`1` for the private preparation): every entry of
their party operations there is this scalar. At a party outside the cell of a gate, the local
part of the branch of the gate is the identification of equal bases.

## Main definitions

* `QuantumCircuit.Party.SourceCircuit.emptyGateScalar`.

## Main results

* `QuantumCircuit.Party.SourceInventory.slotSystem_eq_of_forall_ne`.
* `QuantumCircuit.Party.SourceCircuit.norm_emptyGateScalar_le_one`.
* `QuantumCircuit.Party.SourceCircuit.localPartOp_partialWord_all_none_apply`,
  `QuantumCircuit.Party.SourceCircuit.partyOp_partialResidual_all_none_apply`,
  `QuantumCircuit.Party.SourceCircuit.partyOp_sourcePrivatePreparation_none_apply`,
  `QuantumCircuit.Party.SourceCircuit.partyOp_partialSourceWord_none_apply`.
* `QuantumCircuit.Party.SourceCircuit.localPartOp_partialWord_all_gate_of_notMem`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 24–28, 137–139, 233–267, 351–434 and 565–588.

Adapted from TNLean, `TNLean/Lattice/Compression/EmptyGateScalar.lean`,
`TNLean/Lattice/Compression/NoneResidualGate.lean`,
`TNLean/Lattice/Compression/NoneResidualOperations.lean`,
`TNLean/Lattice/Compression/NoneResidualScalar.lean`,
`TNLean/Lattice/Compression/NoneSourceWordScalar.lean`,
`TNLean/Lattice/Compression/AllPartialGate.lean`,
`TNLean/Lattice/Compression/NonincidentAllGateRestriction.lean` and
`TNLean/Lattice/Compression/SourcePrivatePreparationRestriction.lean` at commit `a05f5d6d0a`
(Apache-2.0). Changes: an operation between two one-element bases is stated entrywise, every
entry being the scalar, instead of as the scalar times the identity through a heterogeneous
equality; the frame case is gone.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Matrices between one-element bases -/

/-- Every entry of a matrix is `c`. -/
private def ConstEntries {α β : Type} (M : Matrix α β ℂ) (c : ℂ) : Prop := ∀ a b, M a b = c

/-- A product of matrices with constant entries through a one-point index has constant entries. -/
private theorem ConstEntries.mul {α β γ : Type} [Fintype β] [Subsingleton β] [Nonempty β]
    {M : Matrix α β ℂ} {N : Matrix β γ ℂ} {c d : ℂ} (hM : ConstEntries M c)
    (hN : ConstEntries N d) : ConstEntries (M * N) (c * d) := fun a b ↦ by
  obtain ⟨m⟩ := ‹Nonempty β›
  rw [mul_apply, Fintype.sum_subsingleton _ m, hM, hN]

/-- The matrix of an equivalence onto a one-point type has all entries `1`. -/
private theorem ConstEntries.toMatrix {α β : Type} [DecidableEq β] [Subsingleton β] (e : α ≃ β) :
    ConstEntries (e.toPEquiv.toMatrix : Matrix α β ℂ) 1 := fun a b ↦ by
  rw [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    ite_eq_left (by rw [Subsingleton.elim (e a) b]; rfl)]

/-- Reindexing keeps constant entries. -/
private theorem ConstEntries.submatrix {α β α' β' : Type} {M : Matrix α β ℂ} {c : ℂ}
    (hM : ConstEntries M c) (f : α' → α) (g : β' → β) : ConstEntries (M.submatrix f g) c :=
  fun a b ↦ hM (f a) (g b)

/-- The identity on a one-point type tensored with a matrix of constant entries has constant
entries. -/
private theorem ConstEntries.one_kronecker {W α β : Type} [DecidableEq W] [Subsingleton W]
    {M : Matrix α β ℂ} {c : ℂ} (hM : ConstEntries M c) :
    ConstEntries ((1 : Matrix W W ℂ) ⊗ₖ M) c := fun a b ↦ by
  rw [kroneckerMap_apply, one_apply, ite_eq_left (Subsingleton.elim _ _), one_mul, hM]

/-- One basis element, transported along an equality of types. -/
private theorem subsingleton_of_eq {α β : Type} (h : α = β) [Subsingleton β] : Subsingleton α :=
  (Equiv.cast h).subsingleton

/-- A type equal to a nonempty type is nonempty. -/
private theorem nonempty_of_eq {α β : Type} (h : α = β) [Nonempty β] : Nonempty α :=
  (Equiv.cast h).nonempty

/-! ### Systems at a party outside every source -/

namespace SourceInventory

/-- At a party that is no endpoint of the sources, the prepared system has the bases of the
system. -/
private theorem system_eq_of_forall_ne (Z : P → Type) (q : P) :
    (S : SourceInventory P) → (∀ s ∈ S, s.left ≠ q ∧ s.right ≠ q) → S.system Z q = Z q
  | [], _ => rfl
  | s :: S, hS => by
    rw [system_cons]
    exact (addPair_of_ne _ _ _ (hS s List.mem_cons_self).1.symm
      (hS s List.mem_cons_self).2.symm).trans
      (system_eq_of_forall_ne Z q S fun t ht ↦ hS t (List.mem_cons_of_mem _ ht))

/-- At a party that is no endpoint of the slots, the slot system has the bases of the system.
Source: `04-compression.tex`, lines 246–267. -/
theorem slotSystem_eq_of_forall_ne (Z : P → Type) (q : P) : (R : SourceInventory P) →
    (B : SlotBases R.length) → (∀ i, (R.get i).left ≠ q ∧ (R.get i).right ≠ q) →
      slotSystem R B Z q = Z q
  | [], _, _ => rfl
  | _ :: R, B, hR =>
    (addPair_of_ne _ _ _ (hR 0).1.symm (hR 0).2.symm).trans
      (slotSystem_eq_of_forall_ne Z q R B.tail fun i ↦ hR i.succ)

/-- Running operations beside fresh factors that avoid the party `q` keeps a constant entry
there. -/
private theorem constEntries_liftOps {X X' : P → Type} (q : P)
    (A : ∀ s, Matrix (X' s) (X s) ℂ) {c : ℂ} (hA : ConstEntries (A q) c) :
    (S : SourceInventory P) → (∀ s ∈ S, s.left ≠ q ∧ s.right ≠ q) →
      ConstEntries (S.liftOps A q) c
  | [], _ => hA
  | s :: S, hS => by
    have ih := constEntries_liftOps q A hA S fun t ht ↦ hS t (List.mem_cons_of_mem _ ht)
    have : Subsingleton (pairFactor s.distinct s.leftBasis s.rightBasis q) := by
      unfold pairFactor
      rw [ite_eq_right (hS s List.mem_cons_self).1.symm,
        ite_eq_right (hS s List.mem_cons_self).2.symm]
      infer_instance
    exact (ConstEntries.one_kronecker ih).submatrix _ _

end SourceInventory

/-- A word beside a fresh pair away from the party `q` keeps a constant entry at `q`. -/
private theorem constEntries_partyOp_liftPair {p₀ q₀ : P} (hpq : p₀ ≠ q₀)
    (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {S T : P → Type}
    [∀ s, Fintype (S s)] [∀ s, DecidableEq (S s)] [∀ s, Fintype (T s)] [∀ s, DecidableEq (T s)]
    (c : Word S T) {q : P} (hp : q ≠ p₀) (hq : q ≠ q₀) [Subsingleton (S q)] [Nonempty (S q)]
    [Subsingleton (T q)] [Nonempty (T q)] {a : ℂ} (hc : ConstEntries (c.partyOp q) a) :
    ConstEntries ((PartyCircuit.liftPair hpq α β c).partyOp q) a := by
  have hpf : pairFactor hpq α β q = Unit := by simp [pairFactor, hp, hq]
  have : Subsingleton (pairFactor hpq α β q) := subsingleton_of_eq hpf
  have : Nonempty (pairFactor hpq α β q) := nonempty_of_eq hpf
  have : Subsingleton (addPair S hpq α β q) := subsingleton_of_eq (addPair_of_ne _ _ _ hp hq)
  have : Subsingleton (addPair T hpq α β q) := subsingleton_of_eq (addPair_of_ne _ _ _ hp hq)
  have h := ((ConstEntries.toMatrix (addPairSiteEquiv hpq α β T q)).mul
    (ConstEntries.one_kronecker (W := pairFactor hpq α β q) hc)).mul
    (ConstEntries.toMatrix (addPairSiteEquiv hpq α β S q).symm)
  rw [one_mul, mul_one] at h
  rw [PartyCircuit.liftPair, PartyCircuit.partyOp_comp, PartyCircuit.partyOp_comp,
    PartyCircuit.partyOp_frame]
  exact h

/-- A word beside the fresh factors of slots away from the party `q` keeps a constant entry at
`q`. -/
private theorem constEntries_partyOp_liftSlots (q : P) {a : ℂ} :
    (R : SourceInventory P) → (B : SourceInventory.SlotBases R.length) →
    (∀ i, (R.get i).left ≠ q ∧ (R.get i).right ≠ q) → {S T : P → Type} →
    [∀ s, Fintype (S s)] → [∀ s, DecidableEq (S s)] → [∀ s, Fintype (T s)] →
    [∀ s, DecidableEq (T s)] → [Unique (S q)] → [Unique (T q)] → (c : Word S T) →
      ConstEntries (c.partyOp q) a →
        ConstEntries ((PartyCircuit.liftSlots R B c).partyOp q) a
  | [], _, _, _, _, _, _, _, _, _, _, _, hc => hc
  | r :: R, B, hR, S, T, _, _, _, _, _, _, c, hc => by
    let : Unique (SourceInventory.slotSystem R B.tail S q) :=
      (Equiv.cast (SourceInventory.slotSystem_eq_of_forall_ne S q R B.tail
        fun i ↦ hR i.succ)).unique
    let : Unique (SourceInventory.slotSystem R B.tail T q) :=
      (Equiv.cast (SourceInventory.slotSystem_eq_of_forall_ne T q R B.tail
        fun i ↦ hR i.succ)).unique
    exact constEntries_partyOp_liftPair r.distinct (B.left 0) (B.right 0)
      (PartyCircuit.liftSlots R B.tail c) (hR 0).1.symm (hR 0).2.symm
      (constEntries_partyOp_liftSlots q R B.tail (fun i ↦ hR i.succ) c hc)

namespace SourceCircuit

variable {X Y Z : P → Type}

/-! ### The scalar of the gates with an empty cell -/

/-- The product of the coefficient sums of the gates whose cell is empty. Source:
`04-compression.tex`, lines 24–28 and 565–588. -/
noncomputable def emptyGateScalar : {X Y : P → Type} → SourceCircuit X Y → ℂ
  | _, _, PartyCircuit.done _ => 1
  | _, _, PartyCircuit.gate D _ g => if D.Nonempty then 1 else ∑ ξ, g.coeff ξ
  | _, _, PartyCircuit.localOp _ _ _ => 1
  | _, _, PartyCircuit.localOps _ => 1
  | _, _, PartyCircuit.comp c c' => emptyGateScalar c * emptyGateScalar c'

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The empty circuit contributes `1`. -/
@[simp] theorem emptyGateScalar_done :
    emptyGateScalar (PartyCircuit.done X : SourceCircuit X X) = 1 :=
  rfl

/-- A gate contributes its coefficient sum when its cell is empty, `1` otherwise. -/
theorem emptyGateScalar_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y) :
    emptyGateScalar (PartyCircuit.gate D hY g : SourceCircuit X Y) =
      if D.Nonempty then 1 else ∑ ξ, g.coeff ξ :=
  rfl

/-- A gate with an empty cell contributes its coefficient sum. Source: `04-compression.tex`,
lines 24–28 and 565–588. -/
theorem emptyGateScalar_gate_of_not_nonempty (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (hD : ¬ D.Nonempty) :
    emptyGateScalar (PartyCircuit.gate D hY g : SourceCircuit X Y) = ∑ ξ, g.coeff ξ :=
  ite_eq_right hD

/-- A local operation contributes `1`. -/
@[simp] theorem emptyGateScalar_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s)
    (U : Matrix (Y p) (X p) ℂ) :
    emptyGateScalar (PartyCircuit.localOp p hY U : SourceCircuit X Y) = 1 :=
  rfl

/-- Local operations at every party contribute `1`. -/
@[simp] theorem emptyGateScalar_localOps (U : ∀ p, Matrix (Y p) (X p) ℂ) :
    emptyGateScalar (PartyCircuit.localOps U : SourceCircuit X Y) = 1 :=
  rfl

/-- The scalar of a composition is the product of the scalars of its parts. -/
@[simp] theorem emptyGateScalar_comp (w : SourceCircuit X Y) (w' : SourceCircuit Y Z) :
    emptyGateScalar (PartyCircuit.comp w w') = emptyGateScalar w * emptyGateScalar w' :=
  rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
-- The finiteness of the bases gives the bound of the prepared gates.
/-- **The exterior scalar is a contraction**, every prepared gate being a contraction; neither a
nonzero sum nor a label is needed. Source: `04-compression.tex`, lines 24–28 and 565–588. -/
theorem norm_emptyGateScalar_le_one [Fintype P] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) → ‖w.emptyGateScalar‖ ≤ 1
  | _, _, _, _, PartyCircuit.done _ => norm_one.le
  | X, Y, _, _, PartyCircuit.gate D hY g => by
    rw [emptyGateScalar_gate]
    split_ifs with hD
    · exact norm_one.le
    · have : IsEmpty ↥D := ⟨fun s ↦ hD ⟨s.1, s.2⟩⟩
      exact g.gate.norm_coeffSum_le_one_of_isEmpty
  | _, _, _, _, PartyCircuit.localOp _ _ _ => norm_one.le
  | _, _, _, _, PartyCircuit.localOps _ => norm_one.le
  | _, _, _, _, PartyCircuit.comp c c' =>
    (norm_mul_le _ _).trans (by
      simpa using mul_le_mul (norm_emptyGateScalar_le_one c) (norm_emptyGateScalar_le_one c')
        (norm_nonneg _) zero_le_one)

/-! ### The exterior party of the expansion along all parties -/

variable [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- No source of a word read on the blocks of all parties has an exterior endpoint. -/
private theorem forall_sources_coarsen_all_ne_none {S T : P → Type} [∀ p, Fintype (S p)]
    [∀ p, DecidableEq (S p)] (u : Word S T) :
    ∀ s ∈ (Word.coarsen (affectedOwner fun _ ↦ true) u).sources,
      s.left ≠ none ∧ s.right ≠ none := by
  intro s hs
  rw [Word.sources_coarsen, SourceInventory.mapOwner] at hs
  obtain ⟨t, -, ht⟩ := List.mem_filterMap.mp hs
  simp only [PairSource.mapOwner] at ht
  split_ifs at ht
  cases Option.some.inj ht
  exact ⟨affectedOwner_true_ne_none _, affectedOwner_true_ne_none _⟩

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- No source of a branch of the expansion along all parties has an exterior endpoint. -/
private theorem forall_sources_partialWord_all_ne_none (w : SourceCircuit X Y)
    (ξ : Choices (fun _ ↦ true) w) :
    ∀ s ∈ (partialWord (fun _ ↦ true) w ξ).sources, s.left ≠ none ∧ s.right ≠ none := by
  intro s hs
  obtain ⟨t, -, -, rfl⟩ := (mem_sources_partialWord _ w ξ s).mp hs
  exact ⟨affectedOwner_true_ne_none _, affectedOwner_true_ne_none _⟩

/-- The exterior block of the blocks of all parties has one configuration. -/
private instance instUniqueBlockSystemNone (Z : P → Type) :
    Unique (blockSystem (affectedOwner fun _ : P ↦ true) Z none) :=
  uniqueBlockSystemNone Z

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- A system prepared by sources away from the exterior party has one configuration there. -/
private theorem subsingleton_system_none (Z : P → Type)
    (S : SourceInventory (Option {_p : P // true = true}))
    (hS : ∀ s ∈ S, s.left ≠ none ∧ s.right ≠ none) :
    Subsingleton (S.system (blockSystem (affectedOwner fun _ ↦ true) Z) none) :=
  subsingleton_of_eq (SourceInventory.system_eq_of_forall_ne _ none S hS)

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- A system prepared by sources away from the exterior party has a configuration there. -/
private theorem nonempty_system_none (Z : P → Type)
    (S : SourceInventory (Option {_p : P // true = true}))
    (hS : ∀ s ∈ S, s.left ≠ none ∧ s.right ≠ none) :
    Nonempty (S.system (blockSystem (affectedOwner fun _ ↦ true) Z) none) :=
  nonempty_of_eq (SourceInventory.system_eq_of_forall_ne _ none S hS)

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- No party of the blocks of all parties is sent to the exterior party. -/
private theorem notMem_parties_coarsen_all_none {S T : P → Type} [∀ p, Fintype (S p)]
    [∀ p, DecidableEq (S p)] (u : Word S T) :
    none ∉ PartyCircuit.parties (Word.coarsen (affectedOwner fun _ ↦ true) u) := fun h ↦ by
  obtain ⟨r, -, hr⟩ := Finset.mem_image.mp (Word.parties_coarsen_subset _ u h)
  exact affectedOwner_true_ne_none r hr

omit [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- A word read on the blocks of all parties and naming no party at the exterior party acts
there by `1`. -/
private theorem constEntries_localPartOp_coarsen_all {S T : P → Type} [∀ p, Fintype (S p)]
    [∀ p, DecidableEq (S p)] (u : Word S T) :
    ConstEntries ((Word.coarsen (affectedOwner fun _ ↦ true) u).localPartOp none) 1 := by
  obtain ⟨h, e⟩ := Word.localPartOp_of_notMem_parties _ none (notMem_parties_coarsen_all_none u)
  have := subsingleton_system_none S _ (forall_sources_coarsen_all_ne_none u)
  rw [e]
  exact ConstEntries.toMatrix _

/-- The recursion behind `localPartOp_partialWord_all_none_apply`. -/
private theorem constEntries_localPartOp_partialWord_all : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (ξ : Choices (fun _ ↦ true) w) →
      ConstEntries ((partialWord (fun _ ↦ true) w ξ).localPartOp none) w.emptyGateScalar
  | X, _, _, _, PartyCircuit.done _, _ => fun y x ↦ by
    have h := ConstEntries.toMatrix (Equiv.refl (blockSystem (affectedOwner fun _ ↦ true) X none))
    rw [Equiv.toPEquiv_refl, PEquiv.toMatrix_refl] at h
    exact h y x
  | _, _, _, _, PartyCircuit.gate D hY g, ξ => by
    rw [emptyGateScalar_gate]
    by_cases hD : D.Nonempty
    · have h : PreparedGate.IsTouched (fun _ ↦ true) D := ⟨hD.choose, hD.choose_spec, rfl⟩
      rw [ite_eq_left hD, partialWord_gate_of_isTouched _ D hY g h]
      exact constEntries_localPartOp_coarsen_all _
    · have h : ¬ PreparedGate.IsTouched (fun _ ↦ true) D := fun ⟨s, hs, _⟩ ↦ hD ⟨s, hs⟩
      rw [ite_eq_right hD, partialWord_gate_of_not_isTouched _ D hY g h, Word.localPartOp_localOp,
        PartyCircuit.localOpFamily_self]
      intro y x
      erw [subregionPlaceBetween_apply]
      rw [ite_eq_left fun (v : {v // v ∈ blockPreimage (affectedOwner fun _ : P ↦ true) {none}})
        _ ↦ (affectedOwner_true_ne_none v.1
          ((mem_blockPreimage_singleton (f := affectedOwner fun _ : P ↦ true)).mp v.2)).elim]
      have : IsEmpty ↥D := ⟨fun s ↦ hD ⟨s.1, s.2⟩⟩
      exact g.gate.eval_apply_of_isEmpty _ _
  | _, _, _, _, PartyCircuit.localOp p hY U, _ => by
    rw [partialWord_localOp]
    exact constEntries_localPartOp_coarsen_all _
  | _, _, _, _, PartyCircuit.localOps U, _ => by
    rw [partialWord_localOps]
    exact constEntries_localPartOp_coarsen_all _
  | _, _, _, _, @PartyCircuit.comp _ _ _ M _ _ _ c c', ξ => by
    rw [partialWord_comp, emptyGateScalar_comp, mul_comm]
    have := subsingleton_system_none M _ (forall_sources_partialWord_all_ne_none c' ξ.2)
    have := nonempty_system_none M _ (forall_sources_partialWord_all_ne_none c' ξ.2)
    rw [Word.localPartOp_comp]
    exact ((constEntries_localPartOp_partialWord_all c' ξ.2).mul
      (SourceInventory.constEntries_liftOps none _ (constEntries_localPartOp_partialWord_all c ξ.1)
        _ (forall_sources_partialWord_all_ne_none c' ξ.2))).submatrix _ _

/-- **The local part of a branch of the expansion along all parties acts at the exterior party
by the exterior scalar**: each of its entries there is `emptyGateScalar`. No scalar is
cancelled, and no label or normalization is needed. Source: `04-compression.tex`,
lines 24–28, 246–251 and 351–417. -/
theorem localPartOp_partialWord_all_none_apply : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) → (ξ : Choices (fun _ ↦ true) w) →
    (y : blockSystem (affectedOwner fun _ ↦ true) Y none) →
    (x : SourceInventory.system (partialWord (fun _ ↦ true) w ξ).sources
      (blockSystem (affectedOwner fun _ ↦ true) X) none) →
      (partialWord (fun _ ↦ true) w ξ).localPartOp none y x = w.emptyGateScalar :=
  fun w ξ ↦ constEntries_localPartOp_partialWord_all w ξ

/-- At a party outside the cell of a gate, the local part of its branch in the expansion along
all parties is the identification of equal bases, whatever the label; with an empty cell no label
is requested. Source: `04-compression.tex`, lines 351–381, 409–434 and 565–588. -/
theorem localPartOp_partialWord_all_gate_of_notMem (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (p : P) (hp : p ∉ D)
    (ξ : Choices (fun _ ↦ true) (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    ∃ h : blockSystem (affectedOwner fun _ ↦ true) Y (some ⟨p, rfl⟩) =
        SourceInventory.system
          (partialWord (fun _ ↦ true) (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ).sources
          (blockSystem (affectedOwner fun _ ↦ true) X) (some ⟨p, rfl⟩),
      (partialWord (fun _ ↦ true) (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ).localPartOp
        (some ⟨p, rfl⟩) = (Equiv.cast h).toPEquiv.toMatrix := by
  by_cases ht : PreparedGate.IsTouched (fun _ ↦ true) D
  · rw [partialWord_gate_of_isTouched _ D hY g ht ξ]
    have hf : ∀ r, affectedOwner (fun _ ↦ true) r = some ⟨p, rfl⟩ ↔ r = p := fun r ↦ by
      simp [affectedOwner]
    have hS : ∀ s ∈ Word.sources (Word.onCell D hY (g.gate.branchWord (choiceLabel _ hY g ht ξ))),
        s.left ≠ p ∧ s.right ≠ p := by
      intro s hs
      rw [Word.sources_onCell] at hs
      obtain ⟨t, -, -, rfl⟩ := (SourceInventory.mem_mapOwner _ _ _).mp hs
      exact ⟨fun e ↦ hp (e ▸ t.left.2), fun e ↦ hp (e ▸ t.right.2)⟩
    obtain ⟨h', e'⟩ := Word.localPartOp_onCell_of_notMem D hY
      (g.gate.branchWord (choiceLabel _ hY g ht ξ)) hp
    obtain ⟨h₁, h₂, eC⟩ := Word.coarsenFiberEquiv_apply_of_forall_ne _ hf
      (Word.onCell D hY (g.gate.branchWord (choiceLabel _ hY g ht ξ)))
      (blockFiberEquiv _ hf X) hS
    have hAB : (fun v : {v // v ∈ blockPreimage (affectedOwner fun _ : P ↦ true)
        {some ⟨p, rfl⟩}} ↦ Y v.1) = fun v ↦ X v.1 :=
      funext fun v ↦ hY v.1 (by rw [eq_of_mem_blockPreimage_of_fiber _ hf v.2]; exact hp)
    have hB : blockSystem (affectedOwner fun _ : P ↦ true) Y (some ⟨p, rfl⟩) =
        blockSystem (affectedOwner fun _ : P ↦ true) X (some ⟨p, rfl⟩) :=
      blockSystem_eq_of_notMem _ (D' := D.image (affectedOwner fun _ : P ↦ true))
        (fun v hv ↦ hY v fun hvD ↦ hv (by simpa using ⟨v, hvD, rfl⟩)) _
        (fun hb ↦ hp (by obtain ⟨r, hr, e⟩ := Finset.mem_image.mp hb; exact (hf r).mp e ▸ hr))
    refine ⟨hB.trans h₁.symm, ?_⟩
    rw [Word.localPartOp_coarsen_of_fiber _ hf, e']
    rw [toMatrix_toPEquiv_submatrix]
    refine congrArg (fun e ↦ (Equiv.toPEquiv e).toMatrix) (Equiv.ext fun y ↦ ?_)
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_eq, eC]
    symm
    change cast h₂ ((cast h₁ (cast (hB.trans h₁.symm) y))
      ⟨p, mem_blockPreimage_of_fiber _ hf⟩) = cast h' (y ⟨p, mem_blockPreimage_of_fiber _ hf⟩)
    rw [cast_cast, cast_pi_apply hAB]
    exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))
  · rw [partialWord_gate_of_not_isTouched _ D hY g ht ξ]
    exact Word.localPartOp_of_notMem_parties _ _
      fun h ↦ Option.some_ne_none _ (Finset.mem_singleton.mp h)

/-- **The residual of a branch of the expansion along all parties acts at the exterior party by
the exterior scalar.** Source: `04-compression.tex`, lines 24–28, 246–267 and 409–434. -/
theorem partyOp_partialResidual_all_none_apply (w : SourceCircuit X Y)
    (ξ : Choices (fun _ ↦ true) w) (y : blockSystem (affectedOwner fun _ ↦ true) Y none)
    (x : SourceInventory.slotSystem (partialSlots (fun _ ↦ true) w)
      (partialSlotBases (fun _ ↦ true) w) (blockSystem (affectedOwner fun _ ↦ true) X) none) :
    PartyCircuit.partyOp (partialResidual (fun _ ↦ true) w ξ) none y x = w.emptyGateScalar := by
  have := subsingleton_system_none X _ (forall_sources_partialWord_all_ne_none w ξ)
  have := nonempty_system_none X _ (forall_sources_partialWord_all_ne_none w ξ)
  have : Subsingleton (SourceInventory.slotSystem (partialSlots (fun _ ↦ true) w)
      (partialSlotBases (fun _ ↦ true) w) (blockSystem (affectedOwner fun _ ↦ true) X) none) :=
    subsingleton_of_eq (SourceInventory.slotSystem_eq_of_forall_ne _ none _ _
      (partialSlots_all_ne_none w))
  have h := (constEntries_localPartOp_partialWord_all w ξ).mul (ConstEntries.toMatrix
    (SourceInventory.slotSystemEquiv _ _ _ _ (ofSlots_partialSlotVector _ w ξ) _ none).symm)
  rw [mul_one] at h
  exact h y x

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **The private preparation acts at the exterior party as the identity** of its one-element
bases. Source: `04-compression.tex`, lines 137–139, 246–267 and 409–434. -/
theorem partyOp_sourcePrivatePreparation_none_apply (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (y : SourceInventory.slotSystem
      (partialSlots (fun _ ↦ true) w) (partialSlotBases (fun _ ↦ true) w)
      (blockSystem (affectedOwner fun _ ↦ true) X) none)
    (x : allSourceSystem w none) :
    PartyCircuit.partyOp (sourcePrivatePreparation w φ) none y x = 1 :=
  constEntries_partyOp_liftSlots none _ _ (partialSlots_all_ne_none w) _
    (fun y x ↦ Word.partyOp_coarsen_apply_of_forall_ne _ (Word.prepareProduct φ) trivial
      affectedOwner_true_ne_none y x) y x

/-- **The prepared source word acts at the exterior party by the exterior scalar.** Source:
`04-compression.tex`, lines 137–139, 246–267 and 565–588. -/
theorem partyOp_partialSourceWord_none_apply (w : SourceCircuit X Y)
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (ξ : Choices (fun _ ↦ true) w)
    (y : blockSystem (affectedOwner fun _ ↦ true) Y none) (x : allSourceSystem w none) :
    PartyCircuit.partyOp (partialSourceWord w φ ξ) none y x = w.emptyGateScalar := by
  have : Unique (SourceInventory.slotSystem (partialSlots (fun _ ↦ true) w)
      (partialSlotBases (fun _ ↦ true) w) (blockSystem (affectedOwner fun _ ↦ true) X) none) :=
    (Equiv.cast (SourceInventory.slotSystem_eq_of_forall_ne _ none _ _
      (partialSlots_all_ne_none w))).unique
  have h := ConstEntries.mul (fun y x ↦ partyOp_partialResidual_all_none_apply w ξ y x)
    fun y x ↦ partyOp_sourcePrivatePreparation_none_apply w φ y x
  rw [mul_one] at h
  exact h y x

end SourceCircuit

end QuantumCircuit.Party
