/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Substitution
import QICLean.Circuit.Party.Compression.PartialExpansion.Residual

/-!
# One residual for all substituted vectors

A substituted branch of the partial expansion keeps the positions and labels of its sources: its
sources are the common slots with the substituted vectors at the chosen labels
(`SourceCircuit.ofSlots_partialWithSources`). The vectors do not enter the operations that act
after the sources are prepared, so the residual of the branch evaluates every substitution in
the same slot system (`SourceCircuit.op_partialResidual_mul_prepareSlots_substituted`); only the
vectors at positions with two exterior endpoints, which become local preparations, must be those
of the gates.

## Main results

* `QuantumCircuit.Party.SourceCircuit.ofSlots_partialWithSources`.
* `QuantumCircuit.Party.SourceCircuit.op_partialResidual_mul_prepareSlots_substituted`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 338–434.

Adapted from TNLean, `TNLean/Lattice/Compression/SourceSubstitutionInventory.lean` and
`TNLean/Lattice/Compression/SourceSubstitutionResidual.lean` at commit `a05f5d6d0a`
(Apache-2.0). Changes: the equality of the residual words is stated as the identity of operators
it is used for.
-/

open Matrix ManyBody

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P] [Fintype P]

namespace SourceCircuit

variable (A : P → Bool) {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- The sources of a substituted branch: the kept pair sources of the positions with the
substituted vectors at the chosen labels. -/
private theorem sources_partialWithSources_eq_filterMap : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (η : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)) → (ξ : Choices A w) →
      (partialWithSources A w η ξ).sources = (sourceOrder w).filterMap fun e ↦
        if h : IsTouched A w e.1 then
          (pairSourceAt w e (η e (choiceAt A w ξ e.1 h))).mapOwner (affectedOwner A)
        else none
  | _, _, _, _, PartyCircuit.done _, _, _ => rfl
  | _, _, _, _, PartyCircuit.gate D hY g, η, ξ => by
    refine Eq.trans ?_ ((congrArg _ (sourceOrder_gate D hY g)).trans (List.filterMap_map ..)).symm
    by_cases h : PreparedGate.IsTouched A D
    · rw [show partialWithSources A (PartyCircuit.gate D hY g : SourceCircuit _ _) η ξ = _ from
        dite_eq_left h, Word.sources_coarsen, Word.sources_onCell]
      erw [PreparedSourceGate.sources_branchWithSources]
      simp only [SourceInventory.mapOwner, SourceInventory.ofSlots, List.ofFn_eq_map,
        List.filterMap_map, List.filterMap_filterMap]
      refine List.filterMap_congr fun i _ ↦ ?_
      let w₀ : SourceCircuit _ _ := PartyCircuit.gate D hY g
      let e₀ : w₀.sourceLocations := ⟨(), i⟩
      refine Eq.trans ?_ (dite_eq_left (c := IsTouched A w₀ e₀.1)
        (t := fun h ↦ (pairSourceAt w₀ e₀ (η e₀ (choiceAt A w₀ ξ e₀.1 h))).mapOwner
          (affectedOwner A)) (e := fun _ ↦ none) h).symm
      rw [Function.comp_apply, PairSource.mapOwner,
        dite_eq_right fun h' ↦ (g.gate.slots.get i).distinct (Subtype.ext h'), Option.bind_some]
      rfl
    · rw [show partialWithSources A (PartyCircuit.gate D hY g : SourceCircuit _ _) η ξ = _ from
        dite_eq_right h]
      exact (List.filterMap_eq_nil_iff.mpr fun i _ ↦ dite_eq_right h).symm
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _ => by
    rw [show partialWithSources A _ _ _ = Word.coarsen _ _ from rfl, Word.sources_coarsen]
    rfl
  | _, _, _, _, PartyCircuit.localOps _, _, _ => by
    rw [show partialWithSources A _ _ _ = Word.coarsen _ _ from rfl, Word.sources_coarsen]
    rfl
  | _, _, _, _, PartyCircuit.comp c c', η, ξ => by
    rw [partialWithSources_comp, Word.sources_comp]
    refine (congrArg₂ (· ++ ·) (sources_partialWithSources_eq_filterMap c' _ _)
      (sources_partialWithSources_eq_filterMap c _ _)).trans ?_
    rw [sourceOrder_comp]
    erw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
    rfl


/-! ### Words that differ only in the vectors of their sources -/

section Variants

variable {Q : Type} [DecidableEq Q]

/-- Two pair sources with the same endpoints and bases. -/
private def SameShape (s t : PairSource Q) : Prop :=
  ∃ v : EuclideanSpace ℂ (s.leftBasis × s.rightBasis), t = { s with vector := v }

omit [DecidableEq Q] in
/-- Every pair source has its own shape. -/
private theorem sameShape_refl (s : PairSource Q) : SameShape s s := ⟨s.vector, rfl⟩

/-- Inventories of the same shape prepare the same system. -/
private theorem system_eq_of_forall₂ {S T : SourceInventory Q} (h : List.Forall₂ SameShape S T)
    (Z : Q → Type) : S.system Z = T.system Z := by
  induction h with
  | nil => rfl
  | cons hst _ ih =>
    obtain ⟨v, rfl⟩ := hst
    rw [SourceInventory.system_cons, SourceInventory.system_cons, ih]

private theorem heq_addPairMatrix {p q : Q} (hpq : p ≠ q) (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {Y₁ Y₂ Y₁' Y₂' : Q → Type} (h : Y₁ = Y₂)
    (h' : Y₁' = Y₂') (C₁ : ∀ s, Matrix (Y₁' s) (Y₁ s) ℂ) (C₂ : ∀ s, Matrix (Y₂' s) (Y₂ s) ℂ)
    (hC : HEq C₁ C₂) : HEq (addPairMatrix hpq α β C₁) (addPairMatrix hpq α β C₂) := by
  subst h h'
  cases hC
  rfl

/-- Running party operations beside the fresh factors of inventories of the same shape. -/
private theorem heq_liftOps {S T : SourceInventory Q} (h : List.Forall₂ SameShape S T)
    {X₁ X₂ X' : Q → Type} (hX : X₁ = X₂) (A₁ : ∀ q, Matrix (X' q) (X₁ q) ℂ)
    (A₂ : ∀ q, Matrix (X' q) (X₂ q) ℂ) (hA : HEq A₁ A₂) :
    HEq (S.liftOps A₁) (T.liftOps A₂) := by
  subst hX
  cases hA
  induction h with
  | nil => rfl
  | @cons s t S T hst hST ih =>
    obtain ⟨v, rfl⟩ := hst
    exact heq_addPairMatrix s.distinct s.leftBasis s.rightBasis (system_eq_of_forall₂ hST _)
      (system_eq_of_forall₂ hST _) _ _ ih

omit [DecidableEq Q] in
/-- Products read through identifications of equal families agree. -/
private theorem heq_submatrix_mul {Z F₁ F₂ G₁ G₂ H₁ H₂ : Q → Type} [i₁ : ∀ q, Fintype (F₁ q)]
    [i₂ : ∀ q, Fintype (F₂ q)] (hF : F₁ = F₂) (hG : G₁ = G₂) (hH : H₁ = H₂)
    (L₁ : ∀ q, Matrix (Z q) (F₁ q) ℂ) (L₂ : ∀ q, Matrix (Z q) (F₂ q) ℂ)
    (M₁ : ∀ q, Matrix (F₁ q) (G₁ q) ℂ) (M₂ : ∀ q, Matrix (F₂ q) (G₂ q) ℂ)
    (c₁ : ∀ q, H₁ q = G₁ q) (c₂ : ∀ q, H₂ q = G₂ q) (hL : HEq L₁ L₂) (hM : HEq M₁ M₂) :
    HEq (fun q ↦ (L₁ q * M₁ q).submatrix id (Equiv.cast (c₁ q)))
      (fun q ↦ (L₂ q * M₂ q).submatrix id (Equiv.cast (c₂ q))) := by
  subst hF hG hH
  cases hL
  cases hM
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  rfl

/-- Words with the same operations whose sources differ only in their vectors, a vector being
allowed to change only at a source whose endpoints are not related by `R`. -/
private inductive Variant (R : Q → Q → Prop) : {X Y : Q → Type} → Word X Y → Word X Y → Prop
  | refl {X Y : Q → Type} (u : Word X Y) : Variant R u u
  | gate {X Y : Q → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] {D : Finset Q}
      (hY : ∀ s ∉ D, Y s = X s) (g : SourceGate D X Y)
      (v : EuclideanSpace ℂ (g.leftBasis × g.rightBasis)) (hv : R g.left g.right → v = g.vector) :
      Variant R (PartyCircuit.gate D hY g) (PartyCircuit.gate D hY { g with vector := v })
  | comp {X Y Z : Q → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] {u u' : Word X Y}
      {w w' : Word Y Z} :
      Variant R u u' → Variant R w w' →
        Variant R (PartyCircuit.comp u w) (PartyCircuit.comp u' w')

/-- Variants have sources of the same shape. -/
private theorem Variant.forall₂_sources {R : Q → Q → Prop} {X Y : Q → Type} {u u' : Word X Y}
    (h : Variant R u u') : List.Forall₂ SameShape u.sources u'.sources := by
  induction h with
  | refl u => exact List.forall₂_same.mpr fun s _ ↦ sameShape_refl s
  | gate hY g v hv => exact .cons ⟨v, rfl⟩ .nil
  | comp _ _ ihu ihw => exact List.rel_append ihw ihu

/-- **The local part of a word does not read the vectors of its sources.** -/
private theorem Variant.heq_localPartOp {R : Q → Q → Prop} {X Y : Q → Type}
    {u u' : Word X Y} (h : Variant R u u') :
    ∀ [∀ q, DecidableEq (X q)], HEq u.localPartOp u'.localPartOp := by
  induction h with
  | refl u => intro _; rfl
  | gate hY g v hv => intro _; rfl
  | @comp X Y Z _ _ u u' w w' hu hw ihu ihw =>
    intro _
    exact heq_submatrix_mul (system_eq_of_forall₂ hw.forall₂_sources _)
      (by rw [system_eq_of_forall₂ hw.forall₂_sources, system_eq_of_forall₂ hu.forall₂_sources])
      (system_eq_of_forall₂ (List.rel_append hw.forall₂_sources hu.forall₂_sources) _) _ _ _ _
      _ _ ihw (heq_liftOps hw.forall₂_sources (system_eq_of_forall₂ hu.forall₂_sources _) _ _ ihu)

/-- Reading variants on blocks keeps them variants, when merged sources keep their vectors. -/
private theorem Variant.coarsen [Fintype Q] {Q' : Type} [DecidableEq Q'] (f : Q → Q')
    {R : Q → Q → Prop} {R' : Q' → Q' → Prop} (h₁ : ∀ a b, a ≠ b → f a = f b → R a b)
    (h₂ : ∀ a b, R' (f a) (f b) → R a b) {X Y : Q → Type} {u u' : Word X Y}
    (h : Variant R u u') :
    ∀ [∀ q, Fintype (X q)] [∀ q, DecidableEq (X q)],
      Variant R' (Word.coarsen f u) (Word.coarsen f u') := by
  induction h with
  | refl u => intro _ _; exact .refl _
  | gate hY g v hv =>
    intro _ _
    by_cases hf : f g.left = f g.right
    · obtain rfl := hv (h₁ _ _ g.distinct hf)
      exact .refl _
    · change Variant R' (dite _ _ _) (dite _ _ _)
      rw [dite_eq_right hf, dite_eq_right hf]
      exact .gate _ (g.coarse f hf) v fun h ↦ hv (h₂ _ _ h)
  | comp _ _ ihu ihw => intro _ _; exact .comp ihu ihw

/-- Variants beside spectator factors are variants. -/
private theorem Variant.frame (W : Q → Type) [∀ q, Fintype (W q)] [∀ q, DecidableEq (W q)]
    {R : Q → Q → Prop} {X Y : Q → Type} {u u' : Word X Y} (h : Variant R u u') :
    ∀ [∀ q, Fintype (X q)] [∀ q, DecidableEq (X q)],
      Variant R (PartyCircuit.frame W u) (PartyCircuit.frame W u') := by
  induction h with
  | refl u => intro _ _; exact .refl _
  | gate hY g v hv => intro _ _; exact .gate _ (g.frame W) v hv
  | comp _ _ ihu ihw => intro _ _; exact .comp ihu ihw

/-- Variants run on a cell are variants. -/
private theorem Variant.onCell (D : Finset Q) {R : Q → Q → Prop} {X Y : Q → Type}
    [∀ q, Fintype (X q)] [∀ q, DecidableEq (X q)] [∀ q, Fintype (Y q)] [∀ q, DecidableEq (Y q)]
    (hY : ∀ s ∉ D, Y s = X s) {w w' : Word (fun s : ↥D ↦ X s) (fun s : ↥D ↦ Y s)}
    (h : Variant (fun a b ↦ R a.1 b.1) w w') :
    Variant R (Word.onCell D hY w) (Word.onCell D hY w') :=
  .comp (.comp (.refl _) ((h.coarsen Subtype.val (fun _ _ hab h ↦ (hab (Subtype.ext h)).elim)
    fun _ _ h ↦ h).frame _)) (.refl _)

/-- Slot preparations with vectors that differ only at slots whose endpoints are not related are
variants. -/
private theorem Variant.prepareSlots {R : Q → Q → Prop} {Z : Q → Type} [∀ q, Fintype (Z q)]
    [∀ q, DecidableEq (Z q)] : (S : SourceInventory Q) → (B : SourceInventory.SlotBases S.length) →
    (η η' : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) →
    (∀ i, R (S.get i).left (S.get i).right → η' i = η i) →
      Variant R (SourceInventory.prepareSlots S B η Z) (SourceInventory.prepareSlots S B η' Z)
  | [], _, _, _, _ => .refl _
  | _ :: S, B, η, η', h =>
    .comp (Variant.prepareSlots S B.tail (fun i ↦ η i.succ) (fun i ↦ η' i.succ)
      fun i ↦ h i.succ)
      (.gate _ (SourceGate.ofAddPair _ (B.left 0) (B.right 0) (η 0) _) (η' 0) (h 0))

end Variants

/-- A substituted branch is a variant of the branch: only kept vectors change. -/
private theorem variant_partialWithSources : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (η : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)) →
    (∀ e ξ, A (w.endpoints e).1 = false → A (w.endpoints e).2 = false →
      η e ξ = w.sourceVectorAt e ξ) → (ξ : Choices A w) →
      Variant (fun _ _ ↦ False) (partialWord A w ξ) (partialWithSources A w η ξ)
  | _, _, _, _, PartyCircuit.done _, _, _, _ => .refl _
  | _, _, _, _, PartyCircuit.gate D hY g, η, hη, ξ => by
    by_cases h : PreparedGate.IsTouched A D
    · rw [partialWord_gate_of_isTouched A D hY g h,
        show partialWithSources A (PartyCircuit.gate D hY g : SourceCircuit _ _) η ξ = _ from
          dite_eq_left h]
      refine Variant.coarsen (affectedOwner A)
        (R := fun a b ↦ affectedOwner A a = affectedOwner A b) (fun _ _ _ h ↦ h)
        (fun _ _ h ↦ h.elim) ?_
      refine Variant.onCell D hY (.comp (Variant.prepareSlots _ _ _ _ fun i hi ↦ ?_) (.refl _))
      obtain hne | ⟨hl, hr⟩ := (affectedOwner_eq_iff A _ _).mp hi
      · exact ((g.gate.slots.get i).distinct (Subtype.ext hne)).elim
      · exact hη ⟨(), i⟩ _ hl hr
    · rw [partialWithSources_gate_of_not_isTouched A D hY g h]
      exact .refl _
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _, _ => .refl _
  | _, _, _, _, PartyCircuit.localOps _, _, _, _ => .refl _
  | _, _, _, _, PartyCircuit.comp c c', η, hη, ξ =>
    .comp (variant_partialWithSources c _ (fun e ξ ↦ hη ⟨Sum.inl e.1, e.2⟩ ξ) ξ.1)
      (variant_partialWithSources c' _ (fun e ξ ↦ hη ⟨Sum.inr e.1, e.2⟩ ξ) ξ.2)

/-- The operator of a residual: the party operations of the local part read through the
identification of the slot system. -/
private theorem op_residualInSlots {Z : P → Type} [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)]
    {Y' : P → Type} [∀ p, Fintype (Y' p)] [∀ p, DecidableEq (Y' p)] (u : Word Z Y')
    (S : SourceInventory P) (B : SourceInventory.SlotBases S.length)
    (e : ∀ p, SourceInventory.slotSystem S B Z p ≃ u.sources.system Z p) :
    (u.residualInSlots S B e).op = piKronecker fun p ↦ (u.localPartOp p).submatrix id (e p) := by
  rw [Word.residualInSlots, Word.op_comp, Word.op_localPart]
  unfold Word.op
  rw [PartyCircuit.op_relabel, PEquiv.mul_toMatrix_toPEquiv]
  rfl

omit [DecidableEq P] [Fintype P] in
/-- Party operations read through identifications of equal families agree. -/
private theorem submatrix_cast_eq_of_heq {Z Y' F₁ F₂ : P → Type} (hF : F₁ = F₂)
    (L₁ : ∀ q, Matrix (Y' q) (F₁ q) ℂ) (L₂ : ∀ q, Matrix (Y' q) (F₂ q) ℂ) (hL : HEq L₁ L₂)
    (c₁ : ∀ q, Z q = F₁ q) (c₂ : ∀ q, Z q = F₂ q) :
    (fun q ↦ (L₁ q).submatrix id (Equiv.cast (c₁ q))) =
      fun q ↦ (L₂ q).submatrix id (Equiv.cast (c₂ q)) := by
  subst hF
  cases hL
  rfl

/-- **The sources of a substituted branch are the common slots with the substituted vectors at
the chosen labels**; no normalization is needed. Source: Theorem 5.2, `04-compression.tex`,
lines 338–417. -/
theorem ofSlots_partialWithSources (w : SourceCircuit X Y)
    (η : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)) (ξ : Choices A w) :
    SourceInventory.ofSlots (partialSlots A w) (partialSlotBases A w)
        (fun i ↦ η (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i)) =
      (partialWithSources A w η ξ).sources := by
  let v : ∀ e : w.sourceLocations, EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e) :=
    fun e ↦ if h : IsTouched A w e.1 then η e (choiceAt A w ξ e.1 h) else 0
  have hv : (fun i ↦ η (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i)) =
      fun i ↦ v (partialSlotEquiv A w i).1 :=
    funext fun i ↦ by
      simp only [v, dite_eq_left (isTouched_of_source_endpoint A w _ (partialSlotEquiv A w i).2)]
      rfl
  rw [hv, ofSlots_partialSlots, sources_partialWithSources_eq_filterMap]
  refine List.filterMap_congr fun e _ ↦ ?_
  by_cases h : IsTouched A w e.1
  · simp only [v, dite_eq_left h]
  · rw [dite_eq_right h]
    refine dite_eq_left (not_not.mp fun hne ↦ h ?_)
    exact isTouched_of_source_endpoint A w e
      (((pairSourceAt w e (v e)).affectedOwner_ne_iff A).mp hne)

/-- **The residual of a branch evaluates every substitution of its kept vectors**: preparing the
substituted vectors in the common slots and then applying the residual gives the substituted
branch. Only the vectors at positions with two exterior endpoints must be those of the gates.
Source: Theorem 5.2, `04-compression.tex`, lines 409–434. -/
theorem op_partialResidual_mul_prepareSlots_substituted [∀ p, Fintype (Y p)]
    [∀ p, DecidableEq (Y p)] (w : SourceCircuit X Y)
    (η : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e))
    (hη : ∀ e ξ, A (w.endpoints e).1 = false → A (w.endpoints e).2 = false →
      η e ξ = w.sourceVectorAt e ξ) (ξ : Choices A w) :
    (partialResidual A w ξ).op *
        (SourceInventory.prepareSlots (partialSlots A w) (partialSlotBases A w)
          (fun i ↦ η (partialSlotEquiv A w i).1 (partialSlotChoice A w ξ i))
          (blockSystem (affectedOwner A) X)).op =
      Word.op (partialWithSources A w η ξ) := by
  rw [← Word.op_residualInSlots_mul_prepareSlots _ _ _ _ (ofSlots_partialWithSources A w η ξ),
    partialResidual, op_residualInSlots, op_residualInSlots]
  have hv := variant_partialWithSources A w η hη ξ
  congr 2
  exact submatrix_cast_eq_of_heq (system_eq_of_forall₂ hv.forall₂_sources _) _ _
    hv.heq_localPartOp _ _

end SourceCircuit

end QuantumCircuit.Party
