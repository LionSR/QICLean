/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.SelectivePreparation
import QICLean.Circuit.Party.Compression.SourceReplacement.PreparedMatrix

/-!
# Coordinates of a selectively prepared source system

A free-slot configuration consists of one pair of coordinates at each free
slot and a configuration of the original system. In these coordinates
preparing the free slots inserts the tensor product of their vectors.
The slot labels remain those of the original inventory.

Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

open Matrix ManyBody

namespace QuantumCircuit.Party.SourceInventory

variable {P : Type} [DecidableEq P]

/-- The indices selected by a mask. -/
private abbrev FreeIndex {n : ℕ} (f : Fin n → Bool) := {i : Fin n // f i = true}

/-- When the first index is not selected, the selected indices are those of the tail. -/
private def freeIndex_of_head_false {n : ℕ} (f : Fin (n + 1) → Bool) (h : f 0 = false) :
    FreeIndex (fun i ↦ f i.succ) ≃ FreeIndex f where
  toFun i := ⟨i.val.succ, i.property⟩
  invFun i := Fin.cases (motive := fun j ↦ f j = true → FreeIndex (fun i ↦ f i.succ))
    (fun hi ↦ False.elim (Bool.false_ne_true (h.symm.trans hi)))
    (fun j hj ↦ ⟨j, hj⟩) i.val i.property
  left_inv i := by cases i; simp
  right_inv i := by
    obtain ⟨i, hi⟩ := i
    induction i using Fin.cases with
    | zero => exact (Bool.false_ne_true (h.symm.trans hi)).elim
    | succ i => rfl

/-- When the first index is selected, the selected indices are the first one and those of the
tail. -/
private def freeIndex_of_head_true {n : ℕ} (f : Fin (n + 1) → Bool) (h : f 0 = true) :
    Unit ⊕ FreeIndex (fun i ↦ f i.succ) ≃ FreeIndex f where
  toFun := Sum.elim (fun _ ↦ ⟨0, h⟩) (fun i ↦ ⟨i.val.succ, i.property⟩)
  invFun i := Fin.cases (motive := fun j ↦ f j = true → Unit ⊕ FreeIndex (fun i ↦ f i.succ))
    (fun _ ↦ .inl ()) (fun j hj ↦ .inr ⟨j, hj⟩) i.val i.property
  left_inv i := by cases i with | inl a => cases a; rfl | inr a => cases a; rfl
  right_inv i := by
    obtain ⟨i, hi⟩ := i
    induction i using Fin.cases <;> rfl

/-- Coordinates at the selected indices when the first index is not selected. -/
private def freeCoords_of_head_false {n : ℕ} (f : Fin (n + 1) → Bool)
    (A : Fin (n + 1) → Type) (h : f 0 = false) :
    (∀ i : FreeIndex (fun i ↦ f i.succ), A i.val.succ) ≃ (∀ i : FreeIndex f, A i.val) :=
  Equiv.piCongrLeft (fun i : FreeIndex f ↦ A i.val) (freeIndex_of_head_false f h)

/-- Coordinates at the selected indices when the first index is selected: the first coordinate
and those of the tail. -/
private def freeCoords_of_head_true {n : ℕ} (f : Fin (n + 1) → Bool)
    (A : Fin (n + 1) → Type) (h : f 0 = true) :
    (A 0 × (∀ i : FreeIndex (fun i ↦ f i.succ), A i.val.succ)) ≃ (∀ i : FreeIndex f, A i.val) :=
  let e := freeIndex_of_head_true f h
  ((Equiv.funUnique Unit (A 0)).symm.prodCongr (Equiv.refl _)).trans
    ((Equiv.sumPiEquivProdPi (fun i ↦ A (e i).val)).symm.trans
      (Equiv.piCongrLeft (fun i : FreeIndex f ↦ A i.val) e))

/-- Coordinates of a free-slot system, read as a configuration of the free
pair factors and a configuration of the base system. -/
def freeSlotColumnEquiv : (R : SourceInventory P) → (B : SlotBases R.length) →
    (f : Fin R.length → Bool) → (Z : P → Type) →
    Config (freeSlotSystem R B f Z) ≃ (∀ i : {i // f i = true}, B.left i × B.right i) × Config Z
  | [], B, f, Z =>
    have : IsEmpty (FreeIndex f) := ⟨fun u ↦ Fin.elim0 u.val⟩
    (Equiv.uniqueProd (Config Z) (∀ i : FreeIndex f, B.left i × B.right i)).symm
  | r :: R, B, f, Z => by
    let tail := freeSlotColumnEquiv R B.tail (fun i ↦ f i.succ) Z
    cases h : f 0
    · have heq : freeSlotSystem (r :: R) B f Z =
          freeSlotSystem R B.tail (fun i ↦ f i.succ) Z := by
        rw [freeSlotSystem.eq_2,
          show (⟨0, Nat.succ_pos R.length⟩ : Fin (r :: R).length) = 0 from rfl, h]
        rfl
      exact (Equiv.cast (congrArg Config heq)).trans
        (tail.trans ((freeCoords_of_head_false f (fun i ↦ B.left i × B.right i) h).prodCongr
          (Equiv.refl _)))
    · let Y := freeSlotSystem R B.tail (fun i ↦ f i.succ) Z
      have heq : freeSlotSystem (r :: R) B f Z = addPair Y r.distinct (B.left 0) (B.right 0) := by
        rw [freeSlotSystem.eq_2,
          show (⟨0, Nat.succ_pos R.length⟩ : Fin (r :: R).length) = 0 from rfl, h]
        rfl
      exact (Equiv.cast (congrArg Config heq)).trans
        ((addPairConfigEquiv (X := Y) r.distinct (B.left 0) (B.right 0)).trans
          (((Equiv.refl _).prodCongr tail).trans
            ((Equiv.prodAssoc _ _ _).symm.trans
              ((freeCoords_of_head_true f (fun i ↦ B.left i × B.right i) h).prodCongr
                (Equiv.refl _)))))

/-- A product over the selected indices when the first index is not selected is the product over
those of the tail. -/
private theorem prod_freeCoords_of_head_false {n : ℕ} (f : Fin (n + 1) → Bool)
    (A : Fin (n + 1) → Type) (h : f 0 = false)
    (g : ∀ i, A i → ℂ) (x : ∀ i : FreeIndex (fun i ↦ f i.succ), A i.val.succ) :
    (∏ i : FreeIndex f, g i (freeCoords_of_head_false f A h x i)) =
      ∏ i : FreeIndex (fun i ↦ f i.succ), g i.val.succ (x i) := by
  let e := freeIndex_of_head_false f h
  symm
  refine Fintype.prod_equiv e _ _ fun i ↦ ?_
  change g (e i) (x i) = g (e i) (freeCoords_of_head_false f A h x (e i))
  refine congrArg (g (e i)) ?_
  exact (congrFun ((freeCoords_of_head_false f A h).symm_apply_apply x) i).symm

/-- A product over the selected indices when the first index is selected is the first factor times
the product over those of the tail. -/
private theorem prod_freeCoords_of_head_true {n : ℕ} (f : Fin (n + 1) → Bool)
    (A : Fin (n + 1) → Type) (h : f 0 = true)
    (g : ∀ i, A i → ℂ) (y : A 0) (x : ∀ i : FreeIndex (fun i ↦ f i.succ), A i.val.succ) :
    (∏ i : FreeIndex f, g i (freeCoords_of_head_true f A h (y, x) i)) =
      g 0 y * ∏ i : FreeIndex (fun i ↦ f i.succ), g i.val.succ (x i) := by
  let e := freeIndex_of_head_true f h
  let z : ∀ t : Unit ⊕ FreeIndex (fun i ↦ f i.succ), A (e t).val :=
    (Equiv.sumPiEquivProdPi (fun i ↦ A (e i).val)).symm ((fun _ ↦ y), x)
  calc
    (∏ i : FreeIndex f, g i (freeCoords_of_head_true f A h (y, x) i)) =
        ∏ i : Unit ⊕ FreeIndex (fun i ↦ f i.succ), g (e i) (z i) :=
      (Fintype.prod_equiv e _ _ fun i ↦
        congrArg (g (e i)) (congrFun ((Equiv.piCongrLeft
          (fun a : FreeIndex f ↦ A a.val) e).symm_apply_apply z) i).symm).symm
    _ = _ := by
      rw [Fintype.prod_sum_type, Fintype.prod_unique]
      rfl


/-- The free-slot preparation is a product of the vectors at the free slots. -/
theorem op_prepareFreeSlots [Fintype P] (R : SourceInventory P) (B : SlotBases R.length)
    (f : Fin R.length → Bool) (ζ : ∀ i, EuclideanSpace ℂ (B.left i × B.right i))
    (Z : P → Type) [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] :
    (prepareFreeSlots R B f ζ Z).op =
      prepMatrix (freeSlotColumnEquiv R B f Z)
        (WithLp.toLp 2 (productVector fun i : {i // f i = true} ↦ ζ i.val)) := by
  induction R with
  | nil =>
    change PartyCircuit.op SourceGate.ev (PartyCircuit.done Z) = _
    rw [PartyCircuit.op_done]
    ext y x
    erw [prepMatrix_apply]
    simp only [freeSlotColumnEquiv, Matrix.one_apply]
    rfl
  | cons r R ih =>
    obtain ⟨b, f', rfl⟩ : ∃ b f', f = Fin.cons b f' :=
      ⟨f 0, Fin.tail f, (Fin.cons_self_tail f).symm⟩
    cases b
    · ext y x
      have hi := congrFun (congrFun (ih B.tail f' (fun i ↦ ζ i.succ)) y) x
      refine hi.trans ?_
      erw [prepMatrix_apply, prepMatrix_apply]
      apply if_congr Iff.rfl ?_ rfl
      change (∏ i : FreeIndex f', ζ i.val.succ ((freeSlotColumnEquiv R B.tail f' Z y).1 i)) = _
      symm
      apply prod_freeCoords_of_head_false (Fin.cons false f') (fun i ↦ B.left i × B.right i)
        (Fin.cons_zero _ _) (fun i z ↦ ζ i z)
    · ext y x
      erw [Word.op_comp, Word.op_sourceAt]
      change (prepMatrix (addPairConfigEquiv
        (X := freeSlotSystem R B.tail f' Z) r.distinct (B.left 0) (B.right 0)) (ζ 0) *
        (prepareFreeSlots R B.tail f' (fun i ↦ ζ i.succ) Z).op) y x = _
      rw [ih B.tail f' (fun i ↦ ζ i.succ)]
      refine (prepMatrix_mul_apply _ _ _ y x).trans ?_
      simp only [prepMatrix_apply, mul_ite, mul_zero]
      apply if_congr Iff.rfl ?_ rfl
      symm
      apply prod_freeCoords_of_head_true (Fin.cons true f') (fun i ↦ B.left i × B.right i)
        (Fin.cons_zero _ _) (fun i z ↦ ζ i z)


/-- The basis at a party, read as the free factors at that party and its
original basis. For a slot without an endpoint at the party, its factor is
the one-element basis. -/
def freeSlotSiteEquiv : (R : SourceInventory P) → (B : SlotBases R.length) →
    (f : Fin R.length → Bool) → (Z : P → Type) → (p : P) →
    freeSlotSystem R B f Z p ≃
      (∀ i : {i // f i = true}, pairFactor (R.get i).distinct (B.left i) (B.right i) p) × Z p
  | [], B, f, Z, p =>
    have : IsEmpty (FreeIndex f) := ⟨fun u ↦ Fin.elim0 u.val⟩
    (Equiv.uniqueProd (Z p)
      (∀ i : FreeIndex f, pairFactor (([] : SourceInventory P).get i).distinct
        (B.left i) (B.right i) p)).symm
  | r :: R, B, f, Z, p => by
    let tail := freeSlotSiteEquiv R B.tail (fun i ↦ f i.succ) Z p
    let A := fun i : Fin (r :: R).length ↦
      pairFactor ((r :: R).get i).distinct (B.left i) (B.right i) p
    cases h : f 0
    · have heq : freeSlotSystem (r :: R) B f Z =
          freeSlotSystem R B.tail (fun i ↦ f i.succ) Z := by
        rw [freeSlotSystem.eq_2,
          show (⟨0, Nat.succ_pos R.length⟩ : Fin (r :: R).length) = 0 from rfl, h]
        rfl
      exact (Equiv.cast (congrFun heq p)).trans
        (tail.trans ((freeCoords_of_head_false f A h).prodCongr (Equiv.refl _)))
    · let Z' := freeSlotSystem R B.tail (fun i ↦ f i.succ) Z
      have heq : freeSlotSystem (r :: R) B f Z = addPair Z' r.distinct (B.left 0) (B.right 0) := by
        rw [freeSlotSystem.eq_2,
          show (⟨0, Nat.succ_pos R.length⟩ : Fin (r :: R).length) = 0 from rfl, h]
        rfl
      exact (Equiv.cast (congrFun heq p)).trans
        ((addPairSiteEquiv r.distinct (B.left 0) (B.right 0) Z' p).trans
          (((Equiv.refl _).prodCongr tail).trans
            ((Equiv.prodAssoc _ _ _).symm.trans
              ((freeCoords_of_head_true f A h).prodCongr (Equiv.refl _)))))

/-- The local coordinate identifications of the free factors agree with the
global slot coordinate identification. -/
theorem freeSlotColumnEquiv_eq_siteEquiv (R : SourceInventory P) (B : SlotBases R.length)
    (f : Fin R.length → Bool) (Z : P → Type) (y : Config (freeSlotSystem R B f Z)) :
    freeSlotColumnEquiv R B f Z y =
      ((fun i : FreeIndex f ↦ pairFactorConfigEquiv (R.get i).distinct (B.left i) (B.right i)
        (fun p ↦ (freeSlotSiteEquiv R B f Z p (y p)).1 i)),
        fun p ↦ (freeSlotSiteEquiv R B f Z p (y p)).2) := by
  induction R with
  | nil => exact Prod.ext (funext fun i ↦ Fin.elim0 i.val) rfl
  | cons r R ih =>
    obtain ⟨b, f', rfl⟩ : ∃ b f', f = Fin.cons b f' :=
      ⟨f 0, Fin.tail f, (Fin.cons_self_tail f).symm⟩
    cases b
    · have ht := ih B.tail f' y
      refine Prod.ext (funext fun i ↦ ?_) ?_
      · obtain ⟨j, rfl⟩ := (freeIndex_of_head_false (Fin.cons false f') rfl).surjective i
        change freeCoords_of_head_false (Fin.cons false f')
          (fun i ↦ B.left i × B.right i) rfl (freeSlotColumnEquiv R B.tail f' Z y).1
          (freeIndex_of_head_false (Fin.cons false f') rfl j) =
          pairFactorConfigEquiv (R.get j).distinct (B.left j.val.succ) (B.right j.val.succ)
            (fun p ↦ freeCoords_of_head_false (Fin.cons false f')
              (fun i ↦ pairFactor ((r :: R).get i).distinct (B.left i) (B.right i) p) rfl
              (freeSlotSiteEquiv R B.tail f' Z p (y p)).1
              (freeIndex_of_head_false (Fin.cons false f') rfl j))
        exact congrFun (congrArg Prod.fst ht) j
      · change (freeSlotColumnEquiv R B.tail f' Z y).2 =
          fun p ↦ (freeSlotSiteEquiv R B.tail f' Z p (y p)).2
        exact congrArg Prod.snd ht
    · let W := freeSlotSystem R B.tail f' Z
      let e := addPairConfigEquiv (X := W) r.distinct (B.left 0) (B.right 0)
      let ep := addPairSiteEquiv r.distinct (B.left 0) (B.right 0) W
      have he : e y =
          (pairFactorConfigEquiv r.distinct (B.left 0) (B.right 0) (fun p ↦ (ep p (y p)).1),
            fun p ↦ (ep p (y p)).2) :=
        DFunLike.congr_fun
          (addPairConfigEquiv_eq_siteEquiv r.distinct (B.left 0) (B.right 0) W) y
      let z : Config W := fun p ↦ (ep p (y p)).2
      have ht := ih B.tail f' z
      have hz : (e y).2 = z := congrArg Prod.snd he
      refine Prod.ext (funext fun i ↦ ?_) ?_
      · obtain ⟨j, rfl⟩ := (freeIndex_of_head_true (Fin.cons true f') rfl).surjective i
        rcases j with (⟨⟩ | j)
        · change freeCoords_of_head_true (Fin.cons true f') (fun i ↦ B.left i × B.right i)
            rfl ((e y).1, (freeSlotColumnEquiv R B.tail f' Z (e y).2).1)
            (freeIndex_of_head_true (Fin.cons true f') rfl (.inl ())) =
            pairFactorConfigEquiv r.distinct (B.left 0) (B.right 0)
              (fun p ↦ freeCoords_of_head_true (Fin.cons true f')
                (fun i ↦ pairFactor ((r :: R).get i).distinct (B.left i) (B.right i) p) rfl
                ((ep p (y p)).1, (freeSlotSiteEquiv R B.tail f' Z p (z p)).1)
                (freeIndex_of_head_true (Fin.cons true f') rfl (.inl ())))
          exact congrArg Prod.fst he
        · change freeCoords_of_head_true (Fin.cons true f') (fun i ↦ B.left i × B.right i)
            rfl ((e y).1, (freeSlotColumnEquiv R B.tail f' Z (e y).2).1)
            (freeIndex_of_head_true (Fin.cons true f') rfl (.inr j)) =
            pairFactorConfigEquiv (R.get j).distinct (B.left j.val.succ) (B.right j.val.succ)
              (fun p ↦ freeCoords_of_head_true (Fin.cons true f')
                (fun i ↦ pairFactor ((r :: R).get i).distinct (B.left i) (B.right i) p) rfl
                ((ep p (y p)).1, (freeSlotSiteEquiv R B.tail f' Z p (z p)).1)
                (freeIndex_of_head_true (Fin.cons true f') rfl (.inr j)))
          simp only [hz]
          exact congrFun (congrArg Prod.fst ht) j
      · change (freeSlotColumnEquiv R B.tail f' Z (e y).2).2 = _
        rw [hz]
        exact congrArg Prod.snd ht

end QuantumCircuit.Party.SourceInventory
