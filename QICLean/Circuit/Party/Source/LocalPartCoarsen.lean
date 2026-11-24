/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.LocalPart

/-!
# The local part of a coarsened word at a one-party block

Along a map of parties `f : P → Q`, let the block `b` consist of the single party `p`
(`hf : ∀ r, f r = b ↔ r = p`). The configurations of that block are those of `p`
(`ManyBody.blockFiberEquiv`). The sources of the word read on the blocks (`Word.coarsen f w`) that
meet `b` are exactly the sources of `w` that meet `p`, with the same fresh factors; a source inside
another block becomes a local operation there. Hence the system prepared at `b` by the sources
of the coarse word is the system prepared at `p` by the sources of the word
(`Word.coarsenFiberEquiv`, by recursion on the word), and the local part of the coarse word at
`b` is the local part of the word at `p` read through these identifications
(`Word.localPartOp_coarsen_of_fiber`).

The proof runs party operations beside the fresh factors of the sources
(`Word.liftOps_coarsen_of_fiber`). At a pair source, the coarse word equals the chosen case of
`Word.coarsen` by a proved, not a definitional, equality of words; this equality enters only
through the identification of the systems prepared by the sources of the two equal words.

## Main definitions

* `QuantumCircuit.Party.addPairFiberEquiv` — the basis of `addPair` at a one-party block.
* `QuantumCircuit.Party.Word.coarsenFiberEquiv` — the system prepared at a one-party block.

## Main results

* `QuantumCircuit.Party.Word.localPartOp_coarsen_of_fiber`.
* `QuantumCircuit.Party.pairFactor_fiber`, `QuantumCircuit.Party.ne_of_fiber_of_eq` — a pair
  source seen from a one-party block.
* `QuantumCircuit.Party.Word.liftOps_coarsen_of_fiber`,
  `QuantumCircuit.Party.Word.coarsenFiberEquiv_gate_of_eq`,
  `QuantumCircuit.Party.Word.coarsenFiberEquiv_gate_of_ne`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 245–251 (the local part of a word) and 357–361 (the affected parties and the exterior).
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party

variable {P Q : Type} [DecidableEq P] [DecidableEq Q]

section addPair

variable {l r : P} (hlr : l ≠ r) (α β : Type)

/-- Away from the two parties of a pair, party operations run beside its fresh factors are the
operations read through the identification of the equal bases. -/
private theorem addPairMatrix_of_ne [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {Y Y' : P → Type} (C : ∀ s, Matrix (Y' s) (Y s) ℂ) {s : P}
    (hl : s ≠ l) (hr : s ≠ r) :
    addPairMatrix hlr α β C s = (C s).submatrix (Equiv.cast (addPair_of_ne hlr α β hl hr))
      (Equiv.cast (addPair_of_ne hlr α β hl hr)) := by
  ext y x
  simp [addPairMatrix, addPairSiteEquiv, hl, hr, kroneckerMap_apply]

/-- Party operations run beside the fresh factors of two pairs, at two parties whose fresh
factors and old bases are identified, are read through the identification. -/
private theorem addPairMatrix_submatrix_prodCongr [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] {P' : Type} [DecidableEq P'] {l' r' : P'}
    (hlr' : l' ≠ r') {Z₁ Z₂ : P → Type} {Z₁' Z₂' : P' → Type} (A : ∀ q, Matrix (Z₁' q) (Z₂' q) ℂ)
    (B : ∀ s, Matrix (Z₁ s) (Z₂ s) ℂ) {s : P} {s' : P'}
    (φ : pairFactor hlr' α β s' ≃ pairFactor hlr α β s) (e₁ : Z₁' s' ≃ Z₁ s)
    (e₂ : Z₂' s' ≃ Z₂ s) (hAB : A s' = (B s).submatrix e₁ e₂) :
    addPairMatrix hlr' α β A s' = (addPairMatrix hlr α β B s).submatrix
      ((addPairSiteEquiv hlr' α β Z₁' s').trans
        ((φ.prodCongr e₁).trans (addPairSiteEquiv hlr α β Z₁ s).symm))
      ((addPairSiteEquiv hlr' α β Z₂' s').trans
        ((φ.prodCongr e₂).trans (addPairSiteEquiv hlr α β Z₂ s).symm)) := by
  ext y x
  simp only [addPairMatrix, reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.apply_symm_apply, hAB, one_apply,
    φ.apply_eq_iff_eq]

/-- `addPairSiteEquiv` at the first party, through `addPairLeft`. -/
private theorem addPairSiteEquiv_apply_left {Z : P → Type} (z : addPair Z hlr α β l) :
    addPairSiteEquiv hlr α β Z l z =
      (cast (by simp [pairFactor]) (addPairLeft hlr α β z).1, (addPairLeft hlr α β z).2) := by
  simp [addPairSiteEquiv, addPairLeft]
  rfl

/-- The inverse of `addPairSiteEquiv` at the first party, through `addPairLeft`. -/
private theorem addPairSiteEquiv_symm_apply_left {Z : P → Type} (a : pairFactor hlr α β l)
    (x : Z l) : (addPairSiteEquiv hlr α β Z l).symm (a, x) =
      (addPairLeft hlr α β).symm (cast (by simp [pairFactor]) a, x) := by
  rw [Equiv.symm_apply_eq, addPairSiteEquiv_apply_left, Equiv.apply_symm_apply]
  simp

/-- `addPairSiteEquiv` at the second party, through `addPairRight`. -/
private theorem addPairSiteEquiv_apply_right {Z : P → Type} (z : addPair Z hlr α β r) :
    addPairSiteEquiv hlr α β Z r z =
      (cast (by simp [pairFactor, hlr.symm]) (addPairRight hlr α β z).1,
        (addPairRight hlr α β z).2) := by
  simp [addPairSiteEquiv, addPairRight, hlr.symm]
  rfl

/-- The inverse of `addPairSiteEquiv` at the second party, through `addPairRight`. -/
private theorem addPairSiteEquiv_symm_apply_right {Z : P → Type} (a : pairFactor hlr α β r)
    (x : Z r) : (addPairSiteEquiv hlr α β Z r).symm (a, x) =
      (addPairRight hlr α β).symm (cast (by simp [pairFactor, hlr.symm]) a, x) := by
  rw [Equiv.symm_apply_eq, addPairSiteEquiv_apply_right, Equiv.apply_symm_apply]
  simp

/-- `addPairSiteEquiv` away from the two parties: the old part is the identification. -/
private theorem addPairSiteEquiv_apply_snd_of_ne {Z : P → Type} {s : P} (hl : s ≠ l)
    (hr : s ≠ r) (z : addPair Z hlr α β s) :
    (addPairSiteEquiv hlr α β Z s z).2 = cast (addPair_of_ne hlr α β hl hr) z := by
  simp [addPairSiteEquiv, hl, hr]

/-- The inverse of `addPairSiteEquiv` away from the two parties. -/
private theorem addPairSiteEquiv_symm_apply_of_ne {Z : P → Type} {s : P} (hl : s ≠ l)
    (hr : s ≠ r) (a : pairFactor hlr α β s) (x : Z s) :
    (addPairSiteEquiv hlr α β Z s).symm (a, x) = cast (addPair_of_ne hlr α β hl hr).symm x := by
  rw [Equiv.symm_apply_eq, Prod.ext_iff, addPairSiteEquiv_apply_snd_of_ne hlr α β hl hr]
  refine ⟨?_, by simp⟩
  have : Subsingleton (pairFactor hlr α β s) := by
    rw [show pairFactor hlr α β s = Unit by simp [pairFactor, hl, hr]]
    infer_instance
  exact Subsingleton.elim _ _

end addPair

section Fiber

variable (f : P → Q) {b : Q} {p : P} (hf : ∀ r, f r = b ↔ r = p)
include hf

/-- The fresh factors of a pair joining two blocks, at the block that is the single party `p`,
are the fresh factors of the pair at `p`. -/
theorem pairFactor_fiber {l r : P} (hlr : l ≠ r) (h : f l ≠ f r) (α β : Type) :
    pairFactor h α β b = pairFactor hlr α β p := by
  by_cases hl : p = l
  · subst hl
    obtain rfl : b = f p := ((hf p).mpr rfl).symm
    simp [pairFactor]
  · by_cases hr : p = r
    · subst hr
      obtain rfl : b = f p := ((hf p).mpr rfl).symm
      simp [pairFactor, h.symm, hl]
    · have h₁ : b ≠ f l := fun e ↦ hl ((hf l).mp e.symm).symm
      have h₂ : b ≠ f r := fun e ↦ hr ((hf r).mp e.symm).symm
      simp [pairFactor, hl, hr, h₁, h₂]

/-- The basis of `addPair` at the block that is the single party `p`, for a pair joining two
blocks, is the basis of `addPair` at `p`, read along an identification `e` of the old bases. -/
def addPairFiberEquiv {l r : P} (hlr : l ≠ r) (h : f l ≠ f r) (α β : Type) {Z : P → Type}
    {Z' : Q → Type} (e : Z' b ≃ Z p) : addPair Z' h α β b ≃ addPair Z hlr α β p :=
  (addPairSiteEquiv h α β Z' b).trans
    (((Equiv.cast (pairFactor_fiber f hf hlr h α β)).prodCongr e).trans
      (addPairSiteEquiv hlr α β Z p).symm)

omit hf in
/-- `addPairFiberEquiv` at the first party, through `addPairLeft`. -/
private theorem addPairFiberEquiv_apply_left {l r : P} (hlr : l ≠ r) (h : f l ≠ f r)
    (hf : ∀ s, f s = f l ↔ s = l) (α β : Type) {Z : P → Type} {Z' : Q → Type}
    (e : Z' (f l) ≃ Z l) (z : addPair Z' h α β (f l)) :
    addPairFiberEquiv f hf hlr h α β e z =
      (addPairLeft hlr α β).symm ((addPairLeft h α β z).1, e (addPairLeft h α β z).2) := by
  rw [addPairFiberEquiv, Equiv.trans_apply, Equiv.trans_apply, addPairSiteEquiv_apply_left,
    Equiv.prodCongr_apply, Prod.map, addPairSiteEquiv_symm_apply_left, Equiv.cast_apply, cast_cast,
    cast_cast, cast_eq]

omit hf in
/-- `addPairFiberEquiv` at the second party, through `addPairRight`. -/
private theorem addPairFiberEquiv_apply_right {l r : P} (hlr : l ≠ r) (h : f l ≠ f r)
    (hf : ∀ s, f s = f r ↔ s = r) (α β : Type) {Z : P → Type} {Z' : Q → Type}
    (e : Z' (f r) ≃ Z r) (z : addPair Z' h α β (f r)) :
    addPairFiberEquiv f hf hlr h α β e z =
      (addPairRight hlr α β).symm ((addPairRight h α β z).1, e (addPairRight h α β z).2) := by
  rw [addPairFiberEquiv, Equiv.trans_apply, Equiv.trans_apply, addPairSiteEquiv_apply_right,
    Equiv.prodCongr_apply, Prod.map, addPairSiteEquiv_symm_apply_right, Equiv.cast_apply,
    cast_cast, cast_cast, cast_eq]

/-- `addPairFiberEquiv` away from the pair. -/
private theorem addPairFiberEquiv_apply_of_ne {l r : P} (hlr : l ≠ r) (h : f l ≠ f r)
    (α β : Type) {Z : P → Type} {Z' : Q → Type} (e : Z' b ≃ Z p) (hbl : b ≠ f l)
    (hbr : b ≠ f r) (hpl : p ≠ l) (hpr : p ≠ r) (z : addPair Z' h α β b) :
    addPairFiberEquiv f hf hlr h α β e z =
      cast (addPair_of_ne hlr α β hpl hpr).symm (e (cast (addPair_of_ne h α β hbl hbr) z)) := by
  rw [addPairFiberEquiv, Equiv.trans_apply, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    addPairSiteEquiv_symm_apply_of_ne _ _ _ hpl hpr, addPairSiteEquiv_apply_snd_of_ne _ _ _ hbl hbr]

omit [DecidableEq P] [DecidableEq Q] in
/-- A pair inside one block avoids the party whose block is a single party. -/
theorem ne_of_fiber_of_eq {l r : P} (hlr : l ≠ r) (h : f l = f r) : p ≠ l ∧ p ≠ r := by
  refine ⟨fun e ↦ ?_, fun e ↦ ?_⟩
  · subst e
    exact hlr ((hf r).mp (h.symm.trans ((hf p).mpr rfl))).symm
  · subst e
    exact hlr ((hf l).mp (h.trans ((hf p).mpr rfl)))

end Fiber

namespace Word

variable [Fintype P] (f : P → Q) {b : Q} {p : P} (hf : ∀ r, f r = b ↔ r = p)
include hf

/-- The system prepared at the block `b` by the sources of a word read on the blocks of `f` is
the system prepared at `p` by the sources of the word, when the block `b` is the single party
`p`; by recursion on the word, `e` identifying the bases on which the sources are prepared. -/
def coarsenFiberEquiv : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (w : Word X Y) → {Z : P → Type} → {Z' : Q → Type} → (Z' b ≃ Z p) →
      SourceInventory.system (Word.sources (coarsen f w)) Z' b ≃
        SourceInventory.system (Word.sources w) Z p
  | _, _, _, _, .done _, _, _, e => e
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, _, Z', e =>
    if h : f g.left = f g.right then
      (Equiv.cast (congrArg (fun w ↦ SourceInventory.system (Word.sources w) Z' b)
        (dite_eq_left h : coarsen f (PartyCircuit.gate D hY g) = _))).trans
        (e.trans (Equiv.cast (addPair_of_ne g.distinct g.leftBasis g.rightBasis
          (ne_of_fiber_of_eq f hf g.distinct h).1 (ne_of_fiber_of_eq f hf g.distinct h).2).symm))
    else
      (Equiv.cast (congrArg (fun w ↦ SourceInventory.system (Word.sources w) Z' b)
        (dite_eq_right h : coarsen f (PartyCircuit.gate D hY g) = _))).trans
        (addPairFiberEquiv f hf g.distinct h g.leftBasis g.rightBasis e)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, _, e => e
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, _, e => e
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', Z, Z', e =>
    (Equiv.cast (congrFun (SourceInventory.system_append (Word.sources (coarsen f c'))
      (Word.sources (coarsen f c)) Z') b)).trans
      ((coarsenFiberEquiv c' (coarsenFiberEquiv c e)).trans
        (Equiv.cast (congrFun (SourceInventory.system_append (Word.sources c') (Word.sources c)
          Z) p)).symm)

/-- `coarsenFiberEquiv` at a pair inside one block. -/
theorem coarsenFiberEquiv_gate_of_eq {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] {D : Finset P}
    (hY : ∀ s ∉ D, Y s = X s) (g : SourceGate D X Y) {Z : P → Type} {Z' : Q → Type}
    (e : Z' b ≃ Z p) (h : f g.left = f g.right) :
    coarsenFiberEquiv f hf (PartyCircuit.gate D hY g) e =
      (Equiv.cast (congrArg (fun w ↦ SourceInventory.system (Word.sources w) Z' b)
        (dite_eq_left h : coarsen f (PartyCircuit.gate D hY g) = _))).trans
        (e.trans (Equiv.cast (addPair_of_ne g.distinct g.leftBasis g.rightBasis
          (ne_of_fiber_of_eq f hf g.distinct h).1
          (ne_of_fiber_of_eq f hf g.distinct h).2).symm)) := by
  rw [coarsenFiberEquiv]
  exact dite_eq_left h

/-- `coarsenFiberEquiv` at a pair joining two blocks. -/
theorem coarsenFiberEquiv_gate_of_ne {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] {D : Finset P}
    (hY : ∀ s ∉ D, Y s = X s) (g : SourceGate D X Y) {Z : P → Type} {Z' : Q → Type}
    (e : Z' b ≃ Z p) (h : f g.left ≠ f g.right) :
    coarsenFiberEquiv f hf (PartyCircuit.gate D hY g) e =
      (Equiv.cast (congrArg (fun w ↦ SourceInventory.system (Word.sources w) Z' b)
        (dite_eq_right h : coarsen f (PartyCircuit.gate D hY g) = _))).trans
        (addPairFiberEquiv f hf g.distinct h g.leftBasis g.rightBasis e) := by
  rw [coarsenFiberEquiv]
  exact dite_eq_right h

omit [DecidableEq P] [Fintype P] hf in
/-- Party operations run beside the fresh factors of the sources of a word equal to another
are those run beside the sources of the other, read through the identification. -/
private theorem liftOps_transport {X' Y' : Q → Type} {cw cw' : Word X' Y'} (hw : cw = cw')
    {Z₁ Z₂ : Q → Type} (A : ∀ q, Matrix (Z₁ q) (Z₂ q) ℂ) {U₁ U₂ : Type} (M : Matrix U₁ U₂ ℂ)
    (E₁ : SourceInventory.system (Word.sources cw') Z₁ b ≃ U₁)
    (E₂ : SourceInventory.system (Word.sources cw') Z₂ b ≃ U₂)
    (h : SourceInventory.liftOps (Word.sources cw') A b = M.submatrix E₁ E₂) :
    SourceInventory.liftOps (Word.sources cw) A b = M.submatrix
      ((Equiv.cast (congrArg (fun w ↦ SourceInventory.system (Word.sources w) Z₁ b) hw)).trans E₁)
      ((Equiv.cast (congrArg (fun w ↦ SourceInventory.system (Word.sources w) Z₂ b) hw)).trans
        E₂) := by
  subst hw
  exact h

/-- **Party operations beside the fresh factors of a coarsened word, at a one-party block**:
those beside the fresh factors of the word at the party, read through `coarsenFiberEquiv`. -/
theorem liftOps_coarsen_of_fiber : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → {Z₁ Z₂ : P → Type} → {Z₁' Z₂' : Q → Type} →
    (e₁ : Z₁' b ≃ Z₁ p) → (e₂ : Z₂' b ≃ Z₂ p) → (A : ∀ q, Matrix (Z₁' q) (Z₂' q) ℂ) →
    (B : ∀ s, Matrix (Z₁ s) (Z₂ s) ℂ) → A b = (B p).submatrix e₁ e₂ →
      SourceInventory.liftOps (Word.sources (coarsen f w)) A b =
        (SourceInventory.liftOps (Word.sources w) B p).submatrix (coarsenFiberEquiv f hf w e₁)
          (coarsenFiberEquiv f hf w e₂)
  | _, _, _, _, .done _, _, _, _, _, _, _, _, _, hAB => hAB
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, _, _, _, _, e₁, e₂, A, B, hAB => by
    by_cases h : f g.left = f g.right
    · rw [coarsenFiberEquiv_gate_of_eq f hf hY g e₁ h,
        coarsenFiberEquiv_gate_of_eq f hf hY g e₂ h]
      refine liftOps_transport (dite_eq_left h) A _ _ _ ?_
      change A b = (addPairMatrix g.distinct g.leftBasis g.rightBasis B p).submatrix _ _
      rw [addPairMatrix_of_ne _ _ _ _ (ne_of_fiber_of_eq f hf g.distinct h).1
        (ne_of_fiber_of_eq f hf g.distinct h).2, hAB]
      ext y x
      change B p (e₁ y) (e₂ x) = B p (cast _ (cast _ (e₁ y))) (cast _ (cast _ (e₂ x)))
      rw [cast_cast, cast_eq, cast_cast, cast_eq]
    · rw [coarsenFiberEquiv_gate_of_ne f hf hY g e₁ h,
        coarsenFiberEquiv_gate_of_ne f hf hY g e₂ h]
      refine liftOps_transport (dite_eq_right h) A _ _ _ ?_
      exact addPairMatrix_submatrix_prodCongr g.distinct g.leftBasis g.rightBasis h A B _ e₁ e₂
        hAB
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, _, _, _, _, _, _, _, hAB => hAB
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, _, _, _, _, _, _, _, hAB => hAB
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', _, _, _, _, e₁, e₂, A, B, hAB => by
    change SourceInventory.liftOps (Word.sources (coarsen f c') ++ Word.sources (coarsen f c))
      A b = _
    rw [SourceInventory.liftOps_append, liftOps_coarsen_of_fiber c' (coarsenFiberEquiv f hf c e₁)
      (coarsenFiberEquiv f hf c e₂) _ _ (liftOps_coarsen_of_fiber c e₁ e₂ A B hAB)]
    change _ = (SourceInventory.liftOps (Word.sources c' ++ Word.sources c) B p).submatrix
      ((Equiv.cast (congrFun (SourceInventory.system_append (Word.sources (coarsen f c'))
        (Word.sources (coarsen f c)) _) b)).trans ((coarsenFiberEquiv f hf c'
          (coarsenFiberEquiv f hf c e₁)).trans (Equiv.cast (congrFun
            (SourceInventory.system_append (Word.sources c') (Word.sources c) _) p)).symm))
      ((Equiv.cast (congrFun (SourceInventory.system_append (Word.sources (coarsen f c'))
        (Word.sources (coarsen f c)) _) b)).trans ((coarsenFiberEquiv f hf c'
          (coarsenFiberEquiv f hf c e₂)).trans (Equiv.cast (congrFun
            (SourceInventory.system_append (Word.sources c') (Word.sources c) _) p)).symm))
    rw [SourceInventory.liftOps_append]
    ext y x
    simp only [submatrix_apply, Equiv.trans_apply, Equiv.cast_apply, ← Equiv.cast_symm,
      cast_cast, cast_eq]

omit [DecidableEq P] [Fintype P] hf in
/-- The local part of a word equal to another is the local part of the other, read through the
identification of the systems prepared by their sources. -/
private theorem localPartOp_transport {X' Y' : Q → Type} [∀ q, DecidableEq (X' q)]
    {cw cw' : Word X' Y'} (hw : cw = cw') {R U : Type} (M : Matrix R U ℂ) (r : Y' b → R)
    (E : SourceInventory.system (Word.sources cw') X' b ≃ U)
    (h : localPartOp cw' b = M.submatrix r E) :
    localPartOp cw b = M.submatrix r
      ((Equiv.cast (congrArg (fun w ↦ SourceInventory.system (Word.sources w) X' b) hw)).trans
        E) := by
  subst hw
  exact h

omit [DecidableEq P] [Fintype P] [DecidableEq Q] hf in
/-- A permutation matrix equals another one with rows and columns read through equivalences
when the equivalences intertwine. -/
private theorem toMatrix_eq_submatrix_of_apply {A B C D : Type} [DecidableEq B] [DecidableEq D]
    {e : C ≃ D} {g : A ≃ B} {r : C ≃ A} {c : D ≃ B} (H : ∀ y, c (e y) = g (r y)) :
    e.toPEquiv.toMatrix = (g.toPEquiv.toMatrix : Matrix A B ℂ).submatrix r c := by
  rw [toMatrix_toPEquiv_submatrix]
  exact congrArg (fun e ↦ (Equiv.toPEquiv e).toMatrix)
    (Equiv.ext fun y ↦ (Equiv.eq_symm_apply c).mpr (H y))

/-- **The local part of a coarsened word at a block that is a single party `p`** is the local
part of the word at `p`, its output read through the value at `p` and its input through the
identification `coarsenFiberEquiv` of the prepared systems. -/
theorem localPartOp_coarsen_of_fiber : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) →
      localPartOp (coarsen f w) b = (w.localPartOp p).submatrix (blockFiberEquiv f hf Y)
        (coarsenFiberEquiv f hf w (blockFiberEquiv f hf X))
  | _, _, _, _, .done X => (submatrix_one_equiv (blockFiberEquiv f hf X)).symm
  | X, Y, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g => by
    by_cases h : f g.left = f g.right
    · rw [coarsenFiberEquiv_gate_of_eq f hf hY g _ h]
      refine localPartOp_transport (dite_eq_left h) _ _ _ ?_
      obtain ⟨hpl, hpr⟩ := ne_of_fiber_of_eq f hf g.distinct h
      have hb : b ≠ f g.left := fun e ↦ hpl ((hf g.left).mp e.symm).symm
      have hpD : p ∉ D := by rw [g.cell_eq]; simp [hpl, hpr]
      have hAB : (fun v : {v // v ∈ blockPreimage f {b}} ↦ Y v.1) = fun v ↦ X v.1 :=
        funext fun v ↦ hY v.1 (by rw [eq_of_mem_blockPreimage_of_fiber f hf v.2]; exact hpD)
      rw [localPartOp_localOp, PartyCircuit.localOpFamily_of_ne _ _ _ hb, localPartOp_gate]
      refine toMatrix_eq_submatrix_of_apply fun y ↦ ?_
      change cast (addPair_of_ne g.distinct g.leftBasis g.rightBasis hpl hpr).symm
        ((cast _ y : blockSystem f X b) ⟨p, mem_blockPreimage_of_fiber f hf⟩) =
          g.toAddPair p (y ⟨p, mem_blockPreimage_of_fiber f hf⟩)
      rw [g.toAddPair_of_notMem hpD, cast_pi_apply hAB]
    · rw [coarsenFiberEquiv_gate_of_ne f hf hY g _ h]
      refine localPartOp_transport (dite_eq_right h) _ _ _ ?_
      rw [localPartOp_gate, localPartOp_gate]
      refine toMatrix_eq_submatrix_of_apply fun y ↦ ?_
      have hL := (g.coarse f h).addPairLeft_toAddPair
      have hR := (g.coarse f h).addPairRight_toAddPair
      have hO := @SourceGate.toAddPair_of_notMem _ _ _ _ _ (g.coarse f h)
      dsimp only [SourceGate.coarse] at hL hR hO ⊢
      simp only [addPairFiberEquiv, blockFiberEquiv_apply]
      by_cases hl : p = g.left
      · subst hl
        obtain rfl : b = f g.left := ((hf g.left).mpr rfl).symm
        refine (addPairFiberEquiv_apply_left f g.distinct h hf _ _ _ _).trans ?_
        erw [hL y]
        refine Eq.trans ?_ ((Equiv.eq_symm_apply _).mpr (g.addPairLeft_toAddPair _)).symm
        exact congrArg _ (Prod.ext rfl (freshBlockEquiv_apply_snd_self
          (mem_blockPreimage_of_fiber f hf) (fun v hv hve ↦
            absurd (eq_of_mem_blockPreimage_of_fiber f hf hv) hve) g.leftEquiv y))
      · by_cases hr : p = g.right
        · subst hr
          obtain rfl : b = f g.right := ((hf g.right).mpr rfl).symm
          refine (addPairFiberEquiv_apply_right f g.distinct h hf _ _ _ _).trans ?_
          erw [hR y]
          refine Eq.trans ?_ ((Equiv.eq_symm_apply _).mpr (g.addPairRight_toAddPair _)).symm
          exact congrArg _ (Prod.ext rfl (freshBlockEquiv_apply_snd_self
            (mem_blockPreimage_of_fiber f hf) (fun v hv hve ↦
              absurd (eq_of_mem_blockPreimage_of_fiber f hf hv) hve) g.rightEquiv y))
        · have hpD : p ∉ D := by rw [g.cell_eq]; simp [hl, hr]
          have hbl : b ≠ f g.left := fun e ↦ hl ((hf g.left).mp e.symm).symm
          have hbr : b ≠ f g.right := fun e ↦ hr ((hf g.right).mp e.symm).symm
          have hbD : b ∉ D.image f := by rw [g.image_eq f]; simp [hbl, hbr]
          have hAB : (fun v : {v // v ∈ blockPreimage f {b}} ↦ Y v.1) = fun v ↦ X v.1 :=
            funext fun v ↦ hY v.1 (by rw [eq_of_mem_blockPreimage_of_fiber f hf v.2]; exact hpD)
          refine (addPairFiberEquiv_apply_of_ne f hf g.distinct h _ _ _ hbl hbr hl hr _).trans ?_
          erw [hO hbD y, cast_cast, cast_eq]
          change cast (addPair_of_ne g.distinct g.leftBasis g.rightBasis hl hr).symm
            ((cast _ y : blockSystem f X b) ⟨p, mem_blockPreimage_of_fiber f hf⟩) =
              g.toAddPair p (y ⟨p, mem_blockPreimage_of_fiber f hf⟩)
          rw [g.toAddPair_of_notMem hpD, cast_pi_apply hAB]
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ q hY A =>
    partyOp_coarsen_of_fiber f (PartyCircuit.localOp q hY A) (by trivial) hf
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A =>
    partyOp_coarsen_of_fiber f (PartyCircuit.localOps A) (by trivial) hf
  | X, _, _, _, @PartyCircuit.comp _ _ _ Y _ _ _ c c' => by
    change localPartOp (PartyCircuit.comp (coarsen f c) (coarsen f c')) b =
      ((localPartOp c' p * SourceInventory.liftOps (Word.sources c') (localPartOp c) p).submatrix
        id (Equiv.cast (congrFun (SourceInventory.system_append (Word.sources c')
          (Word.sources c) X) p))).submatrix (blockFiberEquiv f hf _)
        ((Equiv.cast (congrFun (SourceInventory.system_append (Word.sources (coarsen f c'))
          (Word.sources (coarsen f c)) _) b)).trans ((coarsenFiberEquiv f hf c'
            (coarsenFiberEquiv f hf c (blockFiberEquiv f hf X))).trans (Equiv.cast (congrFun
              (SourceInventory.system_append (Word.sources c') (Word.sources c) X) p)).symm))
    rw [localPartOp_comp, localPartOp_coarsen_of_fiber c',
      liftOps_coarsen_of_fiber f hf c' (blockFiberEquiv f hf Y)
        (coarsenFiberEquiv f hf c (blockFiberEquiv f hf X)) _ _ (localPartOp_coarsen_of_fiber c),
      submatrix_mul_equiv]
    ext y x
    simp only [submatrix_apply, Equiv.trans_apply, Equiv.cast_apply, ← Equiv.cast_symm,
      cast_cast, cast_eq, id]

end Word

end QuantumCircuit.Party
