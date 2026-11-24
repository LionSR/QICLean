/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.PreparedSourceGate
import QICLean.Circuit.Party.Syntax.CoarsenLocal

/-!
# The local part of a word at one party

The local part of a word (`Word.localPartOp`) is the family of party
operations left after every pair source has been prepared on fresh factors; its input at a party
is the basis of that party in the system `w.sources.system X` prepared by the sources. This module
computes it in three situations.

* A word without pair sources: its local part is its family of party operations, read through
  the identification of the system prepared by the empty inventory
  (`Word.localPartOp_of_sources_eq_nil`, with `SourceInventory.systemEquivOfEqNil`).
* A party that the word does not name: the local part there is the identification of two equal
  bases (`Word.localPartOp_of_notMem_parties`); hence the parties of the local part are parties
  of the word (`Word.parties_localPart_subset`). Equality fails: at a party where the word acts by
  a named identity, such as `localOp p _ 1`, the local part is the identification of equal bases,
  and the local part does not name that party.
* A framed word: its local part is `1 ⊗` the local part of the word, read through the
  identification `Word.frameSystemEquiv` of the prepared systems, the spectator factor in front
  (`Word.localPartOp_frame`).

The proofs run the party operations beside the fresh factors of an inventory
(`SourceInventory.liftOps`, with `SourceInventory.liftOps_append` and
`SourceInventory.liftOps_eq_cast`); running them beside the fresh factors of a framed word commutes
with framing (`Word.liftOps_frame`).

## Main definitions

* `QuantumCircuit.Party.Word.frameSystemEquiv` — the system prepared by the sources of a framed
  word is the spectator factor in front of the system prepared by the sources of the word.

## Main results

* `QuantumCircuit.Party.Word.localPartOp_of_sources_eq_nil`,
  `QuantumCircuit.Party.Word.localPartOp_of_notMem_parties`,
  `QuantumCircuit.Party.Word.parties_localPart_subset`,
  `QuantumCircuit.Party.Word.localPartOp_frame`.
* `QuantumCircuit.Party.Word.liftOps_frame`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `eq:compression-source-gate`,
  `04-compression.tex`, lines 245–251 (the local part of a word: fresh registers prepared before
  their first use, the preceding local maps tensored with identities on them).
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### Casts and the fresh factors of one pair -/

/-- Casts of a pair through a third type and back, followed by a cast of the second component. -/
private theorem cast_cast_cast_prod_mk {A T T' U V : Type} (h : T' = T)
    (e₀ : (A × T') = (A × T))
    (e₁ : (A × T) = U) (e₂ : U = (A × T)) (e₃ e₄ : T = V) (a : A) (y : T') :
    ((cast e₂ (cast e₁ (cast e₀ (a, y)))).1, cast e₃ (cast e₂ (cast e₁ (cast e₀ (a, y)))).2) =
      (a, cast e₄ (cast h y)) := by
  subst h e₁ e₃
  rfl

section addPair

variable {p q : P} (hpq : p ≠ q) (α β : Type)

/-- Party operations of the form `1 ⊗ B`, run beside fresh factors, are `1 ⊗` the operations
run beside the fresh factors, read through `addPairFrameEquiv`. -/
private theorem addPairMatrix_frame [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (W : P → Type) [∀ s, DecidableEq (W s)]
    {Z₁ Z₂ Z₁' Z₂' : P → Type}
    (F₁ : ∀ s, Z₁' s ≃ W s × Z₁ s) (F₂ : ∀ s, Z₂' s ≃ W s × Z₂ s)
    (A : ∀ s, Matrix (Z₁' s) (Z₂' s) ℂ) (B : ∀ s, Matrix (Z₁ s) (Z₂ s) ℂ) (s : P)
    (hAB : A s = ((1 : Matrix (W s) (W s) ℂ) ⊗ₖ B s).submatrix (F₁ s) (F₂ s)) :
    addPairMatrix hpq α β A s =
      ((1 : Matrix (W s) (W s) ℂ) ⊗ₖ addPairMatrix hpq α β B s).submatrix
        (addPairFrameEquiv hpq α β F₁ s) (addPairFrameEquiv hpq α β F₂ s) := by
  ext y x
  simp only [addPairMatrix, addPairFrameEquiv, hAB, reindex_apply, submatrix_apply,
    Equiv.symm_symm, kroneckerMap_apply, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply, Equiv.prodLeftComm_apply, Equiv.apply_symm_apply, one_apply]
  split_ifs <;> simp [mul_comm]

/-- `addPairFrameEquiv` at the first party, through `addPairLeft`. -/
private theorem addPairFrameEquiv_apply_left {W Z Z' : P → Type} (F : ∀ s, Z' s ≃ W s × Z s)
    (z : addPair Z' hpq α β p) :
    addPairFrameEquiv hpq α β F p z =
      ((F p (addPairLeft hpq α β z).2).1,
        (addPairLeft hpq α β).symm
          ((addPairLeft hpq α β z).1, (F p (addPairLeft hpq α β z).2).2)) := by
  simp [addPairFrameEquiv, addPairSiteEquiv, addPairLeft, ← Equiv.cast_symm, cast_cast]

/-- `addPairFrameEquiv` at the second party, through `addPairRight`. -/
private theorem addPairFrameEquiv_apply_right {W Z Z' : P → Type} (F : ∀ s, Z' s ≃ W s × Z s)
    (z : addPair Z' hpq α β q) :
    addPairFrameEquiv hpq α β F q z =
      ((F q (addPairRight hpq α β z).2).1,
        (addPairRight hpq α β).symm
          ((addPairRight hpq α β z).1, (F q (addPairRight hpq α β z).2).2)) := by
  simp [addPairFrameEquiv, addPairSiteEquiv, addPairRight, hpq.symm, ← Equiv.cast_symm,
    cast_cast]

/-- `addPairFrameEquiv` away from the two parties. -/
private theorem addPairFrameEquiv_apply_of_ne {W Z Z' : P → Type} (F : ∀ s, Z' s ≃ W s × Z s)
    {s : P} (hp : s ≠ p) (hq : s ≠ q) (z : addPair Z' hpq α β s) :
    addPairFrameEquiv hpq α β F s z =
      ((F s (cast (addPair_of_ne hpq α β hp hq) z)).1,
        cast (addPair_of_ne hpq α β hp hq).symm
          (F s (cast (addPair_of_ne hpq α β hp hq) z)).2) := by
  simp [addPairFrameEquiv, addPairSiteEquiv, hp, hq]
  rfl

end addPair

/-! ### The local part of a word without pair sources, and at a party not named -/

namespace Word

/-- For two empty inventories, a product of party operations read through the identifications
of the systems they prepare, the second operation run beside the fresh factors of the first, is
the product read through the identification of the system prepared by the concatenation. -/
private theorem submatrix_mul_liftOps_of_eq_nil {X Y Z : P → Type} [∀ q, Fintype (Y q)]
    (S T : SourceInventory P) (hS : S = [])
    (hT : T = []) (hST : S ++ T = []) (p : P) (B' : Matrix (Z p) (S.system Y p) ℂ)
    (B : ∀ q, Matrix (Y q) (T.system X q) ℂ) (C' : Matrix (Z p) (Y p) ℂ)
    (C : Matrix (Y p) (X p) ℂ)
    (h' : B' = C'.submatrix id (SourceInventory.systemEquivOfEqNil S hS Y p))
    (h : B p = C.submatrix id (SourceInventory.systemEquivOfEqNil T hT X p)) :
    (B' * S.liftOps B p).submatrix id
        (Equiv.cast (congrFun (SourceInventory.system_append S T X) p)) =
      (C' * C).submatrix id (SourceInventory.systemEquivOfEqNil (S ++ T) hST X p) := by
  subst hS hT h'
  change (C'.submatrix id (Equiv.refl _) * B p).submatrix id (Equiv.cast rfl) =
    (C' * C).submatrix id (Equiv.refl _)
  rw [h]
  rfl

/-- **The local part of a word without pair sources is the word**: its party operations, read
through the identification of the system prepared by the empty inventory. -/
theorem localPartOp_of_sources_eq_nil : {X Y : P → Type} → [∀ p, DecidableEq (X p)] →
    (w : Word X Y) → (hs : w.sources = []) → (p : P) →
      w.localPartOp p =
        (PartyCircuit.partyOp w p).submatrix id
          (SourceInventory.systemEquivOfEqNil w.sources hs X p)
  | _, _, _, PartyCircuit.done _, _, _ => rfl
  | _, _, _, PartyCircuit.gate _ _ _, hs, _ => (List.cons_ne_nil _ _ hs).elim
  | _, _, _, PartyCircuit.localOp _ _ _, _, _ => rfl
  | _, _, _, PartyCircuit.localOps _, _, _ => rfl
  | _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', hs, p => by
    have hc : Word.sources c = [] := (List.append_eq_nil_iff.mp hs).2
    have hc' : Word.sources c' = [] := (List.append_eq_nil_iff.mp hs).1
    rw [localPartOp_comp]
    exact submatrix_mul_liftOps_of_eq_nil _ _ hc' hc hs p _ _ _ _
      (localPartOp_of_sources_eq_nil c' hc' p) (localPartOp_of_sources_eq_nil c hc p)

/-- The product of the matrices of two identifications of equal bases, with its columns read
through a third identification, is the matrix of the composite identification. -/
private theorem toMatrix_cast_mul_submatrix {A B C D : Type} [Fintype B] [iB : DecidableEq B]
    [iC : DecidableEq C] [iD : DecidableEq D] (h₁ : A = B) (h₂ : B = C) (h₃ : D = C) :
    ((Equiv.cast h₁).toPEquiv.toMatrix * (Equiv.cast h₂).toPEquiv.toMatrix :
        Matrix A C ℂ).submatrix id (Equiv.cast h₃) =
      (Equiv.cast (h₁.trans (h₂.trans h₃.symm))).toPEquiv.toMatrix := by
  subst h₁ h₂ h₃
  obtain rfl : iB = iC := Subsingleton.elim _ _
  obtain rfl : iB = iD := Subsingleton.elim _ _
  simp

/-- **The local part of a word is the identification of equal bases at a party that the word
does not name.** -/
theorem localPartOp_of_notMem_parties [Fintype P] : {X Y : P → Type} →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → (p : P) → p ∉ PartyCircuit.parties w →
      ∃ h : Y p = SourceInventory.system w.sources X p,
        w.localPartOp p = (Equiv.cast h).toPEquiv.toMatrix
  | X, _, _, PartyCircuit.done _, p, _ => ⟨rfl, by
    change (1 : Matrix (X p) (X p) ℂ) = (Equiv.refl (X p)).toPEquiv.toMatrix
    simp⟩
  | _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, p, hp => by
    have hpD : p ∉ D := hp
    refine ⟨(g.outside p hpD).trans (addPair_of_ne g.distinct g.leftBasis g.rightBasis
      (g.ne_left_of_notMem hpD) (g.ne_right_of_notMem hpD)).symm, ?_⟩
    rw [localPartOp_gate]
    congr 2
    ext y
    rw [g.toAddPair_of_notMem hpD, cast_cast]
    rfl
  | _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ q hY A, p, hp => by
    have hpq : p ≠ q := by simpa [PartyCircuit.parties] using hp
    exact ⟨hY p hpq, PartyCircuit.localOpFamily_of_ne q hY A hpq⟩
  | X, _, iX, @PartyCircuit.localOps _ _ _ _ _ _ A, p, hp => by
    simp only [PartyCircuit.parties, Finset.mem_filter, Finset.mem_univ, true_and,
      not_not] at hp
    obtain ⟨h, hA⟩ := hp
    refine ⟨h, ?_⟩
    ext y x
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    change A p y x = @ite _ ((cast h y : X p) = (x : X p)) (iX p _ _) 1 0
    rw [hA y x]
    congr 1
  | _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', p, hp => by
    rw [PartyCircuit.parties, Finset.mem_union, not_or] at hp
    obtain ⟨h₁, e₁⟩ := localPartOp_of_notMem_parties c p hp.1
    obtain ⟨h₂, e₂⟩ := localPartOp_of_notMem_parties c' p hp.2
    obtain ⟨h₃, e₃⟩ := SourceInventory.liftOps_eq_cast (Word.sources c') (localPartOp c) h₁ e₁
    exact ⟨h₂.trans (h₃.trans (congrFun (SourceInventory.system_append (Word.sources c')
      (Word.sources c) _) p).symm), by
        rw [localPartOp_comp, e₂, e₃, toMatrix_cast_mul_submatrix]
        rfl⟩

/-- **The parties of the local part of a word are parties of the word.** -/
theorem parties_localPart_subset [Fintype P] {X Y : P → Type} [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] (w : Word X Y) :
    PartyCircuit.parties w.localPart ⊆ PartyCircuit.parties w := by
  intro p hp
  by_contra hnp
  obtain ⟨h, e⟩ := localPartOp_of_notMem_parties w p hnp
  simp only [localPart, PartyCircuit.parties, Finset.mem_filter, Finset.mem_univ,
    true_and] at hp
  exact hp ⟨h, fun y x ↦ by simp [e, PEquiv.toMatrix_apply, eq_comm]⟩

/-! ### The local part of a framed word -/

section Frame

variable (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- The system prepared by the sources of a framed word on a framed system is the spectator
factor in front of the system prepared by the sources of the word, by recursion on the word.
`F` identifies the two systems on which the sources are prepared. -/
def frameSystemEquiv : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (w : Word X Y) → {Z Z' : P → Type} → (∀ q, Z' q ≃ W q × Z q) →
      ∀ q, SourceInventory.system (Word.sources (w.frame W)) Z' q ≃
        W q × SourceInventory.system (Word.sources w) Z q
  | _, _, _, _, .done _, _, _, F => F
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g, _, _, F =>
    addPairFrameEquiv g.distinct g.leftBasis g.rightBasis F
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, _, F => F
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, _, F => F
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', Z, Z', F => fun q ↦
    (Equiv.cast (congrFun (SourceInventory.system_append (Word.sources (c'.frame W))
      (Word.sources (c.frame W)) Z') q)).trans
        ((frameSystemEquiv c' (frameSystemEquiv c F) q).trans
        ((Equiv.refl _).prodCongr (Equiv.cast (congrFun (SourceInventory.system_append
          (Word.sources c') (Word.sources c) Z) q)).symm))

/-- Party operations of the form `1 ⊗ B`, run beside the fresh factors of the sources of a
framed word, are `1 ⊗` the operations run beside the fresh factors of the word. -/
theorem liftOps_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (w : Word X Y) → {Z₁ Z₂ Z₁' Z₂' : P → Type} → (F₁ : ∀ s, Z₁' s ≃ W s × Z₁ s) →
    (F₂ : ∀ s, Z₂' s ≃ W s × Z₂ s) → (A : ∀ s, Matrix (Z₁' s) (Z₂' s) ℂ) →
    (B : ∀ s, Matrix (Z₁ s) (Z₂ s) ℂ) →
    (∀ s, A s = ((1 : Matrix (W s) (W s) ℂ) ⊗ₖ B s).submatrix (F₁ s) (F₂ s)) → ∀ p,
      SourceInventory.liftOps (Word.sources (w.frame W)) A p =
        ((1 : Matrix (W p) (W p) ℂ) ⊗ₖ SourceInventory.liftOps (Word.sources w) B p).submatrix
          (frameSystemEquiv W w F₁ p) (frameSystemEquiv W w F₂ p)
  | _, _, _, _, .done _, _, _, _, _, _, _, _, _, hAB, p => hAB p
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g, _, _, _, _, F₁, F₂, A, B, hAB, p =>
    addPairMatrix_frame g.distinct g.leftBasis g.rightBasis W F₁ F₂ A B p (hAB p)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, _, _, _, _, _, _, _, hAB, p => hAB p
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, _, _, _, _, _, _, _, hAB, p => hAB p
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', _, _, _, _, F₁, F₂, A, B, hAB, p => by
    change SourceInventory.liftOps (Word.sources (c'.frame W) ++ Word.sources (c.frame W)) A p = _
    rw [SourceInventory.liftOps_append, liftOps_frame c' (frameSystemEquiv W c F₁)
      (frameSystemEquiv W c F₂) _ _ (liftOps_frame c F₁ F₂ A B hAB)]
    change _ = ((1 : Matrix (W p) (W p) ℂ) ⊗ₖ
      SourceInventory.liftOps (Word.sources c' ++ Word.sources c) B p).submatrix
        ((Equiv.cast (congrFun (SourceInventory.system_append (Word.sources (c'.frame W))
          (Word.sources (c.frame W)) _) p)).trans ((frameSystemEquiv W c'
            (frameSystemEquiv W c F₁) p).trans ((Equiv.refl _).prodCongr (Equiv.cast (congrFun
              (SourceInventory.system_append (Word.sources c') (Word.sources c) _) p)).symm)))
        ((Equiv.cast (congrFun (SourceInventory.system_append (Word.sources (c'.frame W))
          (Word.sources (c.frame W)) _) p)).trans ((frameSystemEquiv W c'
            (frameSystemEquiv W c F₂) p).trans ((Equiv.refl _).prodCongr (Equiv.cast (congrFun
              (SourceInventory.system_append (Word.sources c') (Word.sources c) _) p)).symm)))
    rw [SourceInventory.liftOps_append]
    ext y x
    simp only [submatrix_apply, kroneckerMap_apply, Equiv.trans_apply, Equiv.prodCongr_apply,
      Prod.map, Equiv.refl_apply, Equiv.cast_apply, ← Equiv.cast_symm, cast_cast, cast_eq]

omit [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)] in
/-- The canonical reading of the output basis of a framed pair source is the canonical reading
of the source beside the spectator factor, through `addPairFrameEquiv`. -/
private theorem addPairFrameEquiv_toAddPair_frame {D : Finset P} {X Y : P → Type}
    (g : SourceGate D X Y) (s : P) (y : W s × Y s) :
    addPairFrameEquiv g.distinct g.leftBasis g.rightBasis (fun t ↦ Equiv.refl (W t × X t)) s
        ((g.frame W).toAddPair s y) = (y.1, g.toAddPair s y.2) := by
  obtain ⟨a, y⟩ := y
  have hL := (g.frame W).addPairLeft_toAddPair
  have hR := (g.frame W).addPairRight_toAddPair
  have hO := @SourceGate.toAddPair_of_notMem _ _ _ _ _ (g.frame W)
  dsimp only [SourceGate.frame] at hL hR hO ⊢
  by_cases hl : s = g.left
  · subst hl
    rw [addPairFrameEquiv_apply_left]
    erw [hL]
    rw [(Equiv.eq_symm_apply _).mpr (g.addPairLeft_toAddPair y)]
    rfl
  · by_cases hr : s = g.right
    · subst hr
      rw [addPairFrameEquiv_apply_right]
      erw [hR]
      rw [(Equiv.eq_symm_apply _).mpr (g.addPairRight_toAddPair y)]
      rfl
    · have hs : s ∉ D := by rw [g.cell_eq]; simp [hl, hr]
      rw [addPairFrameEquiv_apply_of_ne _ _ _ _ hl hr]
      erw [hO hs]
      rw [g.toAddPair_of_notMem hs]
      exact cast_cast_cast_prod_mk (g.outside s hs) _ _ _ _ _ a y

/-- The identity beside a permutation matrix, with its columns read through an equivalence, is
the matrix of the composite equivalence. -/
private theorem one_kronecker_toMatrix_submatrix {A B C E : Type} [DecidableEq A]
    [DecidableEq C] [DecidableEq E] (f : B ≃ C) (e : E ≃ A × C) :
    ((1 : Matrix A A ℂ) ⊗ₖ f.toPEquiv.toMatrix).submatrix id e =
      (((Equiv.refl A).prodCongr f).trans e.symm).toPEquiv.toMatrix := by
  rw [← PEquiv.toMatrix_refl, ← Equiv.toPEquiv_refl, ← toMatrix_toPEquiv_prodCongr]
  exact toMatrix_toPEquiv_submatrix _ (Equiv.refl _) e

/-- **The local part of a framed word is `1 ⊗` the local part of the word**, read through the
identification `frameSystemEquiv` of the prepared systems. -/
theorem localPartOp_frame : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → ∀ p,
      Word.localPartOp (w.frame W) p =
        ((1 : Matrix (W p) (W p) ℂ) ⊗ₖ w.localPartOp p).submatrix id
          (frameSystemEquiv W w (fun s ↦ Equiv.refl (W s × X s)) p)
  | _, _, _, _, .done _, _ => one_kronecker_one.symm
  | X, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g, p => by
    change ((g.frame W).toAddPair p).toPEquiv.toMatrix =
      ((1 : Matrix (W p) (W p) ℂ) ⊗ₖ (g.toAddPair p).toPEquiv.toMatrix).submatrix id
        (addPairFrameEquiv g.distinct g.leftBasis g.rightBasis (fun s ↦ Equiv.refl (W s × X s)) p)
    rw [one_kronecker_toMatrix_submatrix]
    refine congrArg (fun e ↦ (Equiv.toPEquiv e).toMatrix) (Equiv.ext fun y ↦ ?_)
    exact (Equiv.eq_symm_apply (addPairFrameEquiv g.distinct g.leftBasis g.rightBasis
      (fun s ↦ Equiv.refl (W s × X s)) p)).mpr (addPairFrameEquiv_toAddPair_frame W g p y)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ q hY A, p =>
    PartyCircuit.partyOp_frame W (PartyCircuit.localOp (G := SourceGate) q hY A) p
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _ => rfl
  | X, _, _, _, @PartyCircuit.comp _ _ _ Y _ _ _ c c', p => by
    change localPartOp (PartyCircuit.comp (c.frame W) (c'.frame W)) p =
      ((1 : Matrix (W p) (W p) ℂ) ⊗ₖ (localPartOp c' p *
        SourceInventory.liftOps (Word.sources c') (localPartOp c) p).submatrix id
          (Equiv.cast (congrFun (SourceInventory.system_append (Word.sources c') (Word.sources c)
            X) p))).submatrix id
        ((Equiv.cast (congrFun (SourceInventory.system_append (Word.sources (c'.frame W))
          (Word.sources (c.frame W)) _) p)).trans ((frameSystemEquiv W c'
            (frameSystemEquiv W c fun s ↦ Equiv.refl (W s × X s)) p).trans
              ((Equiv.refl _).prodCongr (Equiv.cast (congrFun (SourceInventory.system_append
                (Word.sources c') (Word.sources c) _) p)).symm)))
    rw [localPartOp_comp, localPartOp_frame c' p,
      liftOps_frame W c' (fun s ↦ Equiv.refl (W s × Y s))
        (frameSystemEquiv W c fun s ↦ Equiv.refl (W s × X s)) _ _ (localPartOp_frame c) p,
      submatrix_mul_equiv, ← mul_kronecker_mul, Matrix.one_mul]
    ext y x
    simp only [submatrix_apply, kroneckerMap_apply, Equiv.trans_apply, Equiv.prodCongr_apply,
      Prod.map, Equiv.refl_apply, Equiv.cast_apply, ← Equiv.cast_symm, cast_cast, cast_eq, id]

end Frame

end Word

end QuantumCircuit.Party

/-! ### The local part of a word run on its cell, at a party outside the cell

At a party `p` outside the cell `D`, the local part of `Word.onCell D hY w` is the identification
of the two equal bases `Y p` and the prepared basis (`Word.localPartOp_onCell_of_notMem`). The
proof evaluates, at a party that is no endpoint of any source, the identification
`Word.frameSystemEquiv` of prepared systems (`Word.frameSystemEquiv_apply_of_forall_ne`) and the
party operations run beside fresh factors (`SourceInventory.liftOps_apply_of_forall_ne`); both are
read through identifications of equal bases there. Source: `04-compression.tex`, lines 21–36 and
233–267.
-/

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-- Three casts in a row are one cast. -/
private theorem cast_cast_cast_eq {A B C D : Type} (h₁ : A = B) (h₂ : B = C) (h₃ : C = D)
    (h₄ : A = D) (a : A) : cast h₃ (cast h₂ (cast h₁ a)) = cast h₄ a := by
  subst h₁ h₂ h₃
  rfl

/-- Two successive coordinate identifications are heterogeneously equal to the input. -/
private theorem equiv_cast_cast_heq {A B C : Type} (h : A = B) (h' : B = C) (a : A) :
    HEq (Equiv.cast h' (Equiv.cast h a)) a :=
  (cast_heq h' _).trans (cast_heq h a)

namespace Word

variable (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- **At a party that is no endpoint of the sources of a word**, the identification
`frameSystemEquiv` of the prepared systems is the given identification `F` of the systems on
which the sources are prepared, read through identifications of equal bases. -/
theorem frameSystemEquiv_apply_of_forall_ne : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → {Z Z' : P → Type} →
    (F : ∀ q, Z' q ≃ W q × Z q) → {p : P} → (∀ s ∈ w.sources, s.left ≠ p ∧ s.right ≠ p) →
      ∃ (h₁ : SourceInventory.system (Word.sources (w.frame W)) Z' p = Z' p)
        (h₂ : Z p = SourceInventory.system (Word.sources w) Z p),
        ∀ z, frameSystemEquiv W w F p z = ((F p (cast h₁ z)).1, cast h₂ (F p (cast h₁ z)).2)
  | _, _, _, _, .done _, _, _, _, _, _ => ⟨rfl, rfl, fun _ ↦ rfl⟩
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ g, _, _, F, _, hp => by
    have hl := (hp g.toPairSource List.mem_cons_self).1.symm
    have hr := (hp g.toPairSource List.mem_cons_self).2.symm
    exact ⟨addPair_of_ne g.distinct g.leftBasis g.rightBasis hl hr,
      (addPair_of_ne g.distinct g.leftBasis g.rightBasis hl hr).symm,
      addPairFrameEquiv_apply_of_ne g.distinct g.leftBasis g.rightBasis F hl hr⟩
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, _, _, _, _ => ⟨rfl, rfl, fun _ ↦ rfl⟩
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, _, _, _, _ => ⟨rfl, rfl, fun _ ↦ rfl⟩
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', Z, Z', F, p, hp => by
    obtain ⟨h₁, h₂, e⟩ := frameSystemEquiv_apply_of_forall_ne c F fun s hs ↦
      hp s (List.mem_append_right _ hs)
    obtain ⟨h₁', h₂', e'⟩ := frameSystemEquiv_apply_of_forall_ne c'
      (frameSystemEquiv W c F) fun s hs ↦ hp s (List.mem_append_left _ hs)
    refine ⟨(congrFun (SourceInventory.system_append (Word.sources (c'.frame W))
      (Word.sources (c.frame W)) Z') p).trans (h₁'.trans h₁), h₂.trans (h₂'.trans
        (congrFun (SourceInventory.system_append (Word.sources c') (Word.sources c) Z) p).symm),
      fun z ↦ ?_⟩
    change ((Equiv.refl _).prodCongr (Equiv.cast (congrFun (SourceInventory.system_append
        (Word.sources c') (Word.sources c) Z) p))).symm (frameSystemEquiv W c'
          (frameSystemEquiv W c F) p (cast _ z)) = _
    rw [e', e]
    exact Prod.ext (congrArg (fun u ↦ (F p u).1) (cast_cast_cast_eq _ _ _ _ z))
      ((cast_cast_cast_eq _ _ _ _ _).trans
        (congrArg (cast _) (congrArg (fun u ↦ (F p u).2) (cast_cast_cast_eq _ _ _ _ z))))

end Word

/-- A permutation matrix with its columns read through an equivalence is the matrix of the
composite equivalence. -/
private theorem toMatrix_submatrix_id {A B D : Type} [DecidableEq B] [DecidableEq D]
    (g : A ≃ B) (c : D ≃ B) :
    (g.toPEquiv.toMatrix : Matrix A B ℂ).submatrix id c = (g.trans c.symm).toPEquiv.toMatrix :=
  toMatrix_toPEquiv_submatrix g (Equiv.refl A) c

/-- A permutation matrix read through equivalences is the identification of two equal bases when
the equivalences intertwine it with the identification. -/
private theorem toMatrix_submatrix_eq_cast {A B C D E : Type} [DecidableEq B] [DecidableEq E]
    (g : A ≃ B) (c₂ : D ≃ B) (r : C ≃ A) (c₁ : E ≃ D) (h : C = E)
    (H : ∀ y, c₂ (c₁ (cast h y)) = g (r y)) :
    (((g.toPEquiv.toMatrix : Matrix A B ℂ).submatrix id c₂).submatrix r id).submatrix id c₁ =
      (Equiv.cast h).toPEquiv.toMatrix := by
  ext y x
  simp only [submatrix_apply, id, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Equiv.cast_apply, ← H y, c₂.apply_eq_iff_eq, c₁.apply_eq_iff_eq, eq_comm]

namespace Word

/-- **The local part of a word run on its cell, at a party outside the cell, is the
identification of two equal bases.** The relabellings by `cellEquiv` at the two ends of
`Word.onCell` are not identifications of equal bases at such a party (so the party is in
general named by the word, and `Word.localPartOp_of_notMem_parties` does not apply), but their
composite with the local part of the framed coarse word is. Source: `04-compression.tex`,
lines 21–36 (an operation on the parties of a cell acts as the identity outside it). -/
theorem localPartOp_onCell_of_notMem [Finite P] (D : Finset P) {X Y : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (hY : ∀ s ∉ D, Y s = X s) (w : Word (fun s : ↥D ↦ X s) (fun s : ↥D ↦ Y s)) {p : P}
    (hp : p ∉ D) :
    ∃ h : Y p = SourceInventory.system (onCell D hY w).sources X p,
      (onCell D hY w).localPartOp p = (Equiv.cast h).toPEquiv.toMatrix := by
  have := Fintype.ofFinite P
  have hS : ∀ s ∈ Word.sources (coarsen (Subtype.val : ↥D → P) w),
      s.left ≠ p ∧ s.right ≠ p := by
    intro s hs
    rw [sources_coarsen] at hs
    obtain ⟨t, -, -, rfl⟩ := (SourceInventory.mem_mapOwner _ _ _).mp hs
    exact ⟨fun e ↦ hp (e ▸ t.left.2), fun e ↦ hp (e ▸ t.right.2)⟩
  have hSF : ∀ s ∈ Word.sources ((coarsen (Subtype.val : ↥D → P) w).frame
      fun q ↦ q ∉ D → X q), s.left ≠ p ∧ s.right ≠ p := by
    rw [sources_frame]
    exact hS
  have hcc : p ∉ PartyCircuit.parties (coarsen (Subtype.val : ↥D → P) w) := fun h ↦ by
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp (parties_coarsen_subset _ w h)
    exact hp (hq ▸ q.2)
  obtain ⟨h₀, e₀⟩ := localPartOp_of_notMem_parties (coarsen (Subtype.val : ↥D → P) w) p hcc
  obtain ⟨h₁, h₂, eF⟩ := frameSystemEquiv_apply_of_forall_ne (fun q ↦ q ∉ D → X q)
    (coarsen (Subtype.val : ↥D → P) w)
    (Z := blockSystem Subtype.val fun s : ↥D ↦ X s) (fun s ↦ Equiv.refl _) hS
  obtain ⟨k₁, k₂, eL⟩ := SourceInventory.liftOps_apply_of_forall_ne
    (fun s ↦ ((cellEquiv D X X (fun _ _ ↦ rfl) s).symm).toPEquiv.toMatrix) _ hSF
  have key : localPartOp (onCell D hY w) p = ((cellEquiv D X Y hY p).toPEquiv.toMatrix *
      (localPartOp ((coarsen (Subtype.val : ↥D → P) w).frame fun q ↦ q ∉ D → X q) p *
        SourceInventory.liftOps (Word.sources ((coarsen (Subtype.val : ↥D → P) w).frame
          fun q ↦ q ∉ D → X q))
          (fun s ↦ ((cellEquiv D X X (fun _ _ ↦ rfl) s).symm).toPEquiv.toMatrix) p).submatrix id
        (Equiv.cast (congrFun (SourceInventory.system_append (Word.sources
          ((coarsen (Subtype.val : ↥D → P) w).frame fun q ↦ q ∉ D → X q)) [] X) p))).submatrix id
      (Equiv.cast (congrFun (SourceInventory.system_append [] (Word.sources
        ((coarsen (Subtype.val : ↥D → P) w).frame fun q ↦ q ∉ D → X q) ++ []) X) p)) := rfl
  refine ⟨(hY p hp).trans (k₂.symm.trans (congrFun (SourceInventory.system_append
    (Word.sources ((coarsen (Subtype.val : ↥D → P) w).frame fun q ↦ q ∉ D → X q)) [] X) p).symm),
    ?_⟩
  rw [key, localPartOp_frame, e₀, eL, toMatrix_toPEquiv_submatrix, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  rw [one_kronecker_toMatrix_submatrix, toMatrix_submatrix_id]
  refine toMatrix_submatrix_eq_cast _ _ _ _ _ fun y ↦ ?_
  have hz := eF ((frameSystemEquiv (fun q ↦ q ∉ D → X q) (coarsen (Subtype.val : ↥D → P) w)
    (fun s ↦ Equiv.refl _) p).symm ((cellEquiv D X Y hY p y).1, cast h₀ (cellEquiv D X Y hY p y).2))
  rw [Equiv.apply_symm_apply] at hz
  change _ = cast k₂.symm ((cellEquiv D X X (fun _ _ ↦ rfl) p).symm (cast h₁
    ((frameSystemEquiv (fun q ↦ q ∉ D → X q) (coarsen (Subtype.val : ↥D → P) w)
      (fun s ↦ Equiv.refl _) p).symm ((cellEquiv D X Y hY p y).1,
        cast h₀ (cellEquiv D X Y hY p y).2))))
  have ha : (cast h₁ ((frameSystemEquiv (fun q ↦ q ∉ D → X q)
      (coarsen (Subtype.val : ↥D → P) w) (fun s ↦ Equiv.refl _) p).symm
        ((cellEquiv D X Y hY p y).1, cast h₀ (cellEquiv D X Y hY p y).2))).1 =
      (cellEquiv D X Y hY p y).1 := (congrArg Prod.fst hz).symm
  rw [cellEquiv_symm_apply_of_notMem D X X (fun _ _ ↦ rfl) hp, ha]
  apply eq_of_heq
  have hv : HEq ((cellEquiv D X Y hY p y).1 hp) y := cast_heq (hY p hp) y
  exact ((equiv_cast_cast_heq _ _ _).trans (cast_heq _ _)).trans
    ((cast_heq _ _).trans ((cast_heq _ _).trans hv)).symm

end Word

end QuantumCircuit.Party
