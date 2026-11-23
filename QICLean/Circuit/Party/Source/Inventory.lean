/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Source.InventoryExpansion

/-!
# Source inventories: grouping, ordering and completion

Every normalized inventory is obtained, by expansion, from one with at most one normalized
source on every unordered pair of parties and the same set of pairs
(`SourceInventory.exists_grouped`). Two inventories on the same distinct pairs can be prepared
in a common order and orientation of slots, the ordered endpoints of a reference inventory
with prescribed bases and vectors (`SourceInventory.ofSlots`,
`SourceInventory.exists_ofSlots_expands`). A scalar source, with one basis vector at both
endpoints, is removed by local relabellings (`SourceInventory.Expands.unit_cons`), so every
grouped inventory can be completed to one with a source on every unordered pair of distinct
parties (`SourceInventory.exists_complete`).

## Main definitions

* `QuantumCircuit.Party.SourceInventory.SlotBases` — the bases of the two halves of the slots.
* `QuantumCircuit.Party.SourceInventory.ofSlots` — sources on the slots of a reference
  inventory.
* `QuantumCircuit.Party.Word.eraseUnitPair` — the removal of a scalar source.

## Main results

* `QuantumCircuit.Party.SourceInventory.exists_grouped` — one source per unordered pair.
* `QuantumCircuit.Party.SourceInventory.exists_ofSlots_expands` — a common order and
  orientation.
* `QuantumCircuit.Party.SourceInventory.exists_complete_extension`,
  `QuantumCircuit.Party.SourceInventory.exists_complete` — a source on every unordered pair.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1, `04-compression.tex`,
  lines 68–70 and 125–127; equation `eq:compression-source-gate`, lines 233–267 (scalar sources
  on unused pairs at lines 243–245).
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type}

namespace SourceInventory

variable [DecidableEq P] {X : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  [Fintype P]

/-! ### Grouping -/

/-- Two sources on the same unordered pair can be combined, even if their endpoint orders
differ. Source: Lemma 5.1, `04-compression.tex`, lines 125–127. -/
theorem exists_combined (s t : PairSource P) (h : s.partyPair = t.partyPair)
    (hs : ‖s.vector‖ = 1) (ht : ‖t.vector‖ = 1) :
    ∃ u : PairSource P, ‖u.vector‖ = 1 ∧ u.partyPair = s.partyPair ∧
      ∀ T : SourceInventory P, Expands (u :: T) (s :: t :: T) := by
  change s(s.left, s.right) = s(t.left, t.right) at h
  rcases Sym2.eq_iff.mp h with ⟨hLeft, hRight⟩ | ⟨hLeft, hRight⟩
  · refine ⟨s.combine t hLeft hRight, ?_, rfl, ?_⟩
    · simp only [PairSource.norm_combine_vector, hs, ht, one_mul]
    · exact Expands.combine s t hLeft hRight
  · refine ⟨s.combine t.reverse hLeft hRight, ?_, rfl, ?_⟩
    · exact (PairSource.norm_combine_vector s t.reverse hLeft hRight).trans
        (by rw [PairSource.norm_reverse_vector, hs, ht, one_mul])
    · intro T
      exact (Expands.combine s t.reverse hLeft hRight T).trans
        (Expands.cons s (Expands.reverse t T))

/-- One more normalized source can be added to an inventory with at most one source on each
unordered pair, combining it with the source on its pair if there is one. Source: Lemma 5.1,
`04-compression.tex`, lines 125–127. -/
private theorem exists_insert (s : PairSource P) (S : SourceInventory P)
    (hs : ‖s.vector‖ = 1) (hS : S.IsNormalized) (hN : (S.map PairSource.partyPair).Nodup) :
    ∃ G : SourceInventory P, G.IsNormalized ∧ (G.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ G.map PairSource.partyPair ↔ k = s.partyPair ∨ k ∈ S.map PairSource.partyPair) ∧
      Expands G (s :: S) := by
  induction S with
  | nil =>
      refine ⟨[s], ?_, by simp, ?_, Expands.refl _⟩
      · exact (isNormalized_cons _ _).2 ⟨hs, by simp [IsNormalized]⟩
      · intro k
        simp
  | cons t T ih =>
      obtain ⟨ht, hT⟩ := isNormalized_cons _ _ |>.mp hS
      obtain ⟨htN, hTN⟩ := List.nodup_cons.mp hN
      by_cases hst : s.partyPair = t.partyPair
      · obtain ⟨u, hu, huk, hE⟩ := exists_combined s t hst hs ht
        refine ⟨u :: T, (isNormalized_cons _ _).2 ⟨hu, hT⟩, ?_, ?_, hE T⟩
        · simpa only [List.map_cons, List.nodup_cons, huk, hst] using hN
        · intro k
          simp only [List.map_cons, List.mem_cons, huk, hst]
          tauto
      · obtain ⟨G, hG, hGN, hGK, hGE⟩ := ih hT hTN
        refine ⟨t :: G, (isNormalized_cons _ _).2 ⟨ht, hG⟩, ?_, ?_,
          (Expands.cons t hGE).trans (Expands.swap s t T)⟩
        · refine List.nodup_cons.mpr ⟨?_, hGN⟩
          intro hm
          rcases (hGK t.partyPair).mp hm with he | hm
          · exact hst he.symm
          · exact htN hm
        · intro k
          simp only [List.map_cons, List.mem_cons, hGK]
          tauto

/-- Every normalized finite source inventory is obtained from one normalized source per
participating unordered pair by allowed local operations. The set of participating pairs is
unchanged. Source: Lemma 5.1, `04-compression.tex`, lines 68–70 and 125–127. -/
theorem exists_grouped (S : SourceInventory P) (hS : S.IsNormalized) :
    ∃ G : SourceInventory P, G.IsNormalized ∧ (G.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ G.map PairSource.partyPair ↔ k ∈ S.map PairSource.partyPair) ∧
      G.Expands S := by
  induction S with
  | nil => exact ⟨[], by simp [IsNormalized], by simp, fun _ ↦ Iff.rfl, Expands.refl _⟩
  | cons s S ih =>
      obtain ⟨hs, hS⟩ := (isNormalized_cons _ _).mp hS
      obtain ⟨G, hG, hGN, hGK, hGE⟩ := ih hS
      obtain ⟨H, hH, hHN, hHK, hHE⟩ := exists_insert s G hs hG hGN
      refine ⟨H, hH, hHN, ?_, hHE.trans (Expands.cons s hGE)⟩
      intro k
      rw [hHK, hGK]
      simp only [List.map_cons, List.mem_cons]

/-! ### Slots -/

/-- Basis types for the two fresh factors of `n` slots. -/
structure SlotBases (n : ℕ) : Type 1 where
  /-- The basis at the first endpoint of each slot. -/
  left : Fin n → Type
  /-- The basis at the second endpoint of each slot. -/
  right : Fin n → Type
  [leftFintype : ∀ i, Fintype (left i)]
  [leftDecEq : ∀ i, DecidableEq (left i)]
  [rightFintype : ∀ i, Fintype (right i)]
  [rightDecEq : ∀ i, DecidableEq (right i)]

attribute [instance] SlotBases.leftFintype SlotBases.leftDecEq SlotBases.rightFintype
  SlotBases.rightDecEq

/-- The slot bases `B` with one more slot in front. -/
def SlotBases.cons {n : ℕ} (α β : Type) [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (B : SlotBases n) : SlotBases (n + 1) where
  left := Fin.cons α B.left
  right := Fin.cons β B.right
  leftFintype := Fin.cases (inferInstanceAs (Fintype α)) fun i ↦ inferInstanceAs
    (Fintype (B.left i))
  leftDecEq := Fin.cases (inferInstanceAs (DecidableEq α)) fun i ↦ inferInstanceAs
    (DecidableEq (B.left i))
  rightFintype := Fin.cases (inferInstanceAs (Fintype β)) fun i ↦ inferInstanceAs
    (Fintype (B.right i))
  rightDecEq := Fin.cases (inferInstanceAs (DecidableEq β)) fun i ↦ inferInstanceAs
    (DecidableEq (B.right i))

/-- The slots after the first one. -/
def SlotBases.tail {n : ℕ} (B : SlotBases (n + 1)) : SlotBases n where
  left i := B.left i.succ
  right i := B.right i.succ

/-- The bases of the sources of an inventory. -/
def bases (R : SourceInventory P) : SlotBases R.length where
  left i := (R.get i).leftBasis
  right i := (R.get i).rightBasis

/-- Sources with the endpoint parties and order of a reference inventory, and with prescribed
bases and vectors. Source: `eq:compression-source-gate`, `04-compression.tex`,
lines 253–267. -/
def ofSlots (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) : SourceInventory P :=
  List.ofFn fun i ↦
    { left := (R.get i).left
      right := (R.get i).right
      distinct := (R.get i).distinct
      leftBasis := B.left i
      rightBasis := B.right i
      vector := η i }

omit [Fintype P] [DecidableEq P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- No slots give the empty inventory. -/
@[simp] theorem ofSlots_nil (B : SlotBases 0) (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) :
    ofSlots ([] : SourceInventory P) B η = [] :=
  rfl

omit [Fintype P] [DecidableEq P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- Separate the first source from the remaining slots. -/
theorem ofSlots_cons (r : PairSource P) (R : SourceInventory P) (B : SlotBases (r :: R).length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) :
    ofSlots (r :: R) B η =
      { left := r.left, right := r.right, distinct := r.distinct, leftBasis := B.left 0,
        rightBasis := B.right 0, vector := η 0 } ::
        ofSlots R B.tail (fun i ↦ η i.succ) := by
  simp [ofSlots, List.ofFn_succ, SlotBases.tail]

omit [Fintype P] [DecidableEq P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- The inventory is its own slots. -/
theorem ofSlots_bases (R : SourceInventory P) :
    ofSlots R R.bases (fun i ↦ (R.get i).vector) = R :=
  (congrArg List.ofFn (funext fun _ ↦ rfl)).trans (List.ofFn_get R)

omit [Fintype P] [DecidableEq P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- Normalized vectors give a normalized source inventory. -/
theorem isNormalized_ofSlots (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (hη : ∀ i, ‖η i‖ = 1) :
    (ofSlots R B η).IsNormalized := by
  intro s hs
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
  exact hη i

omit [Fintype P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- Changing the source vectors leaves the prepared system unchanged. -/
theorem system_ofSlots_eq (R : SourceInventory P) (B : SlotBases R.length)
    (η η' : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) (X : P → Type) :
    (ofSlots R B η).system X = (ofSlots R B η').system X := by
  induction R generalizing X with
  | nil => rfl
  | cons r R ih =>
      rw [ofSlots_cons, ofSlots_cons, system_cons, system_cons]
      exact congrArg (fun Z ↦ addPair Z r.distinct (B.left 0) (B.right 0))
        (ih B.tail (fun i ↦ η i.succ) (fun i ↦ η' i.succ) X)

omit [Fintype P] [DecidableEq P] [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] in
/-- The slots have exactly the unordered pairs of the reference inventory. -/
@[simp] theorem partyPairs_ofSlots (R : SourceInventory P) (B : SlotBases R.length)
    (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)) :
    (ofSlots R B η).map PairSource.partyPair = R.map PairSource.partyPair := by
  simpa only [ofSlots, List.map_ofFn, Function.comp_def, PairSource.partyPair] using
    congrArg (List.map PairSource.partyPair) (List.ofFn_get R)

/-- Orient a normalized source according to a prescribed occurrence of the same unordered
pair. Source: `eq:compression-source-gate`, `04-compression.tex`, lines 253–267. -/
private theorem exists_oriented (r s : PairSource P) (hs : ‖s.vector‖ = 1)
    (hk : r.partyPair = s.partyPair) :
    ∃ u : PairSource P, u.left = r.left ∧ u.right = r.right ∧ ‖u.vector‖ = 1 ∧
      ∀ T : SourceInventory P, Expands (u :: T) (s :: T) := by
  change s(r.left, r.right) = s(s.left, s.right) at hk
  rcases Sym2.eq_iff.mp hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨s, h1.symm, h2.symm, hs, fun _ ↦ Expands.refl _⟩
  · exact ⟨s.reverse, h1.symm, h2.symm, (PairSource.norm_reverse_vector s).trans hs,
      fun T ↦ Expands.reverse s T⟩

/-- Reorder normalized sources along a permutation of their unordered pairs. -/
private theorem exists_ofSlots_expands_of_perm : (R S : SourceInventory P) → S.IsNormalized →
    (R.map PairSource.partyPair).Perm (S.map PairSource.partyPair) →
    ∃ (B : SlotBases R.length) (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)),
      (∀ i, ‖η i‖ = 1) ∧ (ofSlots R B η).Expands S
  | [], S, _, hk => by
    obtain rfl : S = [] := List.map_eq_nil_iff.mp (List.Perm.nil_eq hk).symm
    refine ⟨bases [], fun i ↦ i.elim0, fun i ↦ i.elim0, ?_⟩
    rw [ofSlots_nil]
  | r :: R, S, hS, hk => by
    have hmem : r.partyPair ∈ S.map PairSource.partyPair := hk.subset (List.mem_cons_self ..)
    obtain ⟨s, hsS, hsr⟩ := List.mem_map.mp hmem
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hsS
    have hperm : (l₁ ++ s :: l₂).Perm (s :: (l₁ ++ l₂)) := List.perm_middle
    have hk' : (R.map PairSource.partyPair).Perm ((l₁ ++ l₂).map PairSource.partyPair) := by
      have h2 := hk.trans (hperm.map PairSource.partyPair)
      rw [List.map_cons, List.map_cons, ← hsr] at h2
      exact h2.cons_inv
    obtain ⟨B, η, hη, hE⟩ := exists_ofSlots_expands_of_perm R (l₁ ++ l₂)
      (fun t ht ↦ hS t (hperm.symm.subset (List.mem_cons_of_mem _ ht))) hk'
    obtain ⟨⟨ul, ur, ud, uα, uβ, uv⟩, h1, h2, hu, hU⟩ :=
      exists_oriented r s (hS s hsS) hsr.symm
    dsimp only at h1 h2 hu
    subst h1 h2
    refine ⟨SlotBases.cons uα uβ B, Fin.cons uv η, Fin.cases hu hη, ?_⟩
    rw [ofSlots_cons]
    exact ((Expands.cons _ hE).trans (hU _)).trans (Expands.of_perm hperm.symm)

/-- Inventories with the same distinct unordered pairs admit the same ordered endpoint slots.
The source vectors are normalized, and allowed operations containing no sources recover the
original preparation for every spectator system. Source: `eq:compression-source-gate`,
`04-compression.tex`, lines 253–267. -/
theorem exists_ofSlots_expands (R S : SourceInventory P)
    (hR : (R.map PairSource.partyPair).Nodup) (hS : S.IsNormalized)
    (hSN : (S.map PairSource.partyPair).Nodup)
    (hK : ∀ k, k ∈ R.map PairSource.partyPair ↔ k ∈ S.map PairSource.partyPair) :
    ∃ (B : SlotBases R.length) (η : ∀ i, EuclideanSpace ℂ (B.left i × B.right i)),
      (∀ i, ‖η i‖ = 1) ∧ (ofSlots R B η).Expands S :=
  exists_ofSlots_expands_of_perm R S hS ((List.perm_ext_iff_of_nodup hR hSN).mpr hK)

end SourceInventory

variable [Fintype P] [DecidableEq P]

/-! ### Unit sources -/

/-- The equivalence removing the two `Unit` factors of `addPair X hpq Unit Unit`, through
`addPairSiteEquiv`. -/
def unitPairEquiv {X : P → Type} {p q : P} (hpq : p ≠ q) (s : P) :
    addPair X hpq Unit Unit s ≃ X s :=
  (addPairSiteEquiv hpq Unit Unit X s).trans
    (@Equiv.uniqueProd (X s) _ (pairFactor.unique hpq Unit Unit s))

/-- Remove the two scalar factors of a unit source by local relabellings at its endpoints. Source:
`eq:compression-source-gate`, `04-compression.tex`, lines 243–245. -/
noncomputable def Word.eraseUnitPair {X : P → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] {p q : P} (hpq : p ≠ q) : Word (addPair X hpq Unit Unit) X :=
  PartyCircuit.relabel fun s ↦ (unitPairEquiv hpq s).symm

/-- Removing a scalar pair uses only allowed local operations and exactly undoes its
preparation. Source: `04-compression.tex`, lines 243–245. -/
theorem Word.eraseUnitPair_spec {X : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    {p q : P} (hpq : p ≠ q) :
    (Word.eraseUnitPair (X := X) hpq).IsAllowed ∧
      (Word.eraseUnitPair (X := X) hpq).sources = [] ∧
      (Word.eraseUnitPair (X := X) hpq).op *
        (Word.sourceAt hpq Unit Unit (PairSource.unit p q hpq).vector X).op = 1 := by
  refine ⟨Word.isAllowed_relabel _, rfl, ?_⟩
  change Word.op (Word.eraseUnitPair (X := X) hpq) *
    (Word.sourceAt hpq Unit Unit (EuclideanSpace.single ((), ()) (1 : ℂ)) X).op = 1
  rw [Word.op_sourceAt]
  unfold Word.op Word.eraseUnitPair
  rw [PartyCircuit.op_relabel_mul, addPairConfigEquiv_eq_siteEquiv]
  ext y x
  simp [unitPairEquiv, one_apply, funext_iff]

/-- Adding a scalar source before an inventory can be undone by allowed operations containing no
pair sources, uniformly over all spectator systems. Source: `04-compression.tex`, lines 243–245. -/
theorem SourceInventory.Expands.unit_cons {p q : P} (hpq : p ≠ q) (S : SourceInventory P) :
    SourceInventory.Expands (PairSource.unit p q hpq :: S) S := by
  intro X _ _
  obtain ⟨ha, hs, he⟩ := Word.eraseUnitPair_spec (X := S.system X) hpq
  refine ⟨Word.eraseUnitPair hpq, ha, hs, ?_⟩
  rw [SourceInventory.op_prepare_cons]
  exact (Matrix.mul_assoc _ _ _).symm.trans
    ((congrArg (· * (S.prepare X).op) he).trans (Matrix.one_mul _))

/-! ### Completion -/

namespace SourceInventory

/-- Insert scalar sources for the missing pairs of a finite list, retaining the original
inventory as a suffix. Source: `04-compression.tex`, lines 243–245. -/
private theorem exists_extension_covering (K : List (Sym2 P)) (S : SourceInventory P)
    (hS : S.IsNormalized) (hN : (S.map PairSource.partyPair).Nodup)
    (hUnit : ∀ k : Sym2 P, ¬ k.IsDiag → ∃ s : PairSource P,
      ‖s.vector‖ = 1 ∧
      (Fintype.card s.leftBasis = 1 ∧ Fintype.card s.rightBasis = 1) ∧
      s.partyPair = k ∧ ∀ T : SourceInventory P, Expands (s :: T) T) :
    ∃ U : SourceInventory P,
      (∀ s ∈ U, Fintype.card s.leftBasis = 1 ∧ Fintype.card s.rightBasis = 1) ∧
      (U ++ S).IsNormalized ∧ ((U ++ S).map PairSource.partyPair).Nodup ∧
      (∀ k ∈ K, ¬ k.IsDiag → k ∈ (U ++ S).map PairSource.partyPair) ∧
      (U ++ S).Expands S := by
  induction K with
  | nil => exact ⟨[], by simp, hS, hN, by simp, Expands.refl S⟩
  | cons k K ih =>
      obtain ⟨U, hU, hUS, hUN, hUK, hUE⟩ := ih
      by_cases hk : k.IsDiag ∨ k ∈ (U ++ S).map PairSource.partyPair
      · refine ⟨U, hU, hUS, hUN, ?_, hUE⟩
        exact List.forall_mem_cons.mpr ⟨fun h ↦ hk.resolve_left h, hUK⟩
      · obtain ⟨s, hs, hd, hsk, hE⟩ := hUnit k (fun h ↦ hk (Or.inl h))
        refine ⟨s :: U, List.forall_mem_cons.mpr ⟨hd, hU⟩,
          (isNormalized_cons _ _).mpr ⟨hs, hUS⟩,
          List.nodup_cons.mpr ⟨fun h ↦ hk (Or.inr (hsk ▸ h)), hUN⟩,
          ?_, (hE (U ++ S)).trans hUE⟩
        intro j hj hjd
        exact List.mem_cons.mpr ((List.mem_cons.mp hj).imp
          (fun h ↦ h.trans hsk.symm) (fun h ↦ hUK j h hjd))

/-- Complete a grouped inventory by prepending scalar sources only on missing pairs; the
original sources remain the final suffix. Source: `04-compression.tex`, lines 243–245. -/
theorem exists_complete_extension (S : SourceInventory P) (hS : S.IsNormalized)
    (hN : (S.map PairSource.partyPair).Nodup) :
    ∃ U : SourceInventory P,
      (∀ s ∈ U, Fintype.card s.leftBasis = 1 ∧ Fintype.card s.rightBasis = 1 ∧
        s.partyPair ∉ S.map PairSource.partyPair) ∧
      (U ++ S).IsNormalized ∧ ((U ++ S).map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ (U ++ S).map PairSource.partyPair ↔ ¬ k.IsDiag) ∧
      (U ++ S).Expands S := by
  have hUnit : ∀ k : Sym2 P, ¬ k.IsDiag → ∃ s : PairSource P,
      ‖s.vector‖ = 1 ∧
      (Fintype.card s.leftBasis = 1 ∧ Fintype.card s.rightBasis = 1) ∧
      s.partyPair = k ∧ ∀ T : SourceInventory P, Expands (s :: T) T := by
    intro k
    induction k using Sym2.inductionOn with
    | hf p q =>
        intro h
        have hpq : p ≠ q := fun he ↦ h (Sym2.mk_isDiag_iff.mpr he)
        exact ⟨PairSource.unit p q hpq, PairSource.norm_unit_vector _ _ _,
          PairSource.card_unit_bases _ _ _, rfl, Expands.unit_cons hpq⟩
  obtain ⟨U, hU, hUS, hUN, hUK, hUE⟩ :=
    exists_extension_covering (Finset.univ : Finset (Sym2 P)).toList S hS hN hUnit
  refine ⟨U, ?_, hUS, hUN, ?_, hUE⟩
  · intro s hs
    exact ⟨(hU s hs).1, (hU s hs).2,
      List.disjoint_left.mp (List.disjoint_of_nodup_append
        (by simpa only [List.map_append] using hUN)) (List.mem_map.mpr ⟨s, hs, rfl⟩)⟩
  · intro k
    refine ⟨?_, hUK k (by simp)⟩
    intro hk h
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hk
    exact s.distinct (Sym2.mk_isDiag_iff.mp h)

/-- Every grouped normalized inventory admits normalized sources on exactly all unordered pairs
of distinct parties; allowed source-free operations recover its preparation for every spectator
system. Source: `eq:compression-source-gate`, `04-compression.tex`, lines 243–245. -/
theorem exists_complete (S : SourceInventory P) (hS : S.IsNormalized)
    (hN : (S.map PairSource.partyPair).Nodup) :
    ∃ T : SourceInventory P, T.IsNormalized ∧ (T.map PairSource.partyPair).Nodup ∧
      (∀ k, k ∈ T.map PairSource.partyPair ↔ ¬ k.IsDiag) ∧ T.Expands S := by
  obtain ⟨U, _, hUS, hUN, hUK, hUE⟩ := exists_complete_extension S hS hN
  exact ⟨U ++ S, hUS, hUN, hUK, hUE⟩

end SourceInventory

end QuantumCircuit.Party
