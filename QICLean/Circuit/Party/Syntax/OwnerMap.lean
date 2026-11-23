/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Gates

/-!
# Source inventories along a map of parties

Along a map of parties `f : P → Q`, a pair source keeps its fresh factors and its vector and
moves to the image parties when these differ (`PairSource.mapOwner`); a source whose endpoints
have the same image becomes local and disappears from the inventory
(`SourceInventory.mapOwner`). The map `affectedOwner A` keeps each affected party as a party and
sends all others to one exterior party.

## Main definitions

* `QuantumCircuit.Party.PairSource.mapOwner`, `QuantumCircuit.Party.SourceInventory.mapOwner`.
* `QuantumCircuit.Party.affectedOwner`.

## Main results

* `QuantumCircuit.Party.SourceInventory.mem_mapOwner`,
  `QuantumCircuit.Party.SourceInventory.mapOwner_eq_nil_iff`,
  `QuantumCircuit.Party.SourceInventory.map_partyPair_mapOwner`.
* `QuantumCircuit.Party.SourceInventory.mem_mapOwner_affectedOwner`,
  `QuantumCircuit.Party.SourceInventory.map_partyPair_affectedOwner`,
  `QuantumCircuit.Party.SourceInventory.mapOwner_affectedOwner_eq_nil_iff`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 383–427.

Adapted from TNLean, `TNLean/Lattice/PartyCircuit/SourceOwnerMap.lean` and
`TNLean/Lattice/PartyCircuit/AffectedOwners.lean` at commit `ded76a266d` (Apache-2.0). Changes:
the factors of a source are finite basis types.
-/

namespace QuantumCircuit.Party

variable {P Q : Type} [DecidableEq Q]

/-- Retain a pair source exactly when its new owners differ. The halfspaces
and vector are unchanged. Sources whose owners merge become local preparations.
Source: Theorem 5.2, `04-compression.tex`, lines 383–427. -/
def PairSource.mapOwner (f : P → Q) (s : PairSource P) : Option (PairSource Q) :=
  if h : f s.left = f s.right then none else
    some ⟨f s.left, f s.right, h, s.leftBasis, s.rightBasis, s.vector⟩

namespace SourceInventory

/-- The ordered inventory of sources that remain nonlocal after grouping parties.
This records source occurrences, without combining newly coincident pairs.
Source: Theorem 5.2, `04-compression.tex`, lines 383–427. -/
def mapOwner (f : P → Q) (S : SourceInventory P) : SourceInventory Q :=
  S.filterMap (PairSource.mapOwner f)

@[simp] theorem mapOwner_nil (f : P → Q) : mapOwner f [] = [] := rfl

@[simp] theorem mapOwner_cons (f : P → Q) (s : PairSource P) (S : SourceInventory P) :
    mapOwner f (s :: S) =
      match s.mapOwner f with
      | none => mapOwner f S
      | some t => t :: mapOwner f S := by
  cases h : s.mapOwner f <;> simp [mapOwner, h]

@[simp] theorem mapOwner_append (f : P → Q) (S T : SourceInventory P) :
    mapOwner f (S ++ T) = mapOwner f S ++ mapOwner f T := List.filterMap_append

/-- Membership retains the complete original source data, with only its two
owners changed. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 383–427. -/
theorem mem_mapOwner (f : P → Q) (S : SourceInventory P) (t : PairSource Q) :
    t ∈ mapOwner f S ↔ ∃ s ∈ S, ∃ h : f s.left ≠ f s.right,
      t = ⟨f s.left, f s.right, h, s.leftBasis, s.rightBasis, s.vector⟩ := by
  simp only [mapOwner, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, ht⟩
    by_cases h : f s.left = f s.right
    · simp [PairSource.mapOwner, h] at ht
    · exact ⟨s, hs, h, (Option.some.inj (by simpa [PairSource.mapOwner, h] using ht)).symm⟩
  · rintro ⟨s, hs, h, rfl⟩
    exact ⟨s, hs, by simp [PairSource.mapOwner, h]⟩

/-- Every surviving source remains normalized because its vector is unchanged.
Source: Theorem 5.2, `04-compression.tex`, lines 383–427. -/
theorem IsNormalized.mapOwner {S : SourceInventory P} (hS : S.IsNormalized)
    (f : P → Q) : (mapOwner f S).IsNormalized := by
  intro t ht
  obtain ⟨s, hs, h, rfl⟩ := (mem_mapOwner f S t).mp ht
  exact hS s hs

/-- No pair sources remain exactly when every original source becomes internal
to one new party. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 409–427. -/
theorem mapOwner_eq_nil_iff (f : P → Q) (S : SourceInventory P) :
    mapOwner f S = [] ↔ ∀ s ∈ S, f s.left = f s.right := by
  simp [mapOwner, PairSource.mapOwner]

open Classical in
/-- The pair labels are exactly the non-diagonal images of the original labels,
with their occurrence order and multiplicity retained. Source: Theorem 5.2,
`04-compression.tex`, lines 383–427. -/
theorem map_partyPair_mapOwner (f : P → Q) (S : SourceInventory P) :
    (mapOwner f S).map PairSource.partyPair =
      (S.map PairSource.partyPair).filterMap
        (fun k ↦ if (Sym2.map f k).IsDiag then none else some (Sym2.map f k)) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    by_cases h : f s.left = f s.right
    all_goals simp [mapOwner_cons, PairSource.mapOwner, PairSource.partyPair, h, ih]

/-- A surviving pair is a non-diagonal image of an original pair. No injectivity
or distinctness of the original pair labels is required. Source: Theorem 5.2,
`04-compression.tex`, lines 383–427. -/
theorem mem_partyPair_mapOwner (f : P → Q) (S : SourceInventory P) (k : Sym2 Q) :
    k ∈ (mapOwner f S).map PairSource.partyPair ↔
      ¬k.IsDiag ∧ ∃ e ∈ S.map PairSource.partyPair, Sym2.map f e = k := by
  rw [map_partyPair_mapOwner, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hk⟩
    by_cases hd : (Sym2.map f e).IsDiag
    · simp [hd] at hk
    · have heq : Sym2.map f e = k := by simpa [hd] using hk
      exact ⟨heq ▸ hd, e, he, heq⟩
  · rintro ⟨hk, e, he, rfl⟩
    exact ⟨e, he, by simp [hk]⟩

end SourceInventory

/-- Keep each affected party as a distinct owner and identify all exterior
parties with `none`. Source: Theorem 5.2, `04-compression.tex`,
lines 409–417. -/
def affectedOwner (A : P → Bool) (p : P) : Option {p // A p = true} :=
  if h : A p = true then some ⟨p, h⟩ else none

/-- The common exterior owner consists exactly of the unaffected parties.
Source: Theorem 5.2, `04-compression.tex`, lines 409–417. -/
@[simp] theorem affectedOwner_eq_none (A : P → Bool) (p : P) :
    affectedOwner A p = none ↔ A p = false := by
  cases h : A p <;> simp [affectedOwner, h]

/-- Two parties acquire the same owner exactly when they were equal or both
were exterior. Source: Theorem 5.2, `04-compression.tex`,
lines 409–417. -/
theorem affectedOwner_eq_iff (A : P → Bool) (p q : P) :
    affectedOwner A p = affectedOwner A q ↔
      p = q ∨ (A p = false ∧ A q = false) := by
  by_cases hp : A p = true <;> by_cases hq : A q = true <;>
    simp_all only [Bool.not_eq_true, affectedOwner, ↓reduceDIte, Option.some.injEq,
      Subtype.ext_iff, Bool.true_eq_false, Bool.false_eq_true, reduceCtorEq,
      and_self, and_true, and_false, or_false, or_true, false_iff]
  all_goals rintro rfl; simp_all

/-- A source survives exactly when at least one endpoint is affected. This
includes every corrected pair with two affected endpoints, as well as every
pair crossing to the exterior. Source: Theorem 5.2, `04-compression.tex`,
lines 383–417. -/
theorem PairSource.affectedOwner_ne_iff (A : P → Bool) (s : PairSource P) :
    affectedOwner A s.left ≠ affectedOwner A s.right ↔
      A s.left = true ∨ A s.right = true := by
  rw [ne_eq, affectedOwner_eq_iff]
  cases A s.left <;> simp [s.distinct]

variable [DecidableEq P]

namespace SourceInventory

/-- The surviving occurrences are exactly the original sources with at least
one affected endpoint, with their halfspaces and vectors unchanged. Source: Theorem 5.2,
`04-compression.tex`, lines 383–417. -/
theorem mem_mapOwner_affectedOwner (A : P → Bool) (S : SourceInventory P)
    (t : PairSource (Option {p // A p = true})) :
    t ∈ mapOwner (affectedOwner A) S ↔
      ∃ s ∈ S, ∃ h : A s.left = true ∨ A s.right = true,
        t = ⟨affectedOwner A s.left, affectedOwner A s.right,
          (s.affectedOwner_ne_iff A).mpr h, s.leftBasis, s.rightBasis, s.vector⟩ := by
  rw [mem_mapOwner]
  constructor
  · rintro ⟨s, hs, h, rfl⟩
    exact ⟨s, hs, (s.affectedOwner_ne_iff A).mp h, rfl⟩
  · rintro ⟨s, hs, h, rfl⟩
    exact ⟨s, hs, (s.affectedOwner_ne_iff A).mpr h, rfl⟩

/-- The ordered pair labels are obtained by retaining exactly the occurrences
with an affected endpoint. This list identity retains multiplicities, even when
different original pairs acquire the same new pair label. Source: Theorem 5.2,
`04-compression.tex`, lines 383–417. -/
theorem map_partyPair_affectedOwner (A : P → Bool) (S : SourceInventory P) :
    (mapOwner (affectedOwner A) S).map PairSource.partyPair =
      (S.filter (fun s ↦ A s.left || A s.right)).map
        (fun s ↦ Sym2.map (affectedOwner A) s.partyPair) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    cases hl : A s.left <;> cases hr : A s.right <;>
      simp [mapOwner_cons, PairSource.mapOwner, affectedOwner_eq_iff,
        s.distinct, hl, hr, ih, PairSource.partyPair]

/-- No pair sources survive exactly when both endpoints of each original
source are exterior. Source: Theorem 5.2, `04-compression.tex`,
lines 409–417. -/
theorem mapOwner_affectedOwner_eq_nil_iff (A : P → Bool) (S : SourceInventory P) :
    mapOwner (affectedOwner A) S = [] ↔
      ∀ s ∈ S, A s.left = false ∧ A s.right = false := by
  rw [mapOwner_eq_nil_iff]
  exact forall₂_congr fun s _ ↦ by simp [affectedOwner_eq_iff, s.distinct]

end SourceInventory

end QuantumCircuit.Party
