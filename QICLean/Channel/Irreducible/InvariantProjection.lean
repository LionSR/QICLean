/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Hermitian.OrthogonalProjection
import QICLean.Channel.FixedPoint.Stationary.SupportInvariance
import QICLean.Channel.Irreducible.Basic
import QICLean.Kraus.Word

/-!
# Invariant orthogonal projections for finite matrix families

A finite family of square matrices is irreducible when it has no nontrivial
invariant subspace. In finite dimension, this is equivalent to the absence of
a nontrivial invariant orthogonal projection.

## Main declarations

* `Kraus.HasInvariantProj` states that a finite matrix family has a nontrivial
  invariant orthogonal projection.
* `Kraus.IsIrreducibleFamily` states that no such projection exists.
* `Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily` shows that an irreducible
  family defines an irreducible Kraus map.
* `Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM` proves the converse.
* `Kraus.hasInvariantProj_reindexPhysical_equiv` and
  `Kraus.isIrreducibleFamily_reindexPhysical_equiv`: both notions are invariant under
  relabelling the index set.
-/

namespace Kraus

variable {ι : Type*} {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite matrix family has a nontrivial invariant orthogonal projection if there is a
Hermitian idempotent $P$, distinct from $0$ and $1$, such that
$(1-P)K_iP=0$ for every family index $i$. -/
def HasInvariantProj (K : ι → Matrix n n ℂ) : Prop :=
  ∃ P : Matrix n n ℂ,
    IsOrthogonalProjection P ∧ P ≠ 0 ∧ P ≠ 1 ∧ (∀ i : ι, (1 - P) * K i * P = 0)

/-- A finite matrix family is irreducible if it has no nontrivial invariant orthogonal
projection. -/
def IsIrreducibleFamily (K : ι → Matrix n n ℂ) : Prop :=
  ¬ HasInvariantProj K

variable [Fintype ι] {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A finite matrix family with no nontrivial invariant orthogonal projection defines an
irreducible Kraus map. -/
theorem isIrreducibleMap_mapLM_of_isIrreducibleFamily
    (K : ι → Mat) (hIrr : IsIrreducibleFamily K) :
    IsIrreducibleMap (mapLM K) := by
  intro P hProj hInv
  have hLower : ∀ i : ι, (1 - P) * K i * P = 0 :=
    invariance_implies_lowerZero K P hProj fun X => by
      simpa only [mapLM_apply] using hInv X
  by_contra h_neither
  push Not at h_neither
  exact hIrr ⟨P, hProj, h_neither.1, h_neither.2, hLower⟩

/-- If the finite Kraus map is irreducible, then its matrix family has no nontrivial
invariant orthogonal projection. -/
theorem isIrreducibleFamily_of_isIrreducibleMap_mapLM
    (K : ι → Mat) (hIrr : IsIrreducibleMap (mapLM K)) :
    IsIrreducibleFamily K := by
  intro ⟨P, hProj, hP0, hP1, hLower⟩
  have hInv : ∀ X, P * mapLM K (P * X * P) * P = mapLM K (P * X * P) := fun X => by
    simpa only [mapLM_apply] using lowerZero_implies_invariance K P hProj hLower X
  exact (hIrr P hProj hInv).elim hP0 hP1

section Relabel

variable {ι ι' n : Type*} [Fintype n] [DecidableEq n]

/-- Relabelling the index set of a finite family by a bijection preserves invariant
projections. -/
theorem hasInvariantProj_reindexPhysical_equiv (e : ι' ≃ ι) (A : ι → Matrix n n ℂ) :
    HasInvariantProj (reindexPhysical e A) ↔ HasInvariantProj A := by
  constructor
  · rintro ⟨P, hPproj, hP0, hP1, hLower⟩
    refine ⟨P, hPproj, hP0, hP1, ?_⟩
    intro i
    simpa [reindexPhysical] using hLower (e.symm i)
  · rintro ⟨P, hPproj, hP0, hP1, hLower⟩
    exact ⟨P, hPproj, hP0, hP1, fun i => hLower (e i)⟩

/-- Relabelling the index set of a finite family by a bijection preserves irreducibility. -/
theorem isIrreducibleFamily_reindexPhysical_equiv (e : ι' ≃ ι) (A : ι → Matrix n n ℂ) :
    IsIrreducibleFamily (reindexPhysical e A) ↔ IsIrreducibleFamily A := by
  rw [IsIrreducibleFamily, IsIrreducibleFamily, hasInvariantProj_reindexPhysical_equiv e A]

end Relabel

end Kraus
