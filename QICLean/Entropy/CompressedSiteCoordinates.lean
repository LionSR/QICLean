/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sets

/-!
# The compressed site family and physical regions

One auxiliary coordinate accompanies the original physical coordinates
outside a region X. A physical region is represented by its remaining sites;
the auxiliary site never belongs to that region. These definitions make no
reference to a state, spectral selection, or marginal.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–247 and 283–308,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The additional site carries the compressed index; all other sites retain
their original physical coordinate spaces. -/
def compressedSiteSpace (β : V → Type u) (X : Finset V) (R : Type u) :
    Option ↥(Xᶜ) → Type u
  | none => R
  | some v => β v

instance (β : V → Type u) (X : Finset V) (R : Type u)
    [∀ v, Fintype (β v)] [Fintype R] (f : Option ↥(Xᶜ)) :
    Fintype (compressedSiteSpace β X R f) := by
  cases f <;> dsimp [compressedSiteSpace] <;> infer_instance

instance (β : V → Type u) (X : Finset V) (R : Type u)
    [∀ v, DecidableEq (β v)] [DecidableEq R] (f : Option ↥(Xᶜ)) :
    DecidableEq (compressedSiteSpace β X R f) := by
  cases f <;> dsimp [compressedSiteSpace] <;> infer_instance

/-- A physical region, regarded as a region of the exterior site family. -/
def exteriorRegion (X B : Finset V) : Finset (Option ↥(Xᶜ)) := by
  classical
  exact Finset.univ.filter fun f ↦ match f with
    | none => False
    | some v => (v : V) ∈ B

end FiniteProduct
