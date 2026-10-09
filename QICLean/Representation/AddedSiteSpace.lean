/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaMetric

/-!
# A finite site family with one auxiliary site

The auxiliary coordinate occupies the additional element of an option type;
all original sites retain their original coordinate spaces. Iterating this
construction keeps the two original auxiliary registers distinct.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 20–37 and 283–308, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u v

noncomputable section

namespace TensorPower

variable {F : Type v}

/-- An added site and the original coordinate family.
Source: area-law manuscript, `07-comparators.tex`, lines 283–308. -/
def addedSiteSpace (ι : F → Type u) (A : Type u) : Option F → Type u
  | none => A
  | some f => ι f

instance (ι : F → Type u) (A : Type u) [∀ f, Fintype (ι f)] [Fintype A]
    (o : Option F) : Fintype (addedSiteSpace ι A o) := by
  cases o <;> dsimp [addedSiteSpace] <;> infer_instance

instance (ι : F → Type u) (A : Type u) [∀ f, DecidableEq (ι f)] [DecidableEq A]
    (o : Option F) : DecidableEq (addedSiteSpace ι A o) := by
  cases o <;> dsimp [addedSiteSpace] <;> infer_instance


end TensorPower
