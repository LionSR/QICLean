/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.FiniteProduct
import QICLean.Analysis.ReplicaGoodConfigurationDensity
import QICLean.Representation.AddedSiteSpace

/-!
# Regional five-factor coordinates in one global replica space

A disjoint pair of physical regions determines the three physical factors
consisting of those regions and the complement of their union. The two
auxiliary spaces are unchanged. These coordinates identify the original
global configuration space with the five-factor configuration space used
for the component estimates.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 20--37, 80--110 and 421--456, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section

namespace FiniteProduct

variable {V : Type u} [Fintype V] [DecidableEq V] (β : V → Type u)

/-- The original physical configuration split into two disjoint regions
and the complement of their union. Source: `07-comparators.tex`, lines 20--37. -/
def regionalPhysicalEquiv (Q Y : Finset V) (hQY : Disjoint Q Y) :
    ((v : V) → β v) ≃ Configuration β Q ×
      (Configuration β Y × Configuration β (Q ∪ Y)ᶜ) :=
  (splitEquiv β Q).trans
    ((Equiv.refl _).prodCongr (complementUnionEquiv β Q Y hQY))

end FiniteProduct

namespace TensorPower

/-- Change only the one-copy physical coordinates, retaining both original
auxiliary copy registers. Source: `07-comparators.tex`, lines 421--456. -/
def replicaPhysicalCoordinateEquiv {A B C R : Type*} (e : A ≃ B) (k : ℕ) :
    (Fin k → A) × ((Fin k → C) × (Fin k → R)) ≃
      (Fin k → B) × ((Fin k → C) × (Fin k → R)) :=
  (Equiv.arrowCongr (Equiv.refl (Fin k)) e).prodCongr (Equiv.refl _)

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (C R : Type u)

/-- The three actual physical regions followed by the original auxiliary
spaces, in the order used by the component estimates. Source:
`07-comparators.tex`, lines 20--37 and 80--110. -/
def regionalFiveFactorSpace (Q Y : Finset V) : Fin 5 → Type u :=
  ![FiniteProduct.Configuration β Q, FiniteProduct.Configuration β Y,
    FiniteProduct.Configuration β (Q ∪ Y)ᶜ, C, R]

instance regionalFiveFactorSpaceFintype
    [∀ v, Fintype (β v)] [Fintype C] [Fintype R]
    (Q Y : Finset V) (f : Fin 5) : Fintype (regionalFiveFactorSpace β C R Q Y f) := by
  exact Fin.cases (inferInstanceAs (Fintype (FiniteProduct.Configuration β Q)))
    (Fin.cases (inferInstanceAs (Fintype (FiniteProduct.Configuration β Y)))
      (Fin.cases (inferInstanceAs (Fintype (FiniteProduct.Configuration β (Q ∪ Y)ᶜ)))
        (Fin.cases (inferInstanceAs (Fintype C))
          (Fin.cases (inferInstanceAs (Fintype R)) (fun i => Fin.elim0 i))))) f

instance regionalFiveFactorSpaceDecidableEq
    [∀ v, DecidableEq (β v)]
    [DecidableEq C] [DecidableEq R]
    (Q Y : Finset V) (f : Fin 5) : DecidableEq (regionalFiveFactorSpace β C R Q Y f) := by
  fin_cases f <;> dsimp only [regionalFiveFactorSpace] <;> infer_instance

instance regionalFiveFactorSpaceNonempty
    [∀ v, Nonempty (β v)] [Nonempty C] [Nonempty R]
    (Q Y : Finset V) (f : Fin 5) : Nonempty (regionalFiveFactorSpace β C R Q Y f) := by
  fin_cases f <;> dsimp only [regionalFiveFactorSpace] <;> infer_instance

/-- The same original physical-copy and auxiliary registers for every
regional cut. Source: `07-comparators.tex`, lines 80--110 and 421--456. -/
def globalReplicaCopiesEquiv (k : ℕ) :
    Config k (addedSiteSpace (addedSiteSpace β C) R) ≃
      (Fin k → (v : V) → β v) × ((Fin k → C) × (Fin k → R)) where
  toFun x := (fun j v => x j (some (some v)),
    (fun j => x j (some none), fun j => x j none))
  invFun x j o := match o with
    | none => x.2.2 j
    | some none => x.2.1 j
    | some (some v) => x.1 j v
  left_inv x := by
    funext j o
    cases o with
    | none => rfl
    | some o => cases o <;> rfl
  right_inv x := rfl

/-- The literal globalization equivalence for a regional cut. The
auxiliary registers and their order remain unchanged. Source:
`07-comparators.tex`, lines 20--37, 80--110 and 421--456. -/
def regionalFiveFactorCopyEquiv (Q Y : Finset V) (hQY : Disjoint Q Y) (k : ℕ) :
    Config k (addedSiteSpace (addedSiteSpace β C) R) ≃
      Config k (regionalFiveFactorSpace β C R Q Y) :=
  (globalReplicaCopiesEquiv β C R k).trans
    ((replicaPhysicalCoordinateEquiv (C := C) (R := R)
      (FiniteProduct.regionalPhysicalEquiv β Q Y hQY) k).trans
      (fiveFactorCopiesEquiv (regionalFiveFactorSpace β C R Q Y) k).symm)

end TensorPower
