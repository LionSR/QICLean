/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellPinnedProductAction
import QICLean.Representation.ReplicaSymmetricBandCommute
import QICLean.Representation.RegionalReplicaMetricRegions

/-!
# Bell restriction in fixed symmetric coordinates

Fix one isometry onto the simultaneous symmetric space. Each original band
factor is compressed by this same isometry, and the same weighted mean tree
is evaluated in every band. Their ordered product is the matrix used in the
lower norm bounds. Its powers agree with the exterior product through the
actual Bell-inserted symmetric operator. All replica weights belong to the
original full family.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 80–110, 299–308 and
  370–381, `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation FiniteProduct
open scoped InnerProductSpace ComplexOrder MatrixOrder
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ιe" => compressedSiteSpace β X R

local instance bellPinnedCompressedPowersConfigDecidableEq (k : ℕ) : DecidableEq (Config k ι₀) :=
  Fintype.decidablePiFintype

/-- The ordered product of the actual compressed band means is positive
and its real powers intertwine with the exterior product through the Bell
operator. The same supplied symmetric coordinates are retained throughout.
The inserted vector is arbitrary; it need not be a unit vector.

Source: area-law manuscript, `07-comparators.tex`, lines 80–110, 299–308
and 370–381, `comparator:pinned-metric`. -/
theorem replicaMetric_compressed_bandProduct_bellPin_rpow {S : Type*}
    [∀ v, Nonempty (ι₀ v)] (k n : ℕ) (Z : Matrix (Config k ι₀) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj (copyPerm ((v : Option (Option V)) → ι₀ v) k))
    {t : ℝ} (ht : 0 ≤ t) (K : ℕ) (U Y : S → Fin K → Finset V)
    (hdisj : ∀ j g, Disjoint (U j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h)
    (b : (Configuration β X × C) → ℂ) (T : Matrix.MeanTree S) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe (Configuration β X × C) k b).submatrix e id
    let Pe := symProj (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k)
    let P := J * Pe * Jᴴ
    let W := replicaMetric ι₀ t k
    let Q := fun j g ↦ insert (some none)
      ((X ∪ U j g).image fun v ↦ some (some v))
    let F := fun j g ↦ insert none
      (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
    let E := fun B : Finset V ↦ (B \ X).image fun v ↦ some (some v)
    let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (E (Y j g))) ^ 2
    let D := fun j g ↦ ((W (E (U j g)))⁻¹ *
      (W (E (U j g ∪ Y j g)))⁻¹ * W (E (Y j g))) ^ 2
    let B := fun j g ↦ Zᴴ * A j g * Z
    let M := (List.ofFn fun g ↦ T.eval (B · g)).prod
    let N := (List.ofFn fun g ↦ T.eval (D · g)).prod
    M.PosDef ∧ ∀ s : ℝ, (Z * M ^ s * Zᴴ) * P = P * N ^ s := by
  classical
  done

end TensorPower
