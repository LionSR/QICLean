/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellPinnedCompressedPowers
import QICLean.Analysis.ProjectionIntertwiningNorm
import QICLean.Representation.BellSymmetricPinProjection
import QICLean.Representation.ReplicaSymmetricBandCommute
import QICLean.Representation.RegionalReplicaMetricRegions

/-!
# Inverse powers in the supplied symmetric coordinates

The inverse-power cutoff estimate for the exterior replica metric is
transferred to the actual compressed band product. The same supplied
isometry is used in both the matrix and the vector. All weights belong to
the original full family, and the polynomial constant is uniform before
the copy number, regions, tree, cutoff and vectors are specified.

The estimate is stated for a supplied unit test vector satisfying the
actual exterior cutoffs and a supplied unit inserted vector. Its application
to the selected physical state must derive these conditions separately.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 299–308 and 370–381,
`comparator:pinned-metric`, revision
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

local instance bellCompressedInverseNormConfigDecidableEq (k : ℕ) : DecidableEq (Config k ι₀) :=
  Fintype.decidablePiFintype

/-- The cutoff inverse-norm estimate in the same supplied symmetric
coordinates as the lower bound. The original full-family weights are
retained. Source: area-law manuscript, `07-comparators.tex`, lines 299–308
and 370–381, `comparator:pinned-metric`. -/
theorem exists_replicaMetric_compressed_bell_inverse_norm_bound {S : Type*}
    [Finite S] [∀ v, Nonempty (ι₀ v)] {t : ℝ} (ht : 0 < t) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (k n : ℕ) (Z : Matrix (Config k ι₀) (Fin n) ℂ),
      Zᴴ * Z = 1 →
      Z * Zᴴ = symProj (copyPerm ((v : Option (Option V)) → ι₀ v) k) →
      ∀ (K : ℕ) (U Y : S → Fin K → Finset V),
      (∀ j g, Disjoint (U j g) (Y j g)) →
      (∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) →
      ∀ b : (Configuration β X × C) → ℂ, ‖WithLp.toLp 2 b‖ = 1 →
      ∀ (T : Matrix.MeanTree S) (a : ℝ) (φ u : EuclideanSpace ℂ (Config k ι₀)),
      ‖φ‖ = 1 →
      let E := fun B : Finset V ↦ (B \ X).image fun v ↦ some (some v)
      (∀ j g,
        toEuclideanLin (labelCutoff (subsystemPerm k ι₀ (E (U j g))) a) φ = φ ∧
        toEuclideanLin (labelCutoff (subsystemPerm k ι₀ (E (U j g ∪ Y j g))) a) φ = φ) →
      ∀ s : ℝ, 2 * s ∈ Set.Icc (0 : ℝ) 1 →
      let e := bellInsertionCopyEquiv β X C R k
      let J := (addedSiteInsertion ιe (Configuration β X × C) k b).submatrix e id
      let Pe := symProj (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k)
      let P := J * Pe * Jᴴ
      let W := replicaMetric ι₀ t k
      let Q := fun j g ↦ insert (some none)
        ((X ∪ U j g).image fun v ↦ some (some v))
      let F := fun j g ↦ insert none
        (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
      let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (E (Y j g))) ^ 2
      let B := fun j g ↦ Zᴴ * A j g * Z
      let M := (List.ofFn fun g ↦ T.eval (B · g)).prod
      ‖inner ℂ φ (toEuclideanLin P u)‖ ^ 2 ≤
        (((k : ℝ) + 2) ^ (c * (K : ℝ)) * Real.exp (4 * t * (K : ℝ) * a)) ^
          (2 * s) * ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ u)‖ ^ 2 := by
  classical
  obtain ⟨c, hc, hC⟩ := exists_replicaPinnedTree_inverse_norm_bound (J := S) ι₀ ht
  refine ⟨c, hc, fun k n Z hZ hZZ K U Y hdisj hnest b hb T a φ u hφ ↦ ?_⟩
  done

end TensorPower
