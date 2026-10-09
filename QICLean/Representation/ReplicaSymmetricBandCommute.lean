/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.IsometricIntertwiningCommute
import QICLean.Analysis.PositiveProjectionCompression
import QICLean.Representation.ReplicaLaminarBandMetrics
import QICLean.Analysis.OperatorMean.FiniteTree

/-!
# Cross-band commutation in fixed symmetric coordinates

The original band factors have positive compressions on the full copy
symmetric space. Cross-status nesting implies commutation of the compressed
factors from distinct bands. Consequently their weighted mean roots
commute, with the same fixed coordinate isometry for every band and tree.

The far-region metric is the original metric on the complement of the
near and middle regions. Its replacement by a laminar factor is derived
on the symmetric space. Every label weight retains the original full
system dimension.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  `06-transport.tex`, `transport:means` and lines 268–276;
  `07-comparators.tex`, `comparator:nesting`, `comparator:metrics`,
  lines 20–37 and 80–110, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
variable (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]
variable {J : Type*}

local instance replicaSymmetricBandCommuteConfigDecidableEq (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual original band factors have positive definite compressions
in any fixed isometric coordinates on the simultaneous symmetric space.
Their compressions commute across distinct bands, as a consequence of the
original cross-status nesting. No commutation premise is required.

Source: area-law manuscript, `06-transport.tex`, lines 268–276;
`07-comparators.tex`, `comparator:nesting` and `comparator:metrics`,
lines 20–37 and 80–110. -/
theorem replicaMetric_symProj_compressions_posDef_commute
    (k n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj (copyPerm ((f : F) → ι f) k))
    {t : ℝ} (ht : 0 ≤ t) (K : ℕ)
    (Q Y : J → Fin K → Finset F)
    (hdisj : ∀ j g, Disjoint (Q j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → Q j g ∪ Y j g ⊆ Q j' h) :
    let A := fun j g ↦ ((replicaMetric ι t k (Q j g))⁻¹ *
      (replicaMetric ι t k (Q j g ∪ Y j g)ᶜ)⁻¹ *
        replicaMetric ι t k (Y j g)) ^ 2
    let D := fun j g ↦ ((replicaMetric ι t k (Q j g))⁻¹ *
      (replicaMetric ι t k (Q j g ∪ Y j g))⁻¹ *
        replicaMetric ι t k (Y j g)) ^ 2
    let B := fun j g ↦ Zᴴ * A j g * Z
    (∀ j g, (B j g).PosDef ∧ A j g * Z = Z * B j g ∧
      D j g * Z = Z * B j g) ∧
      ∀ j j' g h, g ≠ h → Commute (B j g) (B j' h) := by
  intro A D B
  obtain ⟨hD, hcomm⟩ :=
    replicaPinnedBands_posDef_commute ι ht k K Q Y hdisj hnest
  have hleaf (j : J) (g : Fin K) :
      (B j g).PosDef ∧ A j g * Z = Z * B j g ∧
        D j g * Z = Z * B j g := by
    obtain ⟨_, hDP, hAP⟩ := replicaMetric_factors_symProj ι ht k (Q j g) (Y j g)
    exact ((hD j g).compression_of_projection_intertwine hZ hZZ hAP hDP).2
  refine ⟨hleaf, ?_⟩
  intro j j' g h hgh
  exact Matrix.commute_of_isometric_intertwine hZ
    (hleaf j g).2.2 (hleaf j' h).2.2 (hcomm j j' g h hgh)

/-- Mean roots of distinct actual compressed bands commute in the same
fixed symmetric coordinates. The trees may differ; repeated terminal
labels and zero edge weights are allowed.

Source: area-law manuscript, `06-transport.tex`, `transport:means`
and lines 268–276; `07-comparators.tex`, `comparator:nesting`. -/
theorem replicaMetric_symProj_meanTree_roots_commute
    (k n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj (copyPerm ((f : F) → ι f) k))
    {t : ℝ} (ht : 0 ≤ t) (K : ℕ)
    (Q Y : J → Fin K → Finset F)
    (hdisj : ∀ j g, Disjoint (Q j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → Q j g ∪ Y j g ⊆ Q j' h) :
    let A := fun j g ↦ ((replicaMetric ι t k (Q j g))⁻¹ *
      (replicaMetric ι t k (Q j g ∪ Y j g)ᶜ)⁻¹ *
        replicaMetric ι t k (Y j g)) ^ 2
    let B := fun j g ↦ Zᴴ * A j g * Z
    (∀ (g : Fin K) (T : Matrix.MeanTree J), (T.eval (B · g)).PosDef) ∧
      ∀ (g h : Fin K), g ≠ h → ∀ T T' : Matrix.MeanTree J,
        Commute (T.eval (B · g)) (T'.eval (B · h)) := by
  intro A B
  obtain ⟨hleaf, hcomm⟩ :=
    replicaMetric_symProj_compressions_posDef_commute ι k n Z hZ hZZ ht K Q Y hdisj hnest
  refine ⟨fun g T ↦ Matrix.MeanTree.posDef_eval (fun j ↦ (hleaf j g).1) T, ?_⟩
  intro g h hgh T T'
  exact Matrix.MeanTree.commute_eval_eval (fun j ↦ (hleaf j g).1)
    (fun j ↦ (hleaf j h).1) (fun j j' ↦ hcomm j j' g h hgh) T T'

end TensorPower
