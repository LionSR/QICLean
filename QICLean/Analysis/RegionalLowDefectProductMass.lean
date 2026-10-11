/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RegionalLowDefectMass
import QICLean.Representation.ReplicaSymmetricBandLabelPreservation
import QICLean.Representation.RegionalReplicaMetricRegions

/-!
# Actual defect mass for the common-tree product of band roots

The comparator uses one weighted tree for every band. Its product of band
roots is exactly the mean of the original ordered leaf products in the
same symmetric coordinates. The original gap therefore gives the cutoff
mass of its actual normalized inverse-power vector. The actual excess
energy is nonnegative, as follows from this gap estimate and the upper
bound one for the mass of an orthogonal projection.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 114–121 and 421–443,
  `comparator:defect-mass`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u v

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (C R : Type u)
variable [∀ x, Fintype (β x)] [∀ x, DecidableEq (β x)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R

local instance regionalLowDefectProductMass_decidableEqPhysical :
    DecidableEq ((x : V) → β x) := Fintype.decidablePiFintype

local instance regionalLowDefectProductMass_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι₀) := Fintype.decidablePiFintype

/-- The actual product of the same-tree band roots has nonnegative excess
energy and the original common-cutoff mass bound. The vector, its two
original labels, and the fixed symmetric coordinates remain unchanged.
The cutoff parameter may be chosen after the normalized vector; neither
a mass inequality nor nonnegativity of the energy deficit is a premise. -/
theorem replicaMetric_normalized_symProj_bandProduct_lowDefect_mass_ge
    [∀ x, Nonempty (ι₀ x)]
    {H : Matrix ((x : V) → β x) ((x : V) → β x) ℂ}
    {Ω : ((x : V) → β x) → ℂ} {E₀ gap : ℝ}
    (hgap : (H - (E₀ : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (hgap_pos : 0 < gap)
    (k n : ℕ) (hk : 0 < k) (Z : Matrix (Config k ι₀) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj (copyPerm ((x : Option (Option V)) → ι₀ x) k))
    {t : ℝ} (ht : 0 ≤ t) {J : Type v} (G : ℕ)
    (Q Y : J → Fin G → Finset V)
    (hdisj : ∀ j g, Disjoint (Q j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → Q j g ∪ Y j g ⊆ Q j' h)
    (T : MeanTree J)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k)))
    (s : ℝ) (ξ : EuclideanSpace ℂ (Config k ι₀)) (hξ : ξ ≠ 0)
    (hsym : symProj (copyPerm ((x : Option (Option V)) → ι₀ x) k) *ᵥ ξ = ξ)
    (hC : labelProj (subsystemPerm k ι₀ {some none}) ellC *ᵥ ξ = ξ)
    (hR : labelProj (subsystemPerm k ι₀ {none}) ellR *ᵥ ξ = ξ) :
    let W := replicaMetric ι₀ t k
    let L := fun j g => insert (some none) ((Q j g).image fun x => some (some x))
    let F := fun j g => insert none
      (((Q j g ∪ Y j g)ᶜ).image fun x => some (some x))
    let E := fun j g => (Y j g).image fun x => some (some x)
    let A := fun j g => ((W (L j g))⁻¹ * (W (F j g))⁻¹ * W (E j g)) ^ 2
    let B := fun j g => Zᴴ * A j g * Z
    let M := (List.ofFn fun g => T.eval (B · g)).prod
    let w := toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ ξ)
    let φ := (‖w‖⁻¹ : ℂ) • w
    let v := toEuclideanLin Z φ
    let δ := ((star v ⬝ᵥ (globalReplicaMeanHamiltonian β C R H k *ᵥ v)).re - E₀) / gap
    M.PosDef ∧ w ≠ 0 ∧ ‖φ‖ = 1 ∧ ‖v‖ = 1 ∧ 0 ≤ δ ∧
      ∀ τ : ℝ, 0 < τ →
        let P := Zᴴ * globalReplicaLowDefectProjection β C R Ω k ellC ellR τ * Z
        IsStarProjection P ∧ 1 - δ / τ ≤ (star φ ⬝ᵥ (P *ᵥ φ)).re := by
  intro W L F E A B M w φ v δ
  obtain ⟨hLE, hfar, hnestL⟩ :
      (∀ j g, Disjoint (L j g) (E j g)) ∧
        (∀ j g, F j g = (L j g ∪ E j g)ᶜ) ∧
          ∀ j j' g h, g < h → L j g ∪ E j g ⊆ L j' h :=
    replicaMetric_lifted_region_geometry G Q Y hdisj hnest
  done

end Matrix
