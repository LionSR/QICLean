/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RegionalLowDefectProductMass
import QICLean.Analysis.RegionalLowDefectLowerPin
import QICLean.Analysis.MeanTreeExponentialLowerNorm
import QICLean.Representation.ReplicaSymmetricMetricFloor
import QICLean.Representation.RegionalReplicaMetricRegions

/-!
# An explicit rough lower norm bound in the original physical coordinates

The original regional lower bound, the uniform symmetric floor and the
original physical gap give a lower norm estimate for the same normalized
inverse-power vector. Its remainder is independent of terminal weights
and excess energy. Neither a final mass estimate nor a final lower bound
is a premise.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 97--169 and 585--651,
`comparator:rough-lower`, revision
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

local instance regionalRoughLowerNorm_decidableEqPhysical :
    DecidableEq ((x : V) → β x) := Fintype.decidablePiFintype

local instance regionalRoughLowerNorm_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι₀) := Fintype.decidablePiFintype

variable [∀ x, Nonempty (β x)] [Nonempty C] [Nonempty R]

/-- An explicit rough lower norm estimate for the actual common-tree
band product. The constants precede all state, copy, label, tree and
coordinate data. The original unit state and gap give the mass of the
same normalized vector used by the logarithmic comparison.
Source: `07-comparators.tex`, `comparator:rough-lower`, lines 153--169
and 585--651. -/
theorem exists_replicaMetric_symProj_bandProduct_rough_lower_norm
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
    ∃ c Cf : ℝ, 0 ≤ c ∧ 0 ≤ Cf ∧
      ∀ (k n : ℕ), 0 < k →
      ∀ (H : Matrix ((x : V) → β x) ((x : V) → β x) ℂ)
        (Ω : ((x : V) → β x) → ℂ) (E₀ gap : ℝ),
      (H - (E₀ : ℂ) • 1 -
        (gap : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef →
      ‖WithLp.toLp 2 Ω‖ = 1 → 0 < gap →
      ∀ (Z : Matrix (Config k ι₀) (Fin n) ℂ),
      Zᴴ * Z = 1 →
      Z * Zᴴ = symProj (copyPerm ((x : Option (Option V)) → ι₀ x) k) →
      ∀ (J : Type v) [Fintype J] [DecidableEq J] (G : ℕ)
        (Q Y : J → Fin G → Finset V),
      (∀ j g, Disjoint (Q j g) (Y j g)) →
      (∀ j j' g h, g < h → Q j g ∪ Y j g ⊆ Q j' h) →
      ∀ (T : MeanTree J) (ellC ellR : IrrepLabel (Equiv.Perm (Fin k)))
        (S ε s : ℝ),
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      0 ≤ s →
      ∀ ξ : EuclideanSpace ℂ (Config k ι₀), ξ ≠ 0 → ‖ξ‖ ≤ 1 →
      symProj (copyPerm ((x : Option (Option V)) → ι₀ x) k) *ᵥ ξ = ξ →
      labelProj (subsystemPerm k ι₀ {some none}) ellC *ᵥ ξ = ξ →
      labelProj (subsystemPerm k ι₀ {none}) ellR *ᵥ ξ = ξ →
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
      let d := Real.log (Fintype.card C) + Real.log (Fintype.card R)
      let r := Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) + 2 * t * ε
      let b := ((k : ℝ) + 2) ^ (-Cf) / 2
      w ≠ 0 ∧ ‖v‖ = 1 ∧ 0 ≤ δ ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
          let rate := 2 * S - τ * d - (3 + 1 / (2 * t)) * Real.binEntropy τ
          2 * s * (G : ℝ) *
            (2 * t * (k : ℝ) * (rate - δ / τ * max 0 (2 * S)) -
              (2 * |r| + |Real.log b| + Real.log 2 + Real.log (3 / 2))) ≤
            -Real.log (‖w‖ ^ 2) := by
  obtain ⟨c, hc, hlower⟩ :=
    exists_globalReplicaLowDefectProjection_rough_lower_pin β C R ht htsmall
  let : ∀ x, Nonempty (ι₀ x) := fun
    | none => ‹Nonempty R›
    | some none => ‹Nonempty C›
    | some (some x) => ‹∀ x, Nonempty (β x)› x
  obtain ⟨Cf, hCf, hfloor⟩ := exists_replicaMetric_symProj_isometric_floor ι₀ ht
  refine ⟨c, Cf, hc, hCf, ?_⟩
  intro k n hk H Ω E₀ gap hgap hΩ hgap_pos Z hZ hZZ J _ _ G Q Y hdisj hnest
    T ellC ellR S ε s hlabel hs ξ hξ hξnorm hsym hC hR W L F E A B M w φ v δ d r b
  obtain ⟨hM, hw, hφ, hv, hδ, hmass⟩ :
      M.PosDef ∧ w ≠ 0 ∧ ‖φ‖ = 1 ∧ ‖v‖ = 1 ∧ 0 ≤ δ ∧
        ∀ τ : ℝ, 0 < τ →
          let P := Zᴴ * globalReplicaLowDefectProjection β C R Ω k ellC ellR τ * Z
          IsStarProjection P ∧ 1 - δ / τ ≤ (star φ ⬝ᵥ (P *ᵥ φ)).re :=
    replicaMetric_normalized_symProj_bandProduct_lowDefect_mass_ge
      β C R hgap hΩ hgap_pos k n hk Z hZ hZZ ht.le
      G Q Y hdisj hnest T ellC ellR s ξ hξ hsym hC hR
  refine ⟨hw, hv, hδ, fun τ hτ hτhalf ↦ ?_⟩
  intro rate
  obtain ⟨hLE, hfar, hnestL⟩ :
      (∀ j g, Disjoint (L j g) (E j g)) ∧
        (∀ j g, F j g = (L j g ∪ E j g)ᶜ) ∧
          ∀ j j' g h, g < h → L j g ∪ E j g ⊆ L j' h :=
    replicaMetric_lifted_region_geometry G Q Y hdisj hnest
  have hB (j : J) (g : Fin G) : (B j g).PosDef := by
    simpa only [B, A, W, hfar] using
      ((replicaMetric_symProj_compressions_posDef_commute
        ι₀ k n Z hZ hZZ ht.le G L E hLE hnestL).1 j g).1
  have hcomm (g h : Fin G) (hgh : g ≠ h) :
      Commute (T.eval (B · g)) (T.eval (B · h)) := by
    simpa only [B, A, W, hfar] using
      (replicaMetric_symProj_meanTree_roots_commute
        ι₀ k n Z hZ hZZ ht.le G L E hLE hnestL).2 g h hgh T T
  have hfloorB (j : J) (g : Fin G) :
      (2 * b) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B j g := by
    simpa only [b, mul_div_cancel₀ _ (two_ne_zero : (2 : ℝ) ≠ 0), B, A, W,
      (regionalOriginalRegion_metric_regions (Q j g) (Y j g) (hdisj j g)).1,
      (regionalOriginalRegion_metric_regions (Q j g) (Y j g) (hdisj j g)).2.1,
      (regionalOriginalRegion_metric_regions (Q j g) (Y j g) (hdisj j g)).2.2] using
      (hfloor k _ _ _
        (regionalOriginalRegion_metric_partition (Q j g) (Y j g)).1
        (regionalOriginalRegion_metric_partition (Q j g) (Y j g)).2.1
        (regionalOriginalRegion_metric_partition (Q j g) (Y j g)).2.2.1
        (regionalOriginalRegion_metric_partition (Q j g) (Y j g)).2.2.2 n Z hZ hZZ).2
  have hpin_original :=
    (hlower k Ω hΩ ellC ellR τ S ε hτ.le hτhalf hlabel n Z hZZ).2
  let pinCoeff := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) *
    (((k : ℝ) + 2) ^ c * Real.exp
      (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) + (2 * t) * ε))
  have hpinB (j : J) (g : Fin G) :
      pinCoeff⁻¹ • (Zᴴ * globalReplicaLowDefectProjection β C R Ω k ellC ellR τ * Z) ≤
        B j g := by
    simpa only [pinCoeff, d, B, A, W,
      (regionalOriginalRegion_metric_regions (Q j g) (Y j g) (hdisj j g)).1,
      (regionalOriginalRegion_metric_regions (Q j g) (Y j g) (hdisj j g)).2.1,
      (regionalOriginalRegion_metric_regions (Q j g) (Y j g) (hdisj j g)).2.2] using
      hpin_original (Q j g) (Y j g) (hdisj j g)
  have hpinCoeff : 0 < pinCoeff := by positivity
  have hlog : Real.log pinCoeff = r - 2 * t * (k : ℝ) * rate := by
    simp (disch := positivity) only
      [pinCoeff, Real.log_mul, Real.log_exp, Real.log_rpow, r, rate]
    field_simp [ht.ne']
    ring
  done

end Matrix
