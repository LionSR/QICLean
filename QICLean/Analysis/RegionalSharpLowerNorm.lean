/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RegionalLowDefectProductMass
import QICLean.Analysis.RegionalLowDefectLowerPin
import QICLean.Analysis.RegionalPhysicalMarginals
import QICLean.Analysis.MeanTreeExponentialLowerNorm
import QICLean.Representation.ReplicaSymmetricMetricFloor
import QICLean.Representation.RegionalReplicaMetricRegions

/-!
# An explicit sharp lower norm bound in the original physical coordinates

The sharp regional lower bound, the uniform symmetric floor and the
original physical gap give a lower norm estimate for the same normalized
inverse-power vector. Each entropy difference is computed from the actual
physical marginals. A finite maximum bounds these differences without a
positive number of bands. The polynomial constants precede the state,
region family and moment parameters. The actual defect mass is a conclusion
of the original gap and label conditions.
Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550--651, revision
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

local instance regionalSharpLowerNorm_decidableEqPhysical :
    DecidableEq ((x : V) → β x) := Fintype.decidablePiFintype

local instance regionalSharpLowerNorm_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι₀) := Fintype.decidablePiFintype

variable [∀ x, Nonempty (β x)] [Nonempty C] [Nonempty R]

open Classical in
/-- An explicit sharp lower norm estimate for the actual common-tree
band product. The moment assumptions concern the three original physical
reductions at each leaf. The same physical state determines the gap,
common defect projection and marginal entropies. The label-dimension
parameter remains separate from these marginal entropies.
Source: `07-comparators.tex`, lines 550--651. -/
theorem exists_replicaMetric_symProj_bandProduct_sharp_lower_norm
    {t : ℝ} (ht : 0 < t) :
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
      ∀ (K rMom : ℝ),
      (∀ (j : J) (g : Fin G) (a : Fin 3) (v : ℝ), |v| ≤ rMom →
        let U := FiniteProduct.regionalPhysicalRegion (Q j g) (Y j g) a
        Real.log (Entropy.surprisalMoment
          (FiniteProduct.reducedPure_posSemidef β (WithLp.toLp 2 Ω) U).isHermitian.eigenvalues v) ≤
            v * FiniteProduct.entropy β (WithLp.toLp 2 Ω) U + K * v ^ 2) →
      20 * t ≤ rMom → 20 * t ≤ 1 → 0 ≤ K →
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
      let entropyGap := fun j g =>
        FiniteProduct.entropy β (WithLp.toLp 2 Ω) (Q j g) +
          FiniteProduct.entropy β (WithLp.toLp 2 Ω) (Q j g ∪ Y j g)ᶜ -
          FiniteProduct.entropy β (WithLp.toLp 2 Ω) (Y j g)
      let gaps := (Finset.univ : Finset (J × Fin G)).image
        (fun p => entropyGap p.1 p.2)
      let gmax := (insert (0 : ℝ) gaps).max' (Finset.insert_nonempty _ _)
      let d := Real.log (Fintype.card C) + Real.log (Fintype.card R)
      let r := Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) + 2 * t * ε
      let b := ((k : ℝ) + 2) ^ (-Cf) / 2
      w ≠ 0 ∧ ‖v‖ = 1 ∧ 0 ≤ δ ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
          let rate := fun g => 2 * S +
            (1 - τ) * (∑ j, T.weight j * entropyGap j g) - τ * d -
              (3 + 1 / (2 * t)) * Real.binEntropy τ - 50 * K * t
          2 * s * (∑ g,
            (2 * t * (k : ℝ) * (rate g - δ / τ * max 0 (2 * S + gmax)) -
              (2 * |r| + |Real.log b| + Real.log 2 + Real.log (3 / 2)))) ≤
            -Real.log (‖w‖ ^ 2) := by
  obtain ⟨c, hc, hlower⟩ :=
    exists_globalReplicaLowDefectProjection_sharp_lower_pin β C R ht
  let : ∀ x, Nonempty (ι₀ x) := fun
    | none => ‹Nonempty R›
    | some none => ‹Nonempty C›
    | some (some x) => ‹∀ x, Nonempty (β x)› x
  obtain ⟨Cf, hCf, hfloor⟩ :=
    exists_replicaMetric_symProj_isometric_floor ι₀ ht
  refine ⟨c, Cf, hc, hCf, ?_⟩
  intro k n hk H Ω E₀ gap hgap hΩ hgap_pos Z hZ hZZ J _ _ G Q Y hdisj hnest
    K rMom hmoment htr htone hK T ellC ellR S ε s hlabel hs ξ hξ hξnorm hsym hC hR
    W L F E A B M w φ v δ entropyGap gaps gmax d r b
  obtain ⟨_, hw, _, hv, hδ, hmass⟩ :=
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
  let leafRate := fun (j : J) (g : Fin G) ↦
    2 * S + (1 - τ) * entropyGap j g - τ * d -
      (3 + 1 / (2 * t)) * Real.binEntropy τ - 50 * K * t
  let pinCoeff := fun (j : J) (g : Fin G) ↦
    ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) *
      (((k : ℝ) + 2) ^ c * Real.exp
        (-(k : ℝ) * (2 * t) *
          (2 * S + (1 - τ) * entropyGap j g - τ * d - 3 * Real.binEntropy τ) +
            (2 * t) * ε + 25 * (k : ℝ) * K * (2 * t) ^ 2))
  have hpinB (j : J) (g : Fin G) :
      (pinCoeff j g)⁻¹ •
        (Zᴴ * globalReplicaLowDefectProjection β C R Ω k ellC ellR τ * Z) ≤ B j g := by
    simpa only [pinCoeff, entropyGap, d, B, A, W,
      (regionalOriginalRegion_metric_regions (Q j g) (Y j g) (hdisj j g)).1,
      (regionalOriginalRegion_metric_regions (Q j g) (Y j g) (hdisj j g)).2.1,
      (regionalOriginalRegion_metric_regions (Q j g) (Y j g) (hdisj j g)).2.2] using
      (hlower k Ω hΩ ellC ellR τ S ε hτ.le hτhalf hlabel n Z hZZ).2
        (Q j g) (Y j g) (hdisj j g) K rMom (hmoment j g) htr htone hK
  have hpinCoeff (j : J) (g : Fin G) : 0 < pinCoeff j g := by positivity
  have hlog (j : J) (g : Fin G) :
      Real.log (pinCoeff j g) = r - 2 * t * (k : ℝ) * leafRate j g := by
    simp (disch := positivity) only
      [pinCoeff, Real.log_mul, Real.log_exp, Real.log_rpow, r, leafRate]
    field_simp [ht.ne']
    ring
  have hcoefficient (j : J) (g : Fin G) :
      (pinCoeff j g)⁻¹ = Real.exp (2 * t * (k : ℝ) * leafRate j g - r) := by
    rw [← Real.exp_log (hpinCoeff j g), ← Real.exp_neg, hlog, neg_sub]
  have hmax0 : 0 ≤ gmax :=
    Finset.le_max' (insert (0 : ℝ) gaps) 0 (Finset.mem_insert_self 0 gaps)
  have hmax (f : J × Fin G → ℝ) (p : J × Fin G) :
      f p ≤ (insert (0 : ℝ) (Finset.univ.image f)).max'
        (Finset.insert_nonempty _ _) :=
    Finset.le_max' (insert (0 : ℝ) (Finset.univ.image f)) (f p)
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ p)))
  have hgapmax (j : J) (g : Fin G) : entropyGap j g ≤ gmax :=
    hmax (fun p ↦ entropyGap p.1 p.2) (j, g)
  have hrate (j : J) (g : Fin G) : leafRate j g ≤ 2 * S + gmax :=
    (sub_le_self
      (2 * S + (1 - τ) * entropyGap j g - τ * d -
        (3 + 1 / (2 * t)) * Real.binEntropy τ)
      (show 0 ≤ 50 * K * t by positivity)).trans
      ((sub_le_self (2 * S + (1 - τ) * entropyGap j g - τ * d)
        (mul_nonneg (show 0 ≤ 3 + 1 / (2 * t) by positivity)
          (Real.binEntropy_nonneg hτ.le (hτhalf.trans (by norm_num))))).trans
        ((sub_le_self (2 * S + (1 - τ) * entropyGap j g)
          (mul_nonneg hτ.le
            (add_nonneg (Real.log_natCast_nonneg (Fintype.card C))
              (Real.log_natCast_nonneg (Fintype.card R))))).trans
          (add_le_add_right
            ((mul_le_mul_of_nonneg_left (hgapmax j g)
              (sub_nonneg.mpr (hτhalf.trans (by norm_num)))).trans
              ((mul_le_mul_of_nonneg_right (sub_le_self 1 hτ.le) hmax0).trans_eq
                (one_mul gmax))) (2 * S))))
  have hpNorm : ‖toEuclideanLin Zᴴ ξ‖ ≤ 1 :=
    (l2_opNorm_mulVec Zᴴ ξ).trans
      ((mul_le_mul
        ((l2_opNorm_conjTranspose Z).le.trans
          (l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hZ))
        hξnorm (norm_nonneg ξ) zero_le_one).trans (one_mul (1 : ℝ)).le)
  have hp : toEuclideanLin Zᴴ ξ ≠ 0 :=
    fun h ↦ hw ((congrArg (toEuclideanLin (M ^ (-s))) h).trans (map_zero _))
  have hnorm := MeanTree.explicit_lower_norm_of_exponential_projection_lower_bound
    (fun _ : Fin G ↦ T) hB hcomm
    (fun _ ↦ (hmass τ hτ).1) (fun _ ↦ show 0 < b by positivity)
    (fun _ ↦ show 0 ≤ 2 * t * (k : ℝ) by positivity)
    leafRate (fun _ ↦ 2 * S + gmax) (fun _ ↦ r) hrate
    hfloorB (fun j g ↦ hcoefficient j g ▸ hpinB j g)
    hs (toEuclideanLin Zᴴ ξ) hp hpNorm
    (fun _ ↦ div_nonneg hδ hτ.le) (fun _ ↦ (hmass τ hτ).2)
  have hlinear (g : Fin G) :
      (∑ j, T.weight j * ((1 - τ) * entropyGap j g)) =
        (1 - τ) * (∑ j, T.weight j * entropyGap j g) :=
    (Finset.sum_congr rfl
      (fun j _ ↦ mul_left_comm (T.weight j) (1 - τ) (entropyGap j g))).trans
      (Finset.mul_sum Finset.univ
        (fun j ↦ T.weight j * entropyGap j g) (1 - τ)).symm
  done

end Matrix
