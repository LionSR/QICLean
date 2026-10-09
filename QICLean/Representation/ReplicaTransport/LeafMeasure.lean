/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.CoherentMeasure
import QICLean.Representation.ReplicaTransport.States
import QICLean.Analysis.Transport.ErrorFourier
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier-weighted coherent measures of transport states

The measure of a terminal leaf is the pushforward to the one-copy unit sphere of
Lebesgue measure times unitary Haar measure, with density
`m_{1/4}(u) D_k Re Tr(σ_{j,u} P_{Ue,k})`. The state `σ` is exactly `TransportData.state`.
The definition contains no history or choice weight and no normalization of the
Fourier density, whose integral is `1/2`.

Finiteness holds for every real interpolation parameter and every supplied vector.
The domination argument uses the product of the unitary groups on the replica space
and the one-copy space. It gives a bound for each fixed parameter, not a uniform
bound or continuity in that parameter. Positivity needs admissibility and cross-band
commutation, whereas mass `1/2` also needs a nonzero symmetric vector and a nonzero
terminal weight. Inactive leaves carry the zero measure.

Reference: *A two-dimensional area law from a global spectral gap*, Proposition 7.4,
`06-transport.tex`, displays `transport:coherent-measure` and `transport:states`,
lines 364--401. The remaining scanner conclusions and the source-only verification
boundary are recorded in `docs/paper-gaps/oai26_literal_transport_measures.tex`.
The proofs are written from the paper; no source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix MeasureTheory Set PermutationRepresentation Entropy

noncomputable section

namespace TensorPower.ReplicaTransport.TransportData

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : ℕ} {H : Type*} [DecidableEq H] {C : H → Type*}
  [∀ h, DecidableEq (C h)]
variable (D : TransportData V K H C) (n : V → ℕ) [∀ v, NeZero (n v)]
variable (t : ℝ) (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ)
  (p : ℝ) (j : Σ h, Option (C h))

/-- The real density before pushing forward to the unit sphere. -/
def transportLeafDensity (z : ℝ × unitaryGroup (SiteConfig n) ℂ) : ℝ :=
  Matrix.Transport.fourierWeight z.1 *
    coherentDensity k (base n) (D.state n t k pre p j z.1) z.2

/-- The Fourier-weighted coherent measure of the literal terminal state. -/
def transportLeafMeasure : Measure (CoherentSphere (SiteConfig n)) :=
  Measure.map (fun z : ℝ × unitaryGroup (SiteConfig n) ℂ => coherentSphereMap (base n) z.2)
    ((volume.prod (unitaryHaar (SiteConfig n))).withDensity
      (fun z => ENNReal.ofReal (D.transportLeafDensity n t k pre p j z)))

/-- The density uses the same replica dimension, Fourier weight and coherent projector
as the transport integral. -/
theorem transportLeafDensity_eq (z : ℝ × unitaryGroup (SiteConfig n) ℂ) :
    D.transportLeafDensity n t k pre p j z =
      (symDim (SiteConfig n) k : ℝ) * Matrix.Transport.fourierWeight z.1 *
        (D.state n t k pre p j z.1 *
          coherentProj k ((z.2 : Matrix (SiteConfig n) (SiteConfig n) ℂ) *ᵥ
            Pi.single (base n) 1)).trace.re := by
  unfold transportLeafDensity coherentDensity
  ring

private def leafUnitaryState
    (W : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  let v := Matrix.Transport.filteredVector (D.rootPath n t k p) pre
  traceAdjointMap ((D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).leafMap
    (D.input n t k) j).toLinearMap (vecMulVec (W *ᵥ v) (star (W *ᵥ v)))

private theorem continuous_leafUnitaryState :
    Continuous (D.leafUnitaryState n t k pre p j) := by
  let Φ := traceAdjointMap ((D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).leafMap
    (D.input n t k) j).toLinearMap
  have hv : Continuous fun W :
      Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ =>
        W *ᵥ Matrix.Transport.filteredVector (D.rootPath n t k p) pre :=
    continuous_id.matrix_mulVec continuous_const
  exact Φ.continuous_of_finiteDimensional.comp (hv.matrix_vecMulVec hv.star)

/-- For fixed interpolation parameter, the literal transport state is continuous in
the Fourier variable. No positivity or nonzero-vector hypothesis is needed. -/
theorem continuous_state : Continuous (D.state n t k pre p j) := by
  exact (D.continuous_leafUnitaryState n t k pre p j).comp
    ((continuous_hermitianUnitaryPath (CFC.log (D.rootPath n t k p))).comp continuous_neg)

private def leafUnitaryPath (u : ℝ) : unitaryGroup (Config k fun v => Fin (n v)) ℂ :=
  ⟨Matrix.Transport.imagPow (D.rootPath n t k p) u,
    Matrix.mem_unitaryGroup_iff'.mpr
      (Matrix.Transport.conjTranspose_imagPow_mul_imagPow _ _)⟩

private theorem continuous_leafUnitaryPath : Continuous (D.leafUnitaryPath n t k p) :=
  ((continuous_hermitianUnitaryPath (CFC.log (D.rootPath n t k p))).comp
    continuous_neg).subtype_mk _

private theorem measurable_fourierWeight : Measurable Matrix.Transport.fourierWeight := by
  unfold Matrix.Transport.fourierWeight Real.sinhRatioDensity
  exact measurable_const.div ((Real.continuous_cosh.measurable.comp
    (measurable_const.mul measurable_id)).add measurable_const)

/-- The density is jointly measurable in the Fourier variable and the Haar unitary. -/
theorem measurable_transportLeafDensity :
    Measurable (D.transportLeafDensity n t k pre p j) := by
  have hpair : Continuous fun z : ℝ × unitaryGroup (SiteConfig n) ℂ =>
      (D.state n t k pre p j z.1, z.2) :=
    ((D.continuous_state n t k pre p j).comp continuous_fst).prodMk continuous_snd
  exact (measurable_fourierWeight.comp measurable_fst).mul
    ((continuous_coherentDensity_joint k (base n)).comp hpair).measurable

/-- A continuous spherical symbol times the joint density is absolutely integrable.
Both unitary coordinates enter the compactness bound. -/
theorem integrable_transportLeafDensity_mul {f : CoherentSphere (SiteConfig n) → ℝ}
    (hf : Continuous f) :
    Integrable (fun z : ℝ × unitaryGroup (SiteConfig n) ℂ =>
      D.transportLeafDensity n t k pre p j z * f (coherentSphereMap (base n) z.2))
      (volume.prod (unitaryHaar (SiteConfig n))) := by
  let F : unitaryGroup (Config k fun v => Fin (n v)) ℂ ×
      unitaryGroup (SiteConfig n) ℂ → ℝ := fun z =>
    coherentDensity k (base n) (D.leafUnitaryState n t k pre p j z.1) z.2 *
      f (coherentSphereMap (base n) z.2)
  have hpair : Continuous fun z : unitaryGroup (Config k fun v => Fin (n v)) ℂ ×
      unitaryGroup (SiteConfig n) ℂ => (D.leafUnitaryState n t k pre p j z.1, z.2) :=
    ((D.continuous_leafUnitaryState n t k pre p j).comp
      (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
  have hF : Continuous F :=
    ((continuous_coherentDensity_joint k (base n)).comp hpair).mul
      (hf.comp ((continuous_coherentSphereMap (base n)).comp continuous_snd))
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  have hparam : Continuous fun z : ℝ × unitaryGroup (SiteConfig n) ℂ =>
      F (D.leafUnitaryPath n t k p z.1, z.2) :=
    hF.comp (((D.continuous_leafUnitaryPath n t k p).comp continuous_fst).prodMk
      continuous_snd)
  have hint := (Matrix.Transport.integrable_fourierWeight.comp_fst
    (unitaryHaar (SiteConfig n))).mul_bdd hparam.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hB _ (mem_univ _))
  simpa only [F, transportLeafDensity, leafUnitaryState, leafUnitaryPath,
    state, Matrix.Transport.transportState, rootPath, mul_assoc] using hint

/-- The unweighted joint density is absolutely integrable for all totalized inputs. -/
theorem integrable_transportLeafDensity :
    Integrable (D.transportLeafDensity n t k pre p j)
      (volume.prod (unitaryHaar (SiteConfig n))) := by
  simpa only [mul_one] using
    D.integrable_transportLeafDensity_mul n t k pre p j (f := fun _ => 1) continuous_const

/-- The literal Fourier-weighted measure is finite for every real parameter. -/
instance isFiniteMeasure_transportLeafMeasure :
    IsFiniteMeasure (D.transportLeafMeasure n t k pre p j) := by
  let : IsFiniteMeasure ((volume.prod (unitaryHaar (SiteConfig n))).withDensity
      (fun z => ENNReal.ofReal (D.transportLeafDensity n t k pre p j z))) :=
    isFiniteMeasure_withDensity_ofReal
      (D.integrable_transportLeafDensity n t k pre p j).hasFiniteIntegral
  unfold transportLeafMeasure
  infer_instance

/-- Continuous functions on the unit sphere are integrable against each leaf measure. -/
theorem integrable_transportLeafMeasure {f : CoherentSphere (SiteConfig n) → ℝ}
    (hf : Continuous f) : Integrable f (D.transportLeafMeasure n t k pre p j) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Under the structural transport hypotheses, taking `ofReal` loses no density,
including at inactive leaves and outside the open interpolation interval. -/
theorem transportLeafDensity_nonneg (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : D.CrossBandCommute n t k) (z : ℝ × unitaryGroup (SiteConfig n) ℂ) :
    0 ≤ D.transportLeafDensity n t k pre p j z :=
  mul_nonneg (Real.sinhRatioDensity_pos (by norm_num) z.1).le
    (coherentDensity_nonneg k (base n) (D.state n t k pre p j z.1)
      (D.posSemidef_state hD ht hcomm pre p j z.1) z.2)

/-- The literal pushforward represents the exact nested Fourier-coherent integral. -/
theorem integral_transportLeafMeasure (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : D.CrossBandCommute n t k) {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂D.transportLeafMeasure n t k pre p j) =
      ∫ u, Matrix.Transport.fourierWeight u *
        realCoherentIntegral k (base n) (D.state n t k pre p j u) f := by
  have hs : Continuous fun θ : CoherentSphere (SiteConfig n) => f (fun x => θ.1 x) :=
    hf.comp continuous_coherentSphere_coe
  rw [transportLeafMeasure, integral_map_of_stronglyMeasurable
    ((continuous_coherentSphereMap (base n)).comp continuous_snd).measurable
    hs.stronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (D.measurable_transportLeafDensity n t k pre p j).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (D.transportLeafDensity_nonneg n t k pre p j hD ht hcomm _),
    smul_eq_mul]
  rw [integral_prod _ (D.integrable_transportLeafDensity_mul n t k pre p j hs)]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [transportLeafDensity, coherentSphereMap_apply, mul_assoc]
  rw [integral_const_mul, integral_coherentDensity_mul]

/-- Zero-weight leaves retain the zero state from the normalized derivative definition. -/
theorem state_eq_zero_of_weight_eq_zero
    (hw : (D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).weight j = 0) (u : ℝ) :
    D.state n t k pre p j u = 0 := by
  simp [state, Matrix.Transport.transportState, MeanTree.leafMap, normalizedDerivMap,
    hw, traceAdjointMap]

/-- A zero terminal weight gives the zero measure, rather than an arbitrary probability. -/
theorem transportLeafMeasure_eq_zero_of_weight_eq_zero
    (hw : (D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).weight j = 0) :
    D.transportLeafMeasure n t k pre p j = 0 := by
  simp [transportLeafMeasure, transportLeafDensity,
    D.state_eq_zero_of_weight_eq_zero n t k pre p j hw, coherentDensity]

/-- New leaves are inactive at the left interpolation endpoint. -/
@[simp] theorem transportLeafMeasure_new_zero (h : H) (c : C h) :
    D.transportLeafMeasure n t k pre 0 ⟨h, some c⟩ = 0 := by
  apply D.transportLeafMeasure_eq_zero_of_weight_eq_zero
  have hp : ((projIcc (0 : ℝ) 1 zero_le_one 0 : I) : ℝ) = 0 :=
    congrArg Subtype.val (projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by simp))
  rw [tree, MeanTree.weight_interpTree_new, hp]
  simp

/-- Old leaves are inactive at the right interpolation endpoint. -/
@[simp] theorem transportLeafMeasure_old_one (h : H) :
    D.transportLeafMeasure n t k pre 1 ⟨h, none⟩ = 0 := by
  apply D.transportLeafMeasure_eq_zero_of_weight_eq_zero
  have hp : ((projIcc (0 : ℝ) 1 zero_le_one 1 : I) : ℝ) = 1 :=
    congrArg Subtype.val (projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by simp))
  rw [tree, MeanTree.weight_interpTree_old, hp]
  simp

/-- The measure associated with the zero supplied vector is zero. -/
@[simp] theorem transportLeafMeasure_zero_pre :
    D.transportLeafMeasure n t k 0 p j = 0 := by
  have hz : ∀ u, D.state n t k 0 p j u = 0 := by
    intro u
    simp [state, Matrix.Transport.transportState, Matrix.Transport.filteredVector,
      Matrix.Transport.filteredRaw]
  simp [transportLeafMeasure, transportLeafDensity, hz, coherentDensity]

/-- A nonzero-weight leaf of a nonzero symmetric vector has Fourier mass `1/2`.
The assertion includes active leaves at clamped interpolation parameters. -/
theorem transportLeafMeasure_real_univ_of_weight_ne_zero (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : D.CrossBandCommute n t k)
    (hsym : pre ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre ≠ 0)
    (hw : (D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).weight j ≠ 0) :
    (D.transportLeafMeasure n t k pre p j).real univ = 1 / 2 := by
  have htr : ∀ u, (D.state n t k pre p j u).trace = 1 := by
    intro u
    rw [state, Matrix.Transport.trace_transportState (D.posDef_input hD ht hcomm) hw]
    exact Matrix.Transport.star_dotProduct_filteredVector
      (MeanTree.posDef_eval (D.posDef_input hD ht hcomm) _) hpre
  have hint := D.integral_transportLeafMeasure n t k pre p j hD ht hcomm
    (f := fun _ => 1) continuous_const
  simp only [integral_const, smul_eq_mul, mul_one] at hint
  rw [hint]
  simp_rw [realCoherentIntegral_one (base n) (htr _)
    (D.symProj_mul_state hD ht hcomm hsym p j _), mul_one]
  exact Matrix.Transport.integral_fourierWeight

/-- Every interior leaf has Fourier mass `1/2`, including when there are zero copies. -/
theorem transportLeafMeasure_real_univ (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : D.CrossBandCommute n t k)
    (hsym : pre ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre ≠ 0)
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    (D.transportLeafMeasure n t k pre p j).real univ = 1 / 2 :=
  D.transportLeafMeasure_real_univ_of_weight_ne_zero n t k pre p j hD ht hcomm hsym hpre
    (D.weight_tree_pos hD hp j).ne'

/-- The complete mass law distinguishes active leaves from inactive leaves. -/
theorem transportLeafMeasure_real_univ_eq_ite (hD : D.IsAdmissible) (ht : 0 ≤ t)
    (hcomm : D.CrossBandCommute n t k)
    (hsym : pre ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre ≠ 0) :
    (D.transportLeafMeasure n t k pre p j).real univ =
      if (D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).weight j = 0 then 0 else 1 / 2 := by
  split_ifs with hw
  · rw [D.transportLeafMeasure_eq_zero_of_weight_eq_zero n t k pre p j hw]
    simp
  · exact D.transportLeafMeasure_real_univ_of_weight_ne_zero n t k pre p j
      hD ht hcomm hsym hpre hw

end TensorPower.ReplicaTransport.TransportData
