/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.CoherentLog
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Coherent measures on the unit sphere

The coherent measure of the area-law paper, `05-replicas.tex`, equation
`replicas:husimi`, and `06-transport.tex`, equation `transport:coherent-measure`
(lines 367--375), is the image of the Haar measure with density
`D_k Re Tr(ρ P_{U e_a,k})` under the literal map `U ↦ U e_a` to the unit sphere.

The measure is finite for every matrix. For a positive semidefinite matrix its
integrals agree with `realCoherentIntegral`; for a positive trace-one matrix supported on
the symmetric subspace its mass is one. The zero matrix gives the zero measure.
The definition uses `ENNReal.ofReal` and is total even outside the positive cone;
the identification with the real coherent integral is asserted on that cone.

The proofs are written from the paper; no Lean source was adapted.
-/

open Matrix MeasureTheory PermutationRepresentation
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

namespace TensorPower

/-- The unit-vector domain of the coherent measures (`06-transport.tex`,
equation `transport:coherent-measure`). Its measurable structure is the inherited
Borel structure of finite-dimensional Euclidean space. -/
abbrev CoherentSphere (Ω : Type*) [Fintype Ω] :=
  {θ : EuclideanSpace ℂ Ω // ‖θ‖ = 1}

variable {Ω : Type*} [Fintype Ω]

instance : CompactSpace (CoherentSphere Ω) := by
  apply isCompact_iff_compactSpace.mp
  simpa [Metric.sphere] using (isCompact_sphere (0 : EuclideanSpace ℂ Ω) 1)

/-- The ambient coordinates of a unit vector depend continuously on that vector. -/
theorem continuous_coherentSphere_coe :
    Continuous fun θ : CoherentSphere Ω => (fun x => θ.1 x) :=
  (PiLp.continuous_ofLp 2 (fun _ : Ω => ℂ)).comp continuous_subtype_val

variable [DecidableEq Ω]

/-- The literal Haar-to-sphere map `U ↦ U e_a` used in
`06-transport.tex`, equation `transport:coherent-measure`. -/
def coherentSphereMap (a : Ω) (U : unitaryGroup Ω ℂ) : CoherentSphere Ω := by
  refine ⟨(EuclideanSpace.equiv Ω ℂ).symm
    ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1), ?_⟩
  have h := re_star_dotProduct_self_eq_norm_sq
    ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)
  rw [dotProduct_comm, dotProduct_star_unitary_mulVec_single] at h
  have hn := norm_nonneg ((EuclideanSpace.equiv Ω ℂ).symm
    ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1))
  norm_num at h
  nlinarith

@[simp]
theorem coherentSphereMap_apply (a : Ω) (U : unitaryGroup Ω ℂ) (x : Ω) :
    (coherentSphereMap a U).1 x = ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) x := rfl

/-- The Haar-to-sphere map is continuous. -/
theorem continuous_coherentSphereMap (a : Ω) : Continuous (coherentSphereMap a) := by
  apply Continuous.subtype_mk
  exact (PiLp.continuous_toLp 2 (fun _ : Ω => ℂ)).comp (continuous_coherentVec a)

/-- The real Haar density `D_k Re Tr(ρ P_{U e_a,k})` from
`06-transport.tex`, equation `transport:coherent-measure`. -/
def coherentDensity (k : ℕ) (a : Ω)
    (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) (U : unitaryGroup Ω ℂ) : ℝ :=
  (symDim Ω k : ℝ) *
    (ρ * coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)).trace.re

variable (k : ℕ) (a : Ω) (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ)

/-- The density is jointly continuous in the matrix and the unitary. -/
theorem continuous_coherentDensity_joint :
    Continuous fun z : Matrix (Fin k → Ω) (Fin k → Ω) ℂ × unitaryGroup Ω ℂ =>
      coherentDensity k a z.1 z.2 := by
  exact continuous_const.mul (Complex.continuous_re.comp
    ((continuous_fst.mul (continuous_coherentProj k
      ((continuous_coherentVec a).comp continuous_snd))).matrix_trace))

/-- For a fixed matrix the coherent density is continuous on the compact unitary group. -/
theorem continuous_coherentDensity : Continuous (coherentDensity k a ρ) :=
  (continuous_coherentDensity_joint k a).comp (continuous_const.prodMk continuous_id)

/-- Positivity of the density follows from the quadratic-form characterization of
positive semidefiniteness, without requiring the two matrix factors to commute. -/
theorem coherentDensity_nonneg (hρ : ρ.PosSemidef) (U : unitaryGroup Ω ℂ) :
    0 ≤ coherentDensity k a ρ U := by
  apply mul_nonneg (Nat.cast_nonneg _)
  rw [coherentProj, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
  exact (Complex.nonneg_iff.mp (hρ.dotProduct_mulVec_nonneg _)).1

/-- Compactness gives absolute integrability for every matrix, without positivity. -/
theorem integrable_coherentDensity : Integrable (coherentDensity k a ρ) (unitaryHaar Ω) :=
  (continuous_coherentDensity k a ρ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Moving the dimension factor into the integral gives the accepted real coherent
integral. This algebraic identity does not require positivity or integrability hypotheses. -/
theorem integral_coherentDensity_mul (f : (Ω → ℂ) → ℝ) :
    (∫ U, coherentDensity k a ρ U * f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)
      ∂(unitaryHaar Ω)) = realCoherentIntegral k a ρ f := by
  rw [realCoherentIntegral, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun U => by dsimp [coherentDensity]; ring

/-- The coherent measure is the literal weighted Haar pushforward to the unit
sphere (`06-transport.tex`, equation `transport:coherent-measure`). -/
def coherentMeasure : Measure (CoherentSphere Ω) :=
  Measure.map (coherentSphereMap a)
    ((unitaryHaar Ω).withDensity (fun U => ENNReal.ofReal (coherentDensity k a ρ U)))

/-- The coherent measure is finite for every matrix. -/
instance isFiniteMeasure_coherentMeasure : IsFiniteMeasure (coherentMeasure k a ρ) := by
  letI : IsFiniteMeasure ((unitaryHaar Ω).withDensity
      (fun U => ENNReal.ofReal (coherentDensity k a ρ U))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_coherentDensity k a ρ).hasFiniteIntegral
  unfold coherentMeasure
  infer_instance

/-- On a Borel set the coherent measure is the integral of the density over the
literal Haar preimage of that set. -/
theorem coherentMeasure_apply {s : Set (CoherentSphere Ω)} (hs : MeasurableSet s) :
    coherentMeasure k a ρ s =
      ∫⁻ U in coherentSphereMap a ⁻¹' s, ENNReal.ofReal (coherentDensity k a ρ U)
        ∂(unitaryHaar Ω) := by
  rw [coherentMeasure, Measure.map_apply (continuous_coherentSphereMap a).measurable hs,
    withDensity_apply _ ((continuous_coherentSphereMap a).measurable hs)]

/-- Continuous real symbols are integrable against the finite coherent measure. -/
theorem integrable_coherentMeasure {f : CoherentSphere Ω → ℝ} (hf : Continuous f) :
    Integrable f (coherentMeasure k a ρ) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Integration against the literal coherent measure agrees with the accepted
real coherent integral for a positive semidefinite matrix. -/
theorem integral_coherentMeasure (hρ : ρ.PosSemidef)
    {f : (Ω → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂coherentMeasure k a ρ) =
      realCoherentIntegral k a ρ f := by
  have hfc : Continuous fun θ : CoherentSphere Ω => f (fun x => θ.1 x) :=
    hf.comp continuous_coherentSphere_coe
  rw [coherentMeasure,
    integral_map_of_stronglyMeasurable (continuous_coherentSphereMap a).measurable
      hfc.stronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_coherentDensity k a ρ).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun U => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (coherentDensity_nonneg k a ρ hρ _),
    smul_eq_mul, coherentSphereMap_apply]
  exact integral_coherentDensity_mul k a ρ f

/-- A positive trace-one state on the symmetric subspace gives mass one, as in
`06-transport.tex`, equation `transport:coherent-measure`. -/
theorem coherentMeasure_real_univ (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hsym : symProj (copyPerm Ω k) * ρ = ρ) :
    (coherentMeasure k a ρ).real Set.univ = 1 := by
  have h := integral_coherentMeasure k a ρ hρ (f := fun _ => 1) continuous_const
  simpa [realCoherentIntegral_one a htr hsym] using h

@[simp]
theorem coherentDensity_zero (U : unitaryGroup Ω ℂ) :
    coherentDensity k a (0 : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) U = 0 := by
  simp [coherentDensity]

/-- The zero state has zero coherent measure, preserving the accepted totalized
inactive-leaf definition. -/
@[simp]
theorem coherentMeasure_zero :
    coherentMeasure k a (0 : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) = 0 := by
  simp [coherentMeasure]

end TensorPower
