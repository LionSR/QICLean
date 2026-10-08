/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.EntropyGain
import QICLean.Analysis.Transport.LeafDerivative

/-!
# Integrability of the entropy gain in the interpolation parameter

Proposition 7.4 of the area-law paper asserts that the entropy estimate can be integrated over
a closed subinterval of `[0, 1]` (`06-transport.tex` lines 427--429), and its proof notes that
the entropy integrand is uniformly bounded (lines 769--779). Integration also needs the
entropy-gain term to be measurable in the interpolation parameter `p`, which the source does
not discuss. This file proves it.

Each summand of the entropy gain is a transport-state expectation
`G(p) = ∫ m_{1/4}(u) Tr(σ_{h,u} Q) du` with `Q` Hermitian. Perturbing the old input `A_h` along
`A_h^{1/2} e^{δ Q} A_h^{1/2}` changes `-log N(p)²` at rate `(1 - p) w_h G(p)`
(`Matrix.Transport.hasDerivAt_neg_log_filteredNormSq_leafPerturbation`). For fixed `δ` the
perturbed norm is continuous in `p`, so `(1 - p) w_h G(p)` is a pointwise limit of continuous
functions on `(0, 1)` and hence measurable there. The states are density matrices, so
`|G(p)| ≤ ‖Q‖ / 2`, and the entropy gain is integrable on `[0, 1]`.

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy

noncomputable section

namespace TensorPower.ReplicaTransport.TransportData

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
  {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)

omit [∀ v, NeZero (n v)] [Fintype H] [∀ h, Fintype (C h)] in
/-- Replacing the old input at `h` in the terminal inputs replaces the old metric. -/
theorem update_input_old (t : ℝ) (k : ℕ) (h : H)
    (X : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ) :
    Function.update (D.input n t k) ⟨h, none⟩ X =
      Transport.interpInput (Function.update (D.oldMetric n t k) h X) (D.newMetric n t k) := by
  funext j
  obtain ⟨h', _ | c⟩ := j
  · by_cases hh : h' = h
    · subst hh; simp [Transport.interpInput, input]
    · have hne : (⟨h', none⟩ : Σ h, Option (C h)) ≠ ⟨h, none⟩ := fun e =>
        hh (congrArg Sigma.fst e)
      rw [Function.update_of_ne hne]
      simp [Transport.interpInput, input, Function.update_of_ne hh]
  · have hne : (⟨h', some c⟩ : Σ h, Option (C h)) ≠ ⟨h, none⟩ := by
      simp only [ne_eq, Sigma.mk.injEq, not_and]
      intro e; subst e; simp
    rw [Function.update_of_ne hne]; rfl

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- **Measurability of a transport-state expectation in `p`.** For a Hermitian `Q`, the
function `p ↦ ∫ m_{1/4}(u) Tr(σ_{h,u}(p) Q) du` is almost everywhere strongly measurable on
`(0, 1)`. -/
theorem aestronglyMeasurable_integral_state (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t)
    {k : ℕ} (hcomm : D.CrossBandCommute n t k) {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hpre : pre ≠ 0) (h : H)
    {Q : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ}
    (hQ : Q.IsHermitian) :
    AEStronglyMeasurable (fun p => ∫ u, Transport.fourierWeight u *
      (D.state n t k pre p ⟨h, none⟩ u * Q).trace.re) (volume.restrict (Ioo 0 1)) := by
  have hIn := D.posDef_input hD ht hcomm
  have hA : ∀ h', (D.oldMetric n t k h').PosDef := fun h' => hIn ⟨h', none⟩
  have hA' : ∀ h' c, (D.newMetric n t k h' c).PosDef := fun h' c => hIn ⟨h', some c⟩
  set G := fun p => ∫ u, Transport.fourierWeight u *
    (D.state n t k pre p ⟨h, none⟩ u * Q).trace.re
  -- the perturbed norms
  set X : ℝ → Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
    fun δ => Transport.leafPerturbation (D.oldMetric n t k h) Q δ
  have hX : ∀ δ h', (Function.update (D.oldMetric n t k) h (X δ) h').PosDef := fun δ h' => by
    by_cases hh : h' = h
    · subst hh; simpa using Transport.posDef_leafPerturbation (hA h') hQ δ
    · simpa [Function.update_of_ne hh] using hA h'
  set F : ℝ → ℝ → ℝ := fun δ p => -Real.log (Transport.filteredNormSq
    (Transport.interpPath D.histTree D.choiceTree
      (Function.update (D.oldMetric n t k) h (X δ)) (D.newMetric n t k) p) pre)
  have hFc : ∀ δ, Continuous (F δ) := fun δ =>
    ((Transport.continuous_filteredNormSq_interpPath (hX δ) hA' pre).log fun q =>
      (Transport.filteredNormSq_pos (Transport.posDef_interpRoot (hX δ) hA' _) hpre).ne').neg
  have hF0 : ∀ p, F 0 p = -Real.log (Transport.filteredNormSq (D.rootPath n t k p) pre) := by
    intro p
    simp only [F, X, Transport.leafPerturbation_zero (hA h) hQ, Function.update_eq_self]
    rfl
  -- the derivative in `δ` at an interior parameter
  have hderiv : ∀ p ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun δ => F δ p)
      ((1 - p) * D.histTree.weight h * G p) 0 := by
    intro p hp
    have hpI : ((projIcc (0 : ℝ) 1 zero_le_one p : I) : ℝ) = p :=
      congrArg Subtype.val (projIcc_of_mem _ (Ioo_subset_Icc_self hp))
    have hw := D.weight_tree_pos hD hp ⟨h, none⟩
    have := Transport.hasDerivAt_neg_log_filteredNormSq_leafPerturbation
      (D.tree (projIcc (0 : ℝ) 1 zero_le_one p)) hIn hw.ne' hQ hpre
    rw [tree, MeanTree.weight_interpTree_old, hpI] at this
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun δ => ?_)
    simp only [F, X, Transport.interpPath, Transport.interpRoot]
    rw [← update_input_old]
    rfl
  -- a limit of continuous functions
  have hlim : AEStronglyMeasurable (fun p => (1 - p) * D.histTree.weight h * G p)
      (volume.restrict (Ioo 0 1)) := by
    refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ))
      (f := fun δ p => δ⁻¹ * (F δ p - F 0 p))
      (fun δ => (continuous_const.mul ((hFc δ).sub (hFc 0))).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun p hp => ?_
    have := (hderiv p hp).tendsto_slope_zero
    simpa only [zero_add, smul_eq_mul] using this
  have hcongr : (fun p => ((1 - p) * D.histTree.weight h)⁻¹ *
      ((1 - p) * D.histTree.weight h * G p)) =ᵐ[volume.restrict (Ioo 0 1)] G := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun p hp => ?_
    have : (1 - p) * D.histTree.weight h ≠ 0 :=
      mul_ne_zero (by linarith [hp.2]) (hD.histWeight_pos h).ne'
    rw [← mul_assoc, inv_mul_cancel₀ this, one_mul]
  refine AEStronglyMeasurable.congr ?_ hcongr
  exact ((continuous_const.sub continuous_id).mul continuous_const).measurable.inv
    |>.aestronglyMeasurable.mul hlim

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- The transport-state expectations are bounded: `|∫ m_{1/4} Tr(σ_{j,u} Q) du| ≤ ‖Q‖ / 2`
for Hermitian `Q` and `0 < p < 1`. -/
theorem abs_integral_state_le (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hpre : pre ≠ 0) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (j : Σ h, Option (C h))
    {Q : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ}
    (hQ : Q.IsHermitian) :
    |∫ u, Transport.fourierWeight u * (D.state n t k pre p j u * Q).trace.re| ≤ ‖Q‖ / 2 := by
  have hs : (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) (1 / 2) := ⟨by norm_num, by norm_num⟩
  have hm := Real.integral_sinhRatioDensity (s := 1 / 4) (by norm_num)
  have hmi : Integrable Transport.fourierWeight := Real.integrable_sinhRatioDensity hs
  calc |∫ u, Transport.fourierWeight u * (D.state n t k pre p j u * Q).trace.re|
      ≤ ∫ u, Transport.fourierWeight u * ‖Q‖ := by
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) (hmi.mul_const _)
          (Eventually.of_forall fun u => ?_))
        have hb := Transport.abs_re_trace_mul_le (D.posSemidef_state hD ht hcomm pre p j u) hQ
        rw [D.trace_state hD ht hcomm hpre hp j u, Complex.one_re, mul_one] at hb
        have hm0 : 0 < Transport.fourierWeight u := Real.sinhRatioDensity_pos hs u
        simp only [abs_mul, abs_of_pos hm0]
        exact mul_le_mul_of_nonneg_left hb hm0.le
    _ = ‖Q‖ / 2 := by
        rw [integral_mul_const]
        change (∫ u, Real.sinhRatioDensity (1 / 4) u) * ‖Q‖ = ‖Q‖ / 2
        rw [hm]; ring

/-- The Hermitian part `(X + X^†)/2` of a matrix. -/
def hermPart {m : Type*} (X : Matrix m m ℂ) : Matrix m m ℂ := (1 / 2 : ℂ) • (X + Xᴴ)

omit [Fintype V] [DecidableEq V] [∀ v, NeZero (n v)] [Fintype H] [DecidableEq H]
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] in
theorem isHermitian_hermPart {m : Type*} (X : Matrix m m ℂ) : (hermPart X).IsHermitian := by
  rw [hermPart, IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose,
    add_comm]
  congr 1
  simp

omit [Fintype V] [DecidableEq V] [∀ v, NeZero (n v)] [Fintype H] [DecidableEq H]
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] in
/-- Against a Hermitian matrix, a matrix and its Hermitian part have the same real trace
pairing. -/
theorem re_trace_mul_hermPart {m : Type*} [Fintype m] {ρ : Matrix m m ℂ} (hρ : ρ.IsHermitian)
    (X : Matrix m m ℂ) : (ρ * hermPart X).trace.re = (ρ * X).trace.re := by
  have h1 : (ρ * Xᴴ).trace = star (ρ * X).trace := by
    rw [← trace_conjTranspose (ρ * X), conjTranspose_mul, hρ.eq]
    exact trace_mul_comm _ _
  rw [hermPart, Matrix.mul_smul, trace_smul, Matrix.mul_add, trace_add, h1, smul_eq_mul,
    Complex.mul_re, Complex.add_re, Complex.add_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  norm_num
  ring

/-- **The entropy gain is integrable on `[0, 1]`** (`06-transport.tex` lines 427--429 and
769--779): it is measurable in `p` and bounded uniformly in `0 < p < 1`. -/
theorem intervalIntegrable_entropyGain (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hpre : pre ≠ 0) : IntervalIntegrable (D.entropyGain n t k pre) volume 0 1 := by
  set F : ∀ h, Fin K → (SiteConfig n → ℂ) → ℝ := fun h g θ => ∑ c, (D.choiceTree h).weight c *
    moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ)
  have hFc : ∀ h g, Continuous (F h g) := fun h g =>
    continuous_finsetSum _ fun c _ => continuous_const.mul (continuous_moveEta _ _)
  set Q : H → Fin K → Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
    fun h g => hermPart (coherentAverage k (base n) (F h g))
  have hQ : ∀ h g, (Q h g).IsHermitian := fun h g => isHermitian_hermPart _
  have hstate : ∀ p ∈ Ioo (0 : ℝ) 1, ∀ h g u,
      realCoherentIntegral k (base n) (D.state n t k pre p ⟨h, none⟩ u) (F h g) =
        (D.state n t k pre p ⟨h, none⟩ u * Q h g).trace.re := fun p hp h g u => by
    rw [re_trace_mul_hermPart (D.posSemidef_state hD ht hcomm pre p _ u).isHermitian,
      trace_mul_coherentAverage k (base n) (hFc h g)]
  have heq : ∀ p ∈ Ioo (0 : ℝ) 1, D.entropyGain n t k pre p = ∑ h, ∑ g,
      D.histTree.weight h * ∫ u, Transport.fourierWeight u *
        (D.state n t k pre p ⟨h, none⟩ u * Q h g).trace.re := fun p hp => by
    unfold entropyGain
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun g _ => ?_
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [hstate p hp h g u]
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  set B : ℝ := ∑ h, ∑ g, D.histTree.weight h * (‖Q h g‖ / 2)
  have hmeas : AEStronglyMeasurable (fun p => ∑ h, ∑ g, D.histTree.weight h *
      ∫ u, Transport.fourierWeight u * (D.state n t k pre p ⟨h, none⟩ u * Q h g).trace.re)
      (volume.restrict (Ioo 0 1)) :=
    Finset.aestronglyMeasurable_fun_sum _ fun h _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun g _ => aestronglyMeasurable_const.mul
        (D.aestronglyMeasurable_integral_state hD ht hcomm hpre h (hQ h g))
  refine (show IntegrableOn _ (Ioo (0 : ℝ) 1) volume from
    ⟨hmeas, HasFiniteIntegral.restrict_of_bounded (C := B) (by simp) ?_⟩).congr_fun
    (fun p hp => (heq p hp).symm) measurableSet_Ioo
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun h _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun g _ => ?_))
  rw [abs_mul, abs_of_pos (hD.histWeight_pos h)]
  exact mul_le_mul_of_nonneg_left (D.abs_integral_state_le hD ht hcomm hpre hp _ (hQ h g))
    (hD.histWeight_pos h).le

end TensorPower.ReplicaTransport.TransportData
