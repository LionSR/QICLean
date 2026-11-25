/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.BandMetric.IntegratedEntropy
import QICLean.ManyBody.Replica.BandMetric.Energy
import QICLean.ManyBody.Replica.BandMetric.MoveEntropy
import QICLean.ManyBody.Replica.Symbol.CoherentMeasure
import QICLean.Channel.OperatorMean.ErrorFourier

/-!
# The Fourier–coherent integral at the old leaf of a history

For transport data, a history `h` and a real symbol `f` on one-copy vectors, put
\[
  J_h(f) = \int m_{1/4}(u)\, \mathcal{H}_{\sigma_{(h,\mathrm{old}),u}}(f)\, du ,
\]
the Fourier-weighted coherent integral of `f` in the transport state at the old terminal leaf
of `h` (area-law paper, `06-transport.tex`, displays `transport:states` and
`transport:entropy-gain`, lines 390–412). The state at the old leaf does not depend on the
conditional choice, so one integral serves all choices of a history.

This file proves:

* `J_h` is monotone, additive over finite sums and homogeneous on continuous symbols,
  nonnegative on nonnegative symbols, and `J_h(1) = 1/2` for a nonzero symmetric vector and an
  interior interpolation parameter;
* the entropy gain is `∑_h w_h J_h(G_h)`, where `G_h = ∑_g ∑_c q_{c|h} η_{h,c,g}` is the
  choice-averaged move entropy; `G_h` is continuous and nonnegative, and at most `2Kℓ` on unit
  vectors when every move has logarithmic dimension at most `ℓ`; hence the entropy gain is
  nonnegative;
* for a continuous symbol, `p ↦ J_h(f)` is almost everywhere strongly measurable and
  bounded by `‖herm(𝒬_k f)‖ / 2` on `(0, 1)`, hence integrable on the unit interval, and so
  are finite weighted sums over histories. The vector `pre` may vanish; `J_h` is then zero.

No continuity in the interpolation parameter is asserted.

## Main definitions

* `TensorPower.ReplicaTransport.TransportData.oldFourierCoherentIntegral`: `J_h(f)`.
* `TensorPower.ReplicaTransport.TransportData.choiceEntropySymbol`: `G_h`.

## Main statements

* `TensorPower.ReplicaTransport.TransportData.entropyGain_eq_sum_oldFourierCoherentIntegral`
* `TensorPower.ReplicaTransport.TransportData.entropyGain_nonneg`
* `TensorPower.ReplicaTransport.TransportData.choiceEntropySymbol_le_of_logDim_move_le`
* `TensorPower.ReplicaTransport.TransportData.intervalIntegrable_sum_oldFourierCoherentIntegral`

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `06-transport.tex`, lines 321–330, 390–412, 427–429 and 769–779; `08-scanner.tex`,
  lines 434–440.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Set
noncomputable section

namespace TensorPower.ReplicaTransport.TransportData

variable {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
variable {H : Type*} [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)]

section OldLeaf

variable (D : TransportData V K H C) (n : V → ℕ) [∀ v, NeZero (n v)]

/-- The Fourier–coherent integral `J_h(f) = ∫ m_{1/4}(u) ℋ_{σ_u}(f) du` of a symbol `f`, where
`σ_u` is the transport state at the old terminal leaf of the history `h`. This state does not
depend on the conditional choice. -/
def oldFourierCoherentIntegral (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    (f : ((∀ v, Fin (n v)) → ℂ) → ℝ) : ℝ :=
  ∫ u, Matrix.Transport.fourierWeight u *
    realCoherentIntegral k (base n) (D.state n t k pre p ⟨h, none⟩ u) f

/-- For a continuous symbol, the integrand of `J_h(f)` is integrable in the Fourier
variable. -/
theorem integrable_oldFourierCoherentIntegral (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    {f : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hf : Continuous f) :
    Integrable fun u => Matrix.Transport.fourierWeight u *
      realCoherentIntegral k (base n) (D.state n t k pre p ⟨h, none⟩ u) f := by
  refine (D.integrable_fourierWeight_mul_trace_state t k pre p ⟨h, none⟩
    (coherentAverage k (base n) f)).congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [trace_mul_coherentAverage k (base n) hf]

/-- `J_h` is monotone on continuous symbols: `f ≤ g` pointwise gives `J_h(f) ≤ J_h(g)`. -/
theorem oldFourierCoherentIntegral_mono (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    {f g : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ θ, f θ ≤ g θ) :
    D.oldFourierCoherentIntegral n t k pre p h f ≤
      D.oldFourierCoherentIntegral n t k pre p h g := by
  apply integral_mono (D.integrable_oldFourierCoherentIntegral n t k pre p h hf)
    (D.integrable_oldFourierCoherentIntegral n t k pre p h hg)
  intro u
  exact mul_le_mul_of_nonneg_left
    (realCoherentIntegral_mono k (base n) (D.posSemidef_state hD ht hcomm pre p _ u)
      hf hg hfg) (Real.sinhRatioDensity_pos (by norm_num) u).le

/-- `J_h(f) ≥ 0` for a nonnegative symbol `f`: the Fourier weight is positive and the
transport state is positive semidefinite. -/
theorem oldFourierCoherentIntegral_nonneg (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    {f : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hf0 : ∀ θ, 0 ≤ f θ) :
    0 ≤ D.oldFourierCoherentIntegral n t k pre p h f :=
  integral_nonneg fun u => mul_nonneg (Real.sinhRatioDensity_pos (by norm_num) u).le
    (realCoherentIntegral_nonneg (base n) (D.posSemidef_state hD ht hcomm pre p _ u) hf0)

/-- `J_h` of a finite sum of continuous symbols is the sum of the integrals. -/
theorem oldFourierCoherentIntegral_sum (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    {ι : Type*} (s : Finset ι) (f : ι → ((∀ v, Fin (n v)) → ℂ) → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    D.oldFourierCoherentIntegral n t k pre p h (fun θ => ∑ i ∈ s, f i θ) =
      ∑ i ∈ s, D.oldFourierCoherentIntegral n t k pre p h (f i) := by
  unfold oldFourierCoherentIntegral
  simp_rw [realCoherentIntegral_sum k (base n) _ s f hf, Finset.mul_sum]
  exact integral_finsetSum _ fun i hi =>
    D.integrable_oldFourierCoherentIntegral n t k pre p h (hf i hi)

/-- `J_h(c f) = c J_h(f)` for every symbol `f`. -/
theorem oldFourierCoherentIntegral_const_mul (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    (c : ℝ) (f : ((∀ v, Fin (n v)) → ℂ) → ℝ) :
    D.oldFourierCoherentIntegral n t k pre p h (fun θ => c * f θ) =
      c * D.oldFourierCoherentIntegral n t k pre p h f := by
  unfold oldFourierCoherentIntegral
  simp_rw [realCoherentIntegral_const_mul, mul_left_comm _ c]
  exact integral_const_mul _ _

/-- For a nonzero symmetric vector and an interpolation parameter in `(0, 1)`,
`J_h(1) = 1/2`: the transport state has trace one and the Fourier weight has mass one
half. -/
theorem oldFourierCoherentIntegral_one (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hsym : pre ∈ symmetricSubspace k (fun v => Fin (n v))) (hpre : pre ≠ 0)
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (h : H) :
    D.oldFourierCoherentIntegral n t k pre p h (fun _ => 1) = 1 / 2 := by
  have hmass (u : ℝ) :
      realCoherentIntegral k (base n) (D.state n t k pre p ⟨h, none⟩ u) (fun _ => 1) = 1 :=
    realCoherentIntegral_one (base n) (D.trace_state hD ht hcomm hpre hp _ u)
      (D.symProj_mul_state hD ht hcomm hsym p _ u)
  simp only [oldFourierCoherentIntegral, hmass, mul_one]
  exact Matrix.Transport.integral_fourierWeight

/-! ### Dependence on the interpolation parameter -/

/-- `J_h(F) = 0` for the zero vector, at every interpolation parameter and every number of
copies: its transport state is zero. -/
@[simp] theorem oldFourierCoherentIntegral_zero_pre (t : ℝ) (k : ℕ) (p : ℝ) (h : H)
    (F : ((∀ v, Fin (n v)) → ℂ) → ℝ) :
    D.oldFourierCoherentIntegral n t k 0 p h F = 0 := by
  have hv : Matrix.Transport.filteredVector (D.rootPath n t k p) 0 = 0 := by
    simp [Matrix.Transport.filteredVector, Matrix.Transport.filteredRaw]
  have hrank : vecMulVec (0 : Config k (fun v => Fin (n v)) → ℂ)
      (star (0 : Config k (fun v => Fin (n v)) → ℂ)) = 0 := by
    ext a b
    simp [Matrix.vecMulVec]
  have hstate (u : ℝ) : D.state n t k 0 p ⟨h, none⟩ u = 0 := by
    simp only [state, Matrix.Transport.transportState, hv, Matrix.mulVec_zero,
      hrank, map_zero]
  simp [oldFourierCoherentIntegral, hstate, realCoherentIntegral]

/-- For a continuous symbol `F`, `J_h(F) = ∫ m_{1/4}(u) Re Tr(σ_u herm(𝒬_k F)) du`, where
`herm(𝒬_k F)` is the Hermitian part of the coherent average of `F`. The interpolation
parameter is arbitrary. -/
theorem oldFourierCoherentIntegral_eq_integral_hermPart (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (h : H)
    {F : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hF : Continuous F) :
    D.oldFourierCoherentIntegral n t k pre p h F =
      ∫ u, Matrix.Transport.fourierWeight u *
        (D.state n t k pre p ⟨h, none⟩ u *
          hermPart (coherentAverage k (base n) F)).trace.re := by
  unfold oldFourierCoherentIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    change Matrix.Transport.fourierWeight u *
        realCoherentIntegral k (base n) (D.state n t k pre p ⟨h, none⟩ u) F =
      Matrix.Transport.fourierWeight u *
        (D.state n t k pre p ⟨h, none⟩ u *
          hermPart (coherentAverage k (base n) F)).trace.re
    rw [re_trace_mul_hermPart (D.posSemidef_state hD ht hcomm pre p _ u).isHermitian,
      trace_mul_coherentAverage k (base n) hF]

/-- For a continuous symbol, `p ↦ J_h(F)` is almost everywhere strongly measurable on
`(0, 1)`. The vector `pre` may be zero. -/
theorem aestronglyMeasurable_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (h : H)
    {F : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hF : Continuous F) :
    AEStronglyMeasurable (fun p => D.oldFourierCoherentIntegral n t k pre p h F)
      (volume.restrict (Ioo 0 1)) := by
  by_cases hpre : pre = 0
  · subst pre
    simpa only [oldFourierCoherentIntegral_zero_pre] using
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
        (volume.restrict (Ioo 0 1)))
  · refine (D.aestronglyMeasurable_integral_state hD ht hcomm hpre h
      (isHermitian_hermPart (coherentAverage k (base n) F))).congr ?_
    exact Filter.Eventually.of_forall fun p =>
      (D.oldFourierCoherentIntegral_eq_integral_hermPart n hD ht hcomm pre p h hF).symm

/-- For a continuous symbol and an interpolation parameter in `(0, 1)`,
`|J_h(F)| ≤ ‖herm(𝒬_k F)‖ / 2`. The vector `pre` may be zero. -/
theorem abs_oldFourierCoherentIntegral_le (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (h : H) {F : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hF : Continuous F) :
    |D.oldFourierCoherentIntegral n t k pre p h F| ≤
      ‖hermPart (coherentAverage k (base n) F)‖ / 2 := by
  by_cases hpre : pre = 0
  · subst pre
    rw [oldFourierCoherentIntegral_zero_pre, abs_zero]
    positivity
  · rw [D.oldFourierCoherentIntegral_eq_integral_hermPart n hD ht hcomm pre p h hF]
    exact D.abs_integral_state_le hD ht hcomm hpre hp ⟨h, none⟩
      (isHermitian_hermPart _)

/-- For a continuous symbol, `p ↦ J_h(F)` is integrable on `(0, 1)`. -/
theorem integrableOn_Ioo_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (h : H)
    {F : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hF : Continuous F) :
    IntegrableOn (fun p => D.oldFourierCoherentIntegral n t k pre p h F) (Ioo 0 1) := by
  refine ⟨D.aestronglyMeasurable_oldFourierCoherentIntegral n hD ht hcomm pre h hF,
    HasFiniteIntegral.restrict_of_bounded
      (C := ‖hermPart (coherentAverage k (base n) F)‖ / 2) (by simp) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
  rw [Real.norm_eq_abs]
  exact D.abs_oldFourierCoherentIntegral_le n hD ht hcomm pre hp h hF

/-- For a continuous symbol, `p ↦ J_h(F)` is interval integrable on `[0, 1]`: the endpoints
form a null set. -/
theorem intervalIntegrable_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (h : H)
    {F : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hF : Continuous F) :
    IntervalIntegrable (fun p => D.oldFourierCoherentIntegral n t k pre p h F) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
    (D.integrableOn_Ioo_oldFourierCoherentIntegral n hD ht hcomm pre h hF)

/-- For a continuous symbol, `p ↦ J_h(F)` is integrable on the closed interval `[0, 1]`. -/
theorem integrableOn_Icc_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (h : H)
    {F : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hF : Continuous F) :
    IntegrableOn (fun p => D.oldFourierCoherentIntegral n t k pre p h F) (Icc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (D.intervalIntegrable_oldFourierCoherentIntegral n hD ht hcomm pre h hF)

/-- For a continuous symbol, `p ↦ J_h(F)` is almost everywhere strongly measurable on the
closed interval `[0, 1]`. -/
theorem aestronglyMeasurable_Icc_oldFourierCoherentIntegral (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (h : H)
    {F : ((∀ v, Fin (n v)) → ℂ) → ℝ} (hF : Continuous F) :
    AEStronglyMeasurable (fun p => D.oldFourierCoherentIntegral n t k pre p h F)
      (volume.restrict (Icc 0 1)) :=
  (D.integrableOn_Icc_oldFourierCoherentIntegral n hD ht hcomm pre h hF).aestronglyMeasurable

/-- For continuous symbols `F_h`, real weights `w_h` and a set of histories, the sum
`∑_{h good} w_h J_h(F_h)` is almost everywhere strongly measurable in the interpolation
parameter on `(0, 1)`. -/
theorem aestronglyMeasurable_sum_oldFourierCoherentIntegral [Fintype H] (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ)
    (good : H → Prop) [DecidablePred good] (w : H → ℝ)
    (F : H → ((∀ v, Fin (n v)) → ℂ) → ℝ) (hF : ∀ h, Continuous (F h)) :
    AEStronglyMeasurable (fun p => ∑ h, if good h then
      w h * D.oldFourierCoherentIntegral n t k pre p h (F h) else 0)
      (volume.restrict (Ioo 0 1)) := by
  apply Finset.aestronglyMeasurable_fun_sum
  intro h _
  by_cases hg : good h
  · simp only [hg, ↓reduceIte]
    exact aestronglyMeasurable_const.mul
      (D.aestronglyMeasurable_oldFourierCoherentIntegral n hD ht hcomm pre h (hF h))
  · simp only [hg, ↓reduceIte]
    exact aestronglyMeasurable_const

/-- For continuous symbols `F_h`, real weights `w_h` and a set of histories, the sum
`∑_{h good} w_h J_h(F_h)` is interval integrable in the interpolation parameter on
`[0, 1]`. -/
theorem intervalIntegrable_sum_oldFourierCoherentIntegral [Fintype H] (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ)
    (good : H → Prop) [DecidablePred good] (w : H → ℝ)
    (F : H → ((∀ v, Fin (n v)) → ℂ) → ℝ) (hF : ∀ h, Continuous (F h)) :
    IntervalIntegrable (fun p => ∑ h, if good h then
      w h * D.oldFourierCoherentIntegral n t k pre p h (F h) else 0) volume 0 1 := by
  have hint (h : H) : IntervalIntegrable (fun p => if good h then
      w h * D.oldFourierCoherentIntegral n t k pre p h (F h) else 0) volume 0 1 := by
    by_cases hg : good h
    · simp only [hg, ↓reduceIte]
      exact (D.intervalIntegrable_oldFourierCoherentIntegral n hD ht hcomm pre h (hF h)).const_mul _
    · simp only [hg, ↓reduceIte]
      exact intervalIntegrable_const
  convert IntervalIntegrable.sum Finset.univ (fun h _ => hint h) using 1
  ext p
  simp only [Finset.sum_apply]

/-! ### The choice-averaged move entropy and the entropy gain -/

variable [∀ h, Fintype (C h)]

/-- The choice-averaged move entropy `G_h(θ) = ∑_g ∑_c q_{c|h} η_{h,c,g}(θ)` of a history
`h`: in every band, the entropies of the moves from the old partition of `h` are averaged
with the conditional choice weights. -/
def choiceEntropySymbol (h : H) (θ : (∀ v, Fin (n v)) → ℂ) : ℝ :=
  ∑ g, ∑ c, (D.choiceTree h).weight c *
    moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ)

omit [DecidableEq H] [∀ v, NeZero (n v)] in
/-- The choice-averaged move entropy is continuous in the one-copy vector. -/
theorem continuous_choiceEntropySymbol (h : H) : Continuous (D.choiceEntropySymbol n h) := by
  unfold choiceEntropySymbol
  exact continuous_finsetSum _ fun g _ => continuous_finsetSum _ fun c _ =>
    continuous_const.mul (continuous_moveEta (D.old h g) (D.move h c g))

omit [∀ v, NeZero (n v)] in
/-- For admissible transport data the choice-averaged move entropy is nonnegative: the
choice weights are positive and every valid move has nonnegative entropy. -/
theorem choiceEntropySymbol_nonneg (hD : D.IsAdmissible) (h : H)
    (θ : (∀ v, Fin (n v)) → ℂ) : 0 ≤ D.choiceEntropySymbol n h θ := by
  apply Finset.sum_nonneg
  intro g _
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (hD.choiceWeight_pos h c).le
    (moveEta_nonneg n _ (hD.old_isPartition h g) _ (hD.move_isValid h c g) _)

variable [Fintype H]

/-- The entropy gain is the history average `∑_h w_h J_h(G_h)` of the old-leaf integrals of
the choice-averaged move entropies (`06-transport.tex`, display `transport:entropy-gain`).
The weights are the history weights `w_h`, without the terminal factor `1 - p`. -/
theorem entropyGain_eq_sum_oldFourierCoherentIntegral (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) :
    D.entropyGain n t k pre p =
      ∑ h, D.histTree.weight h *
        D.oldFourierCoherentIntegral n t k pre p h (D.choiceEntropySymbol n h) := by
  unfold entropyGain
  apply Finset.sum_congr rfl
  intro h _
  let f (g : Fin K) (θ : (∀ v, Fin (n v)) → ℂ) : ℝ :=
    ∑ c, (D.choiceTree h).weight c *
      moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ)
  have hcont (g : Fin K) : Continuous (f g) :=
    continuous_finsetSum _ fun c _ =>
      continuous_const.mul (continuous_moveEta (D.old h g) (D.move h c g))
  have hsymbol : D.choiceEntropySymbol n h = (fun θ => ∑ g, f g θ) := rfl
  have hsum :
      D.oldFourierCoherentIntegral n t k pre p h (D.choiceEntropySymbol n h) =
        ∑ g, D.oldFourierCoherentIntegral n t k pre p h (f g) :=
    (congrArg (D.oldFourierCoherentIntegral n t k pre p h) hsymbol).trans
      (D.oldFourierCoherentIntegral_sum n t k pre p h Finset.univ f
        (fun g _ => hcont g))
  change (∑ g, D.histTree.weight h *
      D.oldFourierCoherentIntegral n t k pre p h (f g)) =
    D.histTree.weight h *
      D.oldFourierCoherentIntegral n t k pre p h (D.choiceEntropySymbol n h)
  exact (Finset.mul_sum Finset.univ
    (fun g => D.oldFourierCoherentIntegral n t k pre p h (f g)) (D.histTree.weight h)).symm.trans
      (congrArg (fun x : ℝ => D.histTree.weight h * x) hsum.symm)

/-- The entropy gain of admissible transport data is nonnegative: by strong subadditivity
every move entropy is nonnegative (`06-transport.tex`, lines 321–330), the history weights
are positive, and the old-leaf integrals preserve the sign. The vector `pre` may vanish and
the interpolation parameter is arbitrary. -/
theorem entropyGain_nonneg (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hcomm : D.CrossBandCommute n t k)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) :
    0 ≤ D.entropyGain n t k pre p := by
  rw [D.entropyGain_eq_sum_oldFourierCoherentIntegral n t k pre p]
  apply Finset.sum_nonneg
  intro h _
  exact mul_nonneg (hD.histWeight_pos h).le
    (D.oldFourierCoherentIntegral_nonneg n hD ht hcomm pre p h
      (D.choiceEntropySymbol_nonneg n hD h))

end OldLeaf

/-- The choice-averaged move entropy is at most `2Kℓ` on unit vectors when every move has
logarithmic dimension at most `ℓ`: each of the `K` bands contributes one probability average
of move entropies (`08-scanner.tex`, lines 434–440). -/
theorem choiceEntropySymbol_le_of_logDim_move_le (n : V → ℕ) [∀ v, NeZero (n v)]
    [∀ h, Fintype (C h)] (D : TransportData V K H C) (hD : D.IsAdmissible) {ℓ : ℝ}
    (hmove : ∀ h c g, logDim n (D.move h c g).subsystem ≤ ℓ) (h : H)
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) (hθ : ‖θ‖ = 1) :
    D.choiceEntropySymbol n h (fun x => θ x) ≤ K * (2 * ℓ) := by
  classical
  unfold choiceEntropySymbol
  calc
    _ ≤ ∑ _g : Fin K, ∑ c, (D.choiceTree h).weight c * (2 * ℓ) := by
      refine Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun c _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ ((D.choiceTree h).weight_nonneg c)
      exact (moveEta_le_two_mul_logDim n _ (hD.old_isPartition h g) _
        (hD.move_isValid h c g) θ hθ).trans
        (mul_le_mul_of_nonneg_left (hmove h c g) (by norm_num))
    _ = K * (2 * ℓ) := by
      simp [← Finset.sum_mul, (D.choiceTree h).sum_weight]

end TensorPower.ReplicaTransport.TransportData
