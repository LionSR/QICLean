/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.Setup

/-!
# The logarithmic passage from a rank-one pin to every symmetric state

Let `X` be positive definite, commuting with copy permutations, with
`X ≥ e^{φ(θ)} P_{θ,k}` for every unit `θ`. Then for every density matrix `ρ` on `𝒮_k`,
`∫ φ dμ_ρ - log D_k ≤ Tr(ρ log X)`.

The source argument (area-law paper, proof of Proposition 7.4, `06-transport.tex`
lines 520--575): integrating the pin against Haar measure gives
`X ≥ D_k^{-1} 𝒬_k(e^φ)` on `𝒮_k`, where `𝒬_k(f) = D_k ∫ f(θ) P_{θ,k} dθ` is unital
(coherent-state resolution, `TensorPower.unitaryTwirl_coherentProj`); the block-matrix
inequality `𝒬_k(f)^{-1} ≤ 𝒬_k(f^{-1})` and the resolvent formula for `log` give the
operator Jensen inequality `log 𝒬_k(f) ≥ 𝒬_k(log f)` (display `transport:log-jensen`);
operator monotonicity of `log` concludes. Everything takes place on `𝒮_k`, where
`𝒬_k(1)` is the identity.

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory PermutationRepresentation

noncomputable section

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The coherent-state vector `U e_a` is continuous in `U`. -/
theorem continuous_coherentVec (a : Ω) :
    Continuous fun U : unitaryGroup Ω ℂ => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1 := by
  refine continuous_pi fun x => ?_
  simp only [mulVec, dotProduct]
  exact continuous_finsetSum _ fun y _ => (continuous_unitary_apply Ω _ _).mul continuous_const

omit [Fintype Ω] [DecidableEq Ω] in
/-- The coherent projector `P_{θ,k}` depends continuously on `θ`. -/
theorem continuous_coherentProj {X : Type*} [TopologicalSpace X] (k : ℕ) {θ : X → Ω → ℂ}
    (hθ : Continuous θ) : Continuous fun x => coherentProj k (θ x) := by
  refine continuous_pi fun y => continuous_pi fun z => ?_
  simp only [coherentProj, vecMulVec_apply, tensorVec, Pi.star_apply, star_prod]
  fun_prop

/-- The integrand of a coherent average is Haar integrable. -/
theorem integrable_coherentIntegrand (k : ℕ) (a : Ω) {f : (Ω → ℂ) → ℝ} (hf : Continuous f) :
    Integrable (fun U : unitaryGroup Ω ℂ => (f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) : ℂ) •
      coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)) (unitaryHaar Ω) :=
  ((Complex.continuous_ofReal.comp (hf.comp (continuous_coherentVec a))).smul
    (continuous_coherentProj k (continuous_coherentVec a))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The letter counts of a word of length `k`. -/
def letterCount (k : ℕ) (x : Fin k → Ω) : Ω → Fin (k + 1) := fun c =>
  ⟨(Finset.univ.filter fun j => x j = c).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

omit [Fintype Ω] in
/-- Two words with the same letter counts differ by a permutation of the positions. -/
theorem exists_perm_of_letterCount_eq {k : ℕ} {x y : Fin k → Ω}
    (h : letterCount k x = letterCount k y) : ∃ σ : Equiv.Perm (Fin k), y ∘ σ = x := by
  have e : ∀ c, {j // x j = c} ≃ {j // y j = c} := fun c => Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact congrArg Fin.val (congrFun h c))
  exact ⟨Equiv.ofFiberEquiv e, funext fun j => Equiv.ofFiberEquiv_map e j⟩

/-- A symmetric vector is invariant under permuting the positions of its argument. -/
theorem apply_comp_of_mem_invariantSubspace {k : ℕ} {v : (Fin k → Ω) → ℂ}
    (hv : v ∈ invariantSubspace (copyPerm Ω k)) (x : Fin k → Ω) (σ : Equiv.Perm (Fin k)) :
    v (x ∘ σ) = v x := by
  have := congrFun (hv σ) x
  rw [permOp_mulVec, Function.comp_apply, ← map_inv] at this
  rw [show x ∘ σ = copyPerm Ω k σ⁻¹ x from funext fun j => by rw [copyPerm_apply, inv_inv]; rfl]
  exact this

/-- `D_k ≤ (k + 1)^{dim}`: a symmetric vector is determined by its values on one word of each
letter-count profile. -/
theorem symDim_le (k : ℕ) : symDim Ω k ≤ (k + 1) ^ Fintype.card Ω := by
  classical
  let R := Set.range (letterCount (Ω := Ω) k)
  let rep : R → (Fin k → Ω) := fun c => c.2.choose
  let L : invariantSubspace (copyPerm Ω k) →ₗ[ℂ] (R → ℂ) :=
    { toFun := fun v c => (v : (Fin k → Ω) → ℂ) (rep c)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    ext x
    let c : R := ⟨letterCount k x, x, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_perm_of_letterCount_eq (c.2.choose_spec)
    have h0 : (v : (Fin k → Ω) → ℂ) (rep c) = 0 := congrFun hv c
    rw [show rep c = x ∘ σ from hσ.symm, apply_comp_of_mem_invariantSubspace v.2] at h0
    simpa using h0
  calc symDim Ω k ≤ Module.finrank ℂ (R → ℂ) := LinearMap.finrank_le_finrank_of_injective hL
    _ = Fintype.card R := Module.finrank_fintype_fun_eq_card ℂ
    _ ≤ Fintype.card (Ω → Fin (k + 1)) := Fintype.card_subtype_le _
    _ = (k + 1) ^ Fintype.card Ω := by simp

/-- The symmetric projector is idempotent. -/
theorem symProj_mul_self (k : ℕ) :
    symProj (copyPerm Ω k) * symProj (copyPerm Ω k) = symProj (copyPerm Ω k) := by
  nth_rewrite 1 [symProj]
  rw [smul_mul_assoc, Finset.sum_mul]
  simp_rw [permOp_mul_symProj]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]

/-- `Tr Π_k = D_k`. -/
theorem trace_symProj (k : ℕ) : (symProj (copyPerm Ω k)).trace = symDim Ω k := by
  have hR : LinearMap.range (Matrix.toLin' (symProj (copyPerm Ω k))) =
      invariantSubspace (copyPerm Ω k) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [Matrix.toLin'_apply]
      exact symProj_mulVec_mem _ v
    · intro v hv
      exact ⟨v, by rw [Matrix.toLin'_apply]; exact symProj_mulVec_of_mem _ hv⟩
  rw [trace_eq_finrank_range_of_mul_self (symProj_mul_self k), hR]

/-- `D_k ≥ 1`: the product vector `e_a^{⊗k}` is symmetric and nonzero. -/
theorem symDim_pos (k : ℕ) (a : Ω) : 0 < symDim Ω k := by
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨tensorVec k (Pi.single a 1), tensorVec_mem_symmetricSubspace _⟩, fun h => ?_⟩
  have := congrFun (congrArg Subtype.val h) (fun _ => a)
  simp [tensorVec] at this

/-- The coherent average `𝒬_k(f) = D_k ∫ f(θ) P_{θ,k} dθ` (`06-transport.tex` line 523). -/
def coherentAverage (k : ℕ) (a : Ω) (f : (Ω → ℂ) → ℝ) : Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  (symDim Ω k : ℂ) • ∫ U, (f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) : ℂ) •
    coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ∂(unitaryHaar Ω)

/-- Tracing a coherent average against `ρ` gives the coherent integral. -/
theorem trace_mul_coherentAverage (k : ℕ) (a : Ω) {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) :
    (ρ * coherentAverage k a f).trace.re = realCoherentIntegral k a ρ f := by
  have hF := integrable_coherentIntegrand k a hf
  let L : Matrix (Fin k → Ω) (Fin k → Ω) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap _ ℂ ℂ) ∘ₗ LinearMap.mulLeft ℂ ρ)
  have hL : ∀ M, L M = (ρ * M).trace := fun M => rfl
  have hint : Integrable (fun U : unitaryGroup Ω ℂ => L ((f ((U : Matrix Ω Ω ℂ) *ᵥ
      Pi.single a 1) : ℂ) • coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)))
      (unitaryHaar Ω) := L.integrable_comp hF
  rw [realCoherentIntegral, coherentAverage, mul_smul_comm, trace_smul, ← hL,
    ← L.integral_comp_comm hF, smul_eq_mul, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  congr 1
  rw [← RCLike.re_to_complex, ← integral_re hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [hL, mul_smul_comm, trace_smul, smul_eq_mul, RCLike.re_to_complex,
    Complex.re_ofReal_mul]

/-- **Coherent-state resolution** in the form `𝒬_k(1) = Π_k`. -/
theorem coherentAverage_one (k : ℕ) (a : Ω) :
    coherentAverage k a (fun _ => 1) = symProj (copyPerm Ω k) := by
  have hD : (symDim Ω k : ℂ) ≠ 0 := by exact_mod_cast (symDim_pos k a).ne'
  have hF := integrable_coherentIntegrand k a (f := fun _ => 1) continuous_const
  ext x y
  let L : Matrix (Fin k → Ω) (Fin k → Ω) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ x y)
  have hL : ∀ M, L M = M x y := fun M => rfl
  have hres := congrFun (congrFun (unitaryTwirl_coherentProj (k := k) a) x) y
  rw [trace_symProj] at hres
  rw [coherentAverage, Matrix.smul_apply, ← hL (∫ U, _ ∂(unitaryHaar Ω)), ← L.integral_comp_comm hF]
  simp only [hL, Complex.ofReal_one, one_smul, coherentProj_mulVec]
  change _ * unitaryTwirl (coherentProj k (Pi.single a 1)) x y = _
  rw [hres, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]

/-- The coherent measure of a state on `𝒮_k` has total mass one. -/
theorem realCoherentIntegral_one {k : ℕ} (a : Ω) {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}
    (htr : ρ.trace = 1) (hsym : symProj (copyPerm Ω k) * ρ = ρ) :
    realCoherentIntegral k a ρ (fun _ => 1) = 1 := by
  rw [← trace_mul_coherentAverage k a continuous_const, coherentAverage_one, trace_mul_comm, hsym,
    htr, Complex.one_re]

/-- The coherent integrand of a continuous function is Haar integrable. -/
theorem integrable_realCoherentIntegral_integrand (k : ℕ) (a : Ω)
    (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) {g : (Ω → ℂ) → ℝ} (hg : Continuous g) :
    Integrable (fun U : unitaryGroup Ω ℂ => g ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) *
      (ρ * coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)).trace.re) (unitaryHaar Ω) :=
  ((hg.comp (continuous_coherentVec a)).mul (Complex.continuous_re.comp
    ((continuous_const.mul (continuous_coherentProj k (continuous_coherentVec a))).matrix_trace))
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The coherent integral against a state on `𝒮_k` is affine in the integrand. -/
theorem realCoherentIntegral_affine {k : ℕ} (a : Ω) {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}
    (htr : ρ.trace = 1) (hsym : symProj (copyPerm Ω k) * ρ = ρ) {F : (Ω → ℂ) → ℝ}
    (hF : Continuous F) (α β : ℝ) :
    realCoherentIntegral k a ρ (fun θ => α + β * F θ) = α + β * realCoherentIntegral k a ρ F := by
  have h1 := realCoherentIntegral_one a htr hsym
  unfold realCoherentIntegral at h1 ⊢
  beta_reduce at h1 ⊢
  set w : unitaryGroup Ω ℂ → ℝ := fun U =>
    (ρ * coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)).trace.re with hw
  have hI : ∫ U, (α + β * F ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)) * w U ∂(unitaryHaar Ω) =
      α * ∫ U, 1 * w U ∂(unitaryHaar Ω) +
        β * ∫ U, F ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) * w U ∂(unitaryHaar Ω) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      ((integrable_realCoherentIntegral_integrand k a ρ continuous_const).const_mul α)
      ((integrable_realCoherentIntegral_integrand k a ρ hF).const_mul β)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun U => by ring)
  rw [hI]
  linear_combination α * h1

section LogResolvent

open Set Filter Topology

/-- The resolvent kernel `1/(1+s) - 1/(x+s)` of the logarithm. -/
def logKernel (s x : ℝ) : ℝ := (1 + s)⁻¹ - (x + s)⁻¹

/-- The antiderivative `log(1+s) - log(x+s)` of the kernel in `s`. -/
private theorem hasDerivAt_logKernel_primitive {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) :
    HasDerivAt (fun s => Real.log (1 + s) - Real.log (x + s)) (logKernel s x) s := by
  have h1 : (1 + s) ≠ 0 := by positivity
  have h2 : (x + s) ≠ 0 := by positivity
  have := (((hasDerivAt_id s).const_add 1).log h1).sub (((hasDerivAt_id s).const_add x).log h2)
  convert this using 1
  · rfl
  · simp [logKernel]

private theorem tendsto_logKernel_primitive {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s => Real.log (1 + s) - Real.log (x + s)) atTop (𝓝 0) := by
  have hq : Tendsto (fun s : ℝ => 1 + (1 - x) / (x + s)) atTop (𝓝 1) := by
    have : Tendsto (fun s : ℝ => (1 - x) / (x + s)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_id)
    simpa using this.const_add 1
  have hlog := ((Real.continuousAt_log one_ne_zero).tendsto.comp hq)
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have h1 : (0 : ℝ) < 1 + s := by linarith
  have h2 : 0 < x + s := by linarith
  simp only [Function.comp]
  rw [← Real.log_div h1.ne' h2.ne']
  congr 1
  field_simp
  ring

/-- **Resolvent representation of the logarithm**: for `x > 0`,
`log x = ∫_0^∞ (1/(1+s) - 1/(x+s)) ds`, and the integrand is integrable. -/
theorem integrableOn_logKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s => logKernel s x) (Ioi 0) := by
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (fun s => Real.log (1 + s) - Real.log (x + s))
      (logKernel s x) s := fun s hs => hasDerivAt_logKernel_primitive hx hs
  rcases le_total 1 x with h | h
  · refine integrableOn_Ioi_deriv_of_nonneg' hd (fun s hs => ?_) (tendsto_logKernel_primitive hx)
    have hs : (0 : ℝ) < s := hs
    simp only [logKernel, sub_nonneg]
    exact inv_anti₀ (by linarith) (by linarith)
  · refine integrableOn_Ioi_deriv_of_nonpos ?_ (fun s hs => hd s (Ioi_subset_Ici_self hs))
      (fun s hs => ?_)
      (tendsto_logKernel_primitive hx)
    · exact (hd 0 self_mem_Ici).continuousAt.continuousWithinAt
    have hs : (0 : ℝ) < s := hs
    simp only [logKernel, sub_nonpos]
    exact inv_anti₀ (by linarith) (by linarith)

theorem integral_logKernel {x : ℝ} (hx : 0 < x) :
    ∫ s in Ioi 0, logKernel s x = Real.log x := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun s hs => hasDerivAt_logKernel_primitive hx hs)
    (integrableOn_logKernel hx) (tendsto_logKernel_primitive hx)]
  simp

/-- The kernel is monotone in `x`. -/
theorem logKernel_mono {s x y : ℝ} (hs : 0 ≤ s) (hx : 0 < x) (hxy : x ≤ y) :
    logKernel s x ≤ logKernel s y := by
  simp only [logKernel]
  have : (y + s)⁻¹ ≤ (x + s)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  linarith

/-- A two-sided integrable bound for the kernel on `[m, M]`. -/
theorem abs_logKernel_le {s x m M : ℝ} (hs : 0 ≤ s) (hm : 0 < m) (hmx : m ≤ x) (hxM : x ≤ M) :
    |logKernel s x| ≤ |logKernel s m| + |logKernel s M| := by
  have h1 := logKernel_mono hs hm hmx
  have h2 := logKernel_mono hs (hm.trans_le hmx) hxM
  rw [abs_le]
  constructor <;> cases abs_cases (logKernel s m) <;> cases abs_cases (logKernel s M) <;> linarith

end LogResolvent

section MatrixLog

open Set Filter

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The spectrum of a positive definite matrix lies in a compact interval `[lo, hi]` with
`lo > 0`. -/
theorem exists_spectrum_subset_Icc {X : Matrix m m ℂ} (hX : X.PosDef) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ ∀ z ∈ spectrum ℝ X, lo ≤ z ∧ z ≤ hi := by
  rcases (spectrum ℝ X).eq_empty_or_nonempty with he | hne
  · exact ⟨1, 1, one_pos, le_rfl, by simp [he]⟩
  obtain ⟨zl, hzl, hl⟩ := (spectrum.isCompact X).exists_isMinOn hne continuousOn_id
  obtain ⟨zh, hzh, hh⟩ := (spectrum.isCompact X).exists_isMaxOn hne continuousOn_id
  exact ⟨zl, zh, hX.isStrictlyPositive.spectrum_pos hzl, hl hzh, fun z hz => ⟨hl hz, hh hz⟩⟩

/-- **Resolvent representation of the matrix logarithm**:
`log X = ∫_0^∞ k_s(X) ds` with `k_s(x) = 1/(1+s) - 1/(x+s)`, for positive definite `X`. -/
theorem integrableOn_cfc_logKernel {X : Matrix m m ℂ} (hX : X.PosDef) :
    IntegrableOn (fun s => cfc (logKernel s) X) (Ioi 0) ∧
      CFC.log X = ∫ s in Ioi 0, cfc (logKernel s) X := by
  obtain ⟨lo, hi, hlo, hlohi, hsp⟩ := exists_spectrum_subset_Icc hX
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hcont : ContinuousOn (Function.uncurry logKernel) (Ioi 0 ×ˢ spectrum ℝ X) := by
    refine ContinuousOn.sub ?_ ?_
    · refine (continuousOn_const.add continuousOn_fst).inv₀ fun q hq => ?_
      have : (0 : ℝ) < q.1 := hq.1
      exact (by linarith : (0 : ℝ) < 1 + q.1).ne'
    · refine (continuousOn_snd.add continuousOn_fst).inv₀ fun q hq => ?_
      have h1 : (0 : ℝ) < q.1 := hq.1
      have h2 := (hsp _ hq.2).1
      have : 0 < q.2 + q.1 := by linarith
      exact this.ne'
  have hbound : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ spectrum ℝ X,
      ‖logKernel s z‖ ≤ |logKernel s lo| + |logKernel s hi| :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun s hs z hz => by
      rw [Real.norm_eq_abs]
      exact abs_logKernel_le (le_of_lt hs) hlo (hsp z hz).1 (hsp z hz).2
  have hbi : MeasureTheory.HasFiniteIntegral (fun s => |logKernel s lo| + |logKernel s hi|)
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    ((integrableOn_logKernel hlo).abs.add (integrableOn_logKernel hhi).abs).hasFiniteIntegral
  refine ⟨integrableOn_cfc measurableSet_Ioi logKernel _ X hcont hbound hbi, ?_⟩
  rw [← cfc_setIntegral measurableSet_Ioi logKernel _ X hcont hbound hbi, CFC.log]
  refine cfc_congr fun z hz => ?_
  exact (integral_logKernel (hlo.trans_le (hsp z hz).1)).symm

/-- The resolvent `(X + s)⁻¹` through the functional calculus. -/
noncomputable def resolvent (X : Matrix m m ℂ) (s : ℝ) : Matrix m m ℂ :=
  cfc (fun x : ℝ => (x + s)⁻¹) X

theorem cfc_logKernel {X : Matrix m m ℂ} (hX : X.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    cfc (logKernel s) X = (1 + s)⁻¹ • (1 : Matrix m m ℂ) - resolvent X s := by
  have hc : ContinuousOn (fun x : ℝ => (x + s)⁻¹) (spectrum ℝ X) :=
    (continuousOn_id.add continuousOn_const).inv₀ fun z hz => by
      have := hX.isStrictlyPositive.spectrum_pos hz
      exact (by simp only [id_eq]; linarith : (0 : ℝ) < id z + s).ne'
  rw [show logKernel s = fun x => (fun _ => (1 + s)⁻¹) x - (fun x : ℝ => (x + s)⁻¹) x from rfl,
    cfc_sub _ _ X continuousOn_const hc, cfc_const _ X hX.isHermitian.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one, resolvent]

theorem add_smul_one_mul_resolvent {X : Matrix m m ℂ} (hX : X.PosDef) {s : ℝ} (hs : 0 ≤ s) :
    (X + s • (1 : Matrix m m ℂ)) * resolvent X s = 1 := by
  have hX' : IsSelfAdjoint X := hX.isHermitian.isSelfAdjoint
  have hpos : ∀ z ∈ spectrum ℝ X, z + s ≠ 0 := fun z hz => by
    have := hX.isStrictlyPositive.spectrum_pos hz
    exact (by linarith : (0 : ℝ) < z + s).ne'
  have hc : ContinuousOn (fun x : ℝ => (x + s)⁻¹) (spectrum ℝ X) :=
    (continuousOn_id.add continuousOn_const).inv₀ hpos
  have hlin : cfc (fun x : ℝ => x + s) X = X + s • (1 : Matrix m m ℂ) := by
    rw [cfc_add_const s (fun x : ℝ => x) X continuousOn_id hX', cfc_id' ℝ X hX',
      Algebra.algebraMap_eq_smul_one]
  rw [← hlin, resolvent, ← cfc_mul (fun x : ℝ => x + s) (fun x : ℝ => (x + s)⁻¹) X
    (continuousOn_id.add continuousOn_const) hc, ← cfc_one ℝ X hX']
  exact cfc_congr fun z hz => mul_inv_cancel₀ (hpos z hz)

theorem commute_resolvent {X Y : Matrix m m ℂ} (h : Commute X Y) (s : ℝ) :
    Commute (resolvent X s) Y :=
  Commute.cfc_real h _

theorem isHermitian_resolvent (X : Matrix m m ℂ) (s : ℝ) : (resolvent X s).IsHermitian :=
  cfc_predicate (p := IsSelfAdjoint) _ X

end MatrixLog

section AverageAlgebra

variable (k : ℕ) (a : Ω)

/-- The symmetric projector is Hermitian. -/
theorem isHermitian_symProj : (symProj (copyPerm Ω k)).IsHermitian := by
  rw [IsHermitian, symProj, conjTranspose_smul, conjTranspose_sum]
  simp_rw [conjTranspose_permOp]
  congr 1
  · simp
  · exact Fintype.sum_equiv (Equiv.inv _) _ _ fun _ => rfl

omit [DecidableEq Ω] in
set_option linter.unusedFintypeInType false in
theorem isHermitian_coherentProj (θ : Ω → ℂ) : (coherentProj k θ).IsHermitian :=
  (posSemidef_vecMulVec_self_star _).isHermitian

theorem symProj_mul_coherentProj (θ : Ω → ℂ) :
    symProj (copyPerm Ω k) * coherentProj k θ = coherentProj k θ := by
  rw [coherentProj, mul_vecMulVec, symProj_mulVec_of_mem _ (tensorVec_mem_symmetricSubspace θ)]

theorem coherentProj_mul_symProj (θ : Ω → ℂ) :
    coherentProj k θ * symProj (copyPerm Ω k) = coherentProj k θ := by
  have h := congrArg conjTranspose (symProj_mul_coherentProj k θ)
  rwa [conjTranspose_mul, (isHermitian_symProj k).eq, (isHermitian_coherentProj k θ).eq] at h

/-- Left multiplication by a fixed matrix commutes with the Haar integral. -/
theorem mul_integral {X : Type*} [Fintype X] [DecidableEq X] (B : Matrix X X ℂ)
    {F : unitaryGroup Ω ℂ → Matrix X X ℂ} (hF : Integrable F (unitaryHaar Ω)) :
    B * ∫ U, F U ∂(unitaryHaar Ω) = ∫ U, B * F U ∂(unitaryHaar Ω) :=
  ((ContinuousLinearMap.mul ℂ (Matrix X X ℂ)) B).integral_comp_comm hF |>.symm

/-- Right multiplication by a fixed matrix commutes with the Haar integral. -/
theorem integral_mul {X : Type*} [Fintype X] [DecidableEq X] (B : Matrix X X ℂ)
    {F : unitaryGroup Ω ℂ → Matrix X X ℂ} (hF : Integrable F (unitaryHaar Ω)) :
    (∫ U, F U ∂(unitaryHaar Ω)) * B = ∫ U, F U * B ∂(unitaryHaar Ω) :=
  ((ContinuousLinearMap.mul ℂ (Matrix X X ℂ)).flip B).integral_comp_comm hF |>.symm

theorem symProj_mul_coherentAverage {f : (Ω → ℂ) → ℝ} (hf : Continuous f) :
    symProj (copyPerm Ω k) * coherentAverage k a f = coherentAverage k a f := by
  rw [coherentAverage, mul_smul_comm, mul_integral _ (integrable_coherentIntegrand k a hf)]
  simp_rw [mul_smul_comm, symProj_mul_coherentProj]

theorem coherentAverage_mul_symProj {f : (Ω → ℂ) → ℝ} (hf : Continuous f) :
    coherentAverage k a f * symProj (copyPerm Ω k) = coherentAverage k a f := by
  rw [coherentAverage, smul_mul_assoc, integral_mul _ (integrable_coherentIntegrand k a hf)]
  simp_rw [smul_mul_assoc, coherentProj_mul_symProj]

theorem coherentAverage_sub {f g : (Ω → ℂ) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    coherentAverage k a (fun θ => f θ - g θ) = coherentAverage k a f - coherentAverage k a g := by
  simp only [coherentAverage, ← smul_sub]
  rw [← integral_sub (integrable_coherentIntegrand k a hf) (integrable_coherentIntegrand k a hg)]
  simp_rw [Complex.ofReal_sub, sub_smul]

theorem coherentAverage_add {f g : (Ω → ℂ) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    coherentAverage k a (fun θ => f θ + g θ) = coherentAverage k a f + coherentAverage k a g := by
  simp only [coherentAverage, ← smul_add]
  rw [← integral_add (integrable_coherentIntegrand k a hf) (integrable_coherentIntegrand k a hg)]
  simp_rw [Complex.ofReal_add, add_smul]

theorem coherentAverage_const (c : ℝ) :
    coherentAverage k a (fun _ => c) = c • symProj (copyPerm Ω k) := by
  rw [← coherentAverage_one k a, coherentAverage, coherentAverage, smul_comm]
  congr 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), ← integral_smul]
  simp_rw [smul_smul, Complex.ofReal_one, mul_one]
  rfl

end AverageAlgebra

section Jensen

open Set Filter

variable (k : ℕ) (a : Ω)

/-- The coherent-state vector `U e_a` is a unit vector. -/
theorem star_coherentVec_dotProduct (U : unitaryGroup Ω ℂ) :
    star ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ⬝ᵥ ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) = 1 := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.mp U.2, vecMul_one]
  simp [dotProduct, Pi.single_apply]

/-- A coherent average of a nonnegative function is positive semidefinite. -/
theorem coherentAverage_nonneg {f : (Ω → ℂ) → ℝ}
    (hf0 : ∀ U : unitaryGroup Ω ℂ, 0 ≤ f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)) :
    0 ≤ coherentAverage k a f := by
  rw [Matrix.nonneg_iff_posSemidef, coherentAverage]
  refine PosSemidef.smul ?_ (by exact_mod_cast Nat.zero_le _)
  rw [← Matrix.nonneg_iff_posSemidef]
  refine integral_nonneg fun U => ?_
  rw [Pi.zero_apply, Matrix.nonneg_iff_posSemidef]
  exact (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast hf0 _)

/-- The coherent average is monotone. -/
theorem coherentAverage_mono {f g : (Ω → ℂ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ U : unitaryGroup Ω ℂ,
      f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ≤ g ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)) :
    coherentAverage k a f ≤ coherentAverage k a g := by
  have := coherentAverage_nonneg k a (f := fun θ => g θ - f θ) fun U => sub_nonneg.mpr (hfg U)
  rwa [coherentAverage_sub k a hg hf, sub_nonneg] at this

/-- Left multiplication commutes with a Bochner integral. -/
theorem mul_integral' {α X : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype X]
    [DecidableEq X] (B : Matrix X X ℂ) {F : α → Matrix X X ℂ} (hF : Integrable F μ) :
    B * ∫ x, F x ∂μ = ∫ x, B * F x ∂μ :=
  ((ContinuousLinearMap.mul ℂ (Matrix X X ℂ)) B).integral_comp_comm hF |>.symm

/-- Right multiplication commutes with a Bochner integral. -/
theorem integral_mul' {α X : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype X]
    [DecidableEq X] (B : Matrix X X ℂ) {F : α → Matrix X X ℂ} (hF : Integrable F μ) :
    (∫ x, F x ∂μ) * B = ∫ x, F x * B ∂μ :=
  ((ContinuousLinearMap.mul ℂ (Matrix X X ℂ)).flip B).integral_comp_comm hF |>.symm

/-- **Schwarz step** (`06-transport.tex` lines 526--540): if `X` is Hermitian, supported on
`𝒮_k`, and `X 𝒬_k(g) X = X`, then `X ≤ 𝒬_k(g⁻¹)`. Pointwise,
`g (X - g⁻¹) P_θ (X - g⁻¹) ≥ 0`; integrating gives `X - 2X + 𝒬_k(g⁻¹) ≥ 0`. -/
theorem le_coherentAverage_inv {g : (Ω → ℂ) → ℝ} (hg : Continuous g) (hpos : ∀ θ, 0 < g θ)
    {X : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hX : X.IsHermitian)
    (hXQ : X * coherentAverage k a g * X = X) (hXP : X * symProj (copyPerm Ω k) = X)
    (hPX : symProj (copyPerm Ω k) * X = X) :
    X ≤ coherentAverage k a (fun θ => (g θ)⁻¹) := by
  have hgi : Continuous fun θ => (g θ)⁻¹ := hg.inv₀ fun θ => (hpos θ).ne'
  have hFg := integrable_coherentIntegrand k a hg
  have hF1 := integrable_coherentIntegrand k a (f := fun _ => 1) continuous_const
  have hFi := integrable_coherentIntegrand k a hgi
  have h0 := ((ContinuousLinearMap.mul ℂ _) X).integrable_comp hFg
  have h1 := ((ContinuousLinearMap.mul ℂ _).flip X).integrable_comp h0
  have h2 := ((ContinuousLinearMap.mul ℂ _) X).integrable_comp hF1
  have h3 := ((ContinuousLinearMap.mul ℂ _).flip X).integrable_comp hF1
  simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at h0 h1 h2 h3
  set μ := unitaryHaar Ω
  set θ : unitaryGroup Ω ℂ → Ω → ℂ := fun U => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1
  set P := symProj (copyPerm Ω k)
  have hpt : ∀ U, 0 ≤ X * (((g (θ U) : ℝ) : ℂ) • coherentProj k (θ U)) * X -
      X * (((1 : ℝ) : ℂ) • coherentProj k (θ U)) - ((1 : ℝ) : ℂ) • coherentProj k (θ U) * X +
      (((g (θ U))⁻¹ : ℝ) : ℂ) • coherentProj k (θ U) := by
    intro U
    set r : ℝ := g (θ U)
    have hr : r ≠ 0 := (hpos _).ne'
    set N := X - ((r⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin k → Ω) (Fin k → Ω) ℂ)
    have hN : Nᴴ = N := by
      simp only [N, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq,
        Complex.star_def, Complex.conj_ofReal]
    have hpsd : ((r : ℂ) • (Nᴴ * coherentProj k (θ U) * N)).PosSemidef :=
      ((posSemidef_vecMulVec_self_star _).conjTranspose_mul_mul_same N).smul
        (by exact_mod_cast (hpos _).le)
    rw [Matrix.nonneg_iff_posSemidef]
    convert hpsd using 1
    rw [hN]
    simp only [N, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
      smul_smul, Complex.ofReal_one, one_smul]
    have e1 : (r : ℂ) * (r⁻¹ : ℝ) = 1 := by
      rw [Complex.ofReal_inv, mul_inv_cancel₀ (by exact_mod_cast hr)]
    have e2 : (r : ℂ) * ((r⁻¹ : ℝ) * (r⁻¹ : ℝ)) = (r⁻¹ : ℝ) := by
      rw [← mul_assoc, e1, one_mul]
    rw [e1, e2, one_smul, one_smul]
    simp only [mul_assoc]
    abel
  have hint : 0 ≤ ∫ U, (X * (((g (θ U) : ℝ) : ℂ) • coherentProj k (θ U)) * X -
      X * (((1 : ℝ) : ℂ) • coherentProj k (θ U)) - ((1 : ℝ) : ℂ) • coherentProj k (θ U) * X +
      (((g (θ U))⁻¹ : ℝ) : ℂ) • coherentProj k (θ U)) ∂μ := integral_nonneg fun U => hpt U
  rw [integral_add, integral_sub, integral_sub,
    ← integral_mul' X h0, ← mul_integral' X hFg, ← mul_integral' X hF1,
    ← integral_mul' X hF1] at hint
  rotate_left
  · exact h1
  · exact h2
  · exact h1.sub h2
  · exact h3
  · exact (h1.sub h2).sub h3
  · exact hFi
  have hD : (0 : ℂ) ≤ (symDim Ω k : ℂ) := by exact_mod_cast Nat.zero_le _
  have hfin := (Matrix.nonneg_iff_posSemidef.mp hint).smul hD
  have hQ1 := coherentAverage_one k a
  simp only [coherentAverage] at hXQ hQ1 ⊢
  rw [smul_add, smul_sub, smul_sub, ← smul_mul_assoc, ← mul_smul_comm, hXQ, ← mul_smul_comm,
    ← smul_mul_assoc, hQ1, hXP, hPX] at hfin
  rw [Matrix.le_iff]
  convert hfin using 1
  abel

omit [Fintype Ω] [DecidableEq Ω] in
private theorem mul_resolvent_aux {α : Type*} [Ring α] {P R B : α} (hPP : P * P = P)
    (hRP : Commute R P) (hBP : Commute B P) (hRB : R * B = 1) :
    R * P * (B * P) * (R * P) = R * P := by
  calc R * P * (B * P) * (R * P) = R * (P * B) * (P * (R * P)) := by simp only [mul_assoc]
    _ = R * (B * P) * (P * (R * P)) := by rw [← hBP.eq]
    _ = R * B * ((P * P) * R) * P := by simp only [mul_assoc]
    _ = R * B * (R * P) * P := by rw [hPP, ← hRP.eq]
    _ = (R * B) * R * (P * P) := by simp only [mul_assoc]
    _ = R * P := by rw [hRB, hPP, one_mul]

/-- **Resolvent form of the Jensen step** (`06-transport.tex` lines 526--546): if `Y` is
positive definite, commutes with `Π`, and `Π Y Π = 𝒬_k(f)`, then for each `s ≥ 0`
`𝒬_k(k_s ∘ f) ≤ Π k_s(Y) Π` for the resolvent kernel `k_s(x) = 1/(1+s) - 1/(x+s)`. -/
theorem coherentAverage_logKernel_le {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) {Y : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hY : Y.PosDef)
    (hYP : Commute Y (symProj (copyPerm Ω k)))
    (hPYP : symProj (copyPerm Ω k) * Y * symProj (copyPerm Ω k) = coherentAverage k a f)
    {s : ℝ} (hs : 0 ≤ s) :
    coherentAverage k a (fun θ => logKernel s (f θ)) ≤
      symProj (copyPerm Ω k) * cfc (logKernel s) Y * symProj (copyPerm Ω k) := by
  set P := symProj (copyPerm Ω k) with hPdef
  have hPP : P * P = P := symProj_mul_self k
  have hPh : P.IsHermitian := isHermitian_symProj k
  set R := resolvent Y s with hRdef
  set B := Y + s • (1 : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) with hBdef
  have hBR : B * R = 1 := add_smul_one_mul_resolvent hY hs
  have hRP : Commute R P := commute_resolvent hYP s
  have hBP : Commute B P := hYP.add_left ((Commute.one_left P).smul_left s)
  have hRB' : Commute R B :=
    (commute_resolvent (Commute.refl Y) s).add_right ((Commute.one_right R).smul_right s)
  have hRB : R * B = 1 := by rw [hRB'.eq, hBR]
  have hQf : coherentAverage k a f = Y * P := by
    rw [← hPYP, ← hYP.eq, mul_assoc, hPP]
  have hQs : coherentAverage k a (fun θ => f θ + s) = B * P := by
    rw [coherentAverage_add k a hf continuous_const, coherentAverage_const, hQf, hBdef, add_mul,
      smul_mul_assoc, one_mul]
  have hXdef : P * R * P = R * P := by rw [← hRP.eq, mul_assoc, hPP]
  have hXh : (P * R * P).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, hPh.eq, (isHermitian_resolvent Y s).eq, mul_assoc]
  have hXP : P * R * P * P = P * R * P := by rw [mul_assoc, hPP]
  have hPX : P * (P * R * P) = P * R * P := by rw [← mul_assoc, ← mul_assoc, hPP]
  have hXQ : P * R * P * coherentAverage k a (fun θ => f θ + s) * (P * R * P) = P * R * P := by
    rw [hQs, hXdef]
    exact mul_resolvent_aux hPP hRP hBP hRB
  have hle := le_coherentAverage_inv k a (g := fun θ => f θ + s) (hf.add continuous_const)
    (fun θ => add_pos_of_pos_of_nonneg (hpos θ) hs) hXh hXQ hXP hPX
  have hinv : Continuous fun θ => (f θ + s)⁻¹ :=
    (hf.add continuous_const).inv₀ fun θ => (add_pos_of_pos_of_nonneg (hpos θ) hs).ne'
  have hL : coherentAverage k a (fun θ => logKernel s (f θ)) =
      (1 + s)⁻¹ • P - coherentAverage k a (fun θ => (f θ + s)⁻¹) := by
    rw [← coherentAverage_const, ← coherentAverage_sub k a continuous_const hinv]
    rfl
  rw [hL, cfc_logKernel hY hs, ← hRdef, mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc,
    hPP]
  exact sub_le_sub_left hle _

/-- A continuous function is bounded above and below on the coherent vectors `U e_a`, and the
lower bound is positive for a positive function. -/
theorem exists_bounds_coherentVec {f : (Ω → ℂ) → ℝ} (hf : Continuous f) (hpos : ∀ θ, 0 < f θ) :
    ∃ lo hi : ℝ, 0 < lo ∧ ∀ U : unitaryGroup Ω ℂ,
      lo ≤ f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ∧
        f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ≤ hi := by
  have hc := hf.comp (continuous_coherentVec a)
  obtain ⟨U₀, -, hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  obtain ⟨U₁, -, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  exact ⟨_, _, hpos _, fun U => ⟨hmin (Set.mem_univ U), hmax (Set.mem_univ U)⟩⟩

/-- **Exchange of the Haar and resolvent integrals**:
`𝒬_k(log f) = ∫_0^∞ 𝒬_k(k_s ∘ f) ds` for continuous `f > 0`. -/
theorem coherentAverage_log_eq_integral {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) :
    IntegrableOn (fun s => coherentAverage k a (fun θ => logKernel s (f θ))) (Ioi 0) ∧
      coherentAverage k a (fun θ => Real.log (f θ)) =
        ∫ s in Ioi 0, coherentAverage k a (fun θ => logKernel s (f θ)) := by
  set μ := unitaryHaar Ω
  set θ : unitaryGroup Ω ℂ → Ω → ℂ := fun U => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1 with hθdef
  have hcθ : Continuous θ := continuous_coherentVec a
  obtain ⟨lo, hi, hlo, hb⟩ := exists_bounds_coherentVec a hf hpos
  have hhi : 0 < hi := hlo.trans_le ((hb 1).1.trans (hb 1).2)
  have hPc : Continuous fun U => coherentProj k (θ U) := continuous_coherentProj k hcθ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hPc.continuousOn
  set F : unitaryGroup Ω ℂ → ℝ → Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
    fun U s => ((logKernel s (f (θ U)) : ℝ) : ℂ) • coherentProj k (θ U) with hFdef
  have hmeas : StronglyMeasurable (Function.uncurry F) := by
    have h1 : Measurable fun p : unitaryGroup Ω ℂ × ℝ => logKernel p.2 (f (θ p.1)) := by
      unfold logKernel
      exact ((measurable_const.add measurable_snd).inv).sub
        ((((hf.comp hcθ).measurable.comp measurable_fst).add measurable_snd).inv)
    exact (Complex.measurable_ofReal.comp h1).stronglyMeasurable.smul
      (hPc.stronglyMeasurable.comp_measurable measurable_fst)
  have hbd : Integrable (fun s => (|logKernel s lo| + |logKernel s hi|) * C)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((integrableOn_logKernel hlo).abs.add (integrableOn_logKernel hhi).abs).mul_const C
  have hint : Integrable (Function.uncurry F) (μ.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (hbd.comp_snd μ).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)]
      with p hp
    have hp' : (0 : ℝ) ≤ p.2 := le_of_lt hp
    simp only [Function.uncurry, hFdef]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (abs_logKernel_le hp' hlo (hb p.1).1 (hb p.1).2) (hC _ (Set.mem_univ _))
      (norm_nonneg _) (by positivity)
  refine ⟨(hint.integral_prod_right).smul (symDim Ω k : ℂ), ?_⟩
  change (symDim Ω k : ℂ) • ∫ U, ((Real.log (f (θ U)) : ℝ) : ℂ) • coherentProj k (θ U) ∂μ =
    ∫ s in Ioi 0, (symDim Ω k : ℂ) • ∫ U, F U s ∂μ
  rw [integral_smul, ← integral_integral_swap hint]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [hFdef]
  rw [integral_smul_const, integral_complex_ofReal, integral_logKernel ((hlo.trans_le (hb U).1))]

/-- The projector `Π` is positive semidefinite. -/
theorem posSemidef_symProj : (symProj (copyPerm Ω k)).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (symProj (copyPerm Ω k))
  rwa [(isHermitian_symProj k).eq, symProj_mul_self] at h

/-- The complementary projector `1 - Π` is positive semidefinite. -/
theorem posSemidef_one_sub_symProj : (1 - symProj (copyPerm Ω k)).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (1 - symProj (copyPerm Ω k))
  rwa [conjTranspose_sub, conjTranspose_one, (isHermitian_symProj k).eq, sub_mul, mul_sub,
    mul_sub, one_mul, mul_one, one_mul, symProj_mul_self, sub_self, sub_zero] at h

theorem mul_coherentAverage_add_smul_symProj {f : (Ω → ℂ) → ℝ} (hf : Continuous f) (c : ℝ) :
    (coherentAverage k a f + c • (1 - symProj (copyPerm Ω k))) * symProj (copyPerm Ω k) =
      coherentAverage k a f := by
  rw [add_mul, coherentAverage_mul_symProj k a hf, smul_mul_assoc, sub_mul, one_mul,
    symProj_mul_self, sub_self, smul_zero, add_zero]

theorem symProj_mul_coherentAverage_add_smul {f : (Ω → ℂ) → ℝ} (hf : Continuous f) (c : ℝ) :
    symProj (copyPerm Ω k) * (coherentAverage k a f + c • (1 - symProj (copyPerm Ω k))) =
      coherentAverage k a f := by
  rw [mul_add, symProj_mul_coherentAverage k a hf, mul_smul_comm, mul_sub, mul_one,
    symProj_mul_self, sub_self, smul_zero, add_zero]

/-- `𝒬_k(f) + c (1 - Π)` is positive definite for continuous `f > 0` and `c > 0`. -/
theorem posDef_coherentAverage_add_smul {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) {c : ℝ} (hc : 0 < c) :
    (coherentAverage k a f + c • (1 - symProj (copyPerm Ω k))).PosDef := by
  obtain ⟨lo, hi, hlo, hb⟩ := exists_bounds_coherentVec a hf hpos
  set P := symProj (copyPerm Ω k)
  set m := min lo c
  have hm : 0 < m := lt_min hlo hc
  have hQ : lo • P ≤ coherentAverage k a f := by
    rw [← coherentAverage_const]
    exact coherentAverage_mono k a continuous_const hf fun U => (hb U).1
  have hsum : (coherentAverage k a f + c • (1 - P) - m • 1).PosSemidef := by
    have e : coherentAverage k a f + c • (1 - P) - m • 1 =
        (coherentAverage k a f - lo • P) + (lo - m) • P + (c - m) • (1 - P) := by
      simp only [sub_smul, smul_sub]
      abel
    rw [e]
    exact ((Matrix.le_iff.mp hQ).add ((posSemidef_symProj k).smul
      (sub_nonneg.mpr (min_le_left _ _)))).add ((posSemidef_one_sub_symProj k).smul
      (sub_nonneg.mpr (min_le_right _ _)))
  have := (PosDef.one.smul hm).add_posSemidef hsum
  rwa [add_sub_cancel] at this

/-- **Operator Jensen inequality for the logarithm** with an arbitrary positive filler `c` on
the complement of `𝒮_k` (`06-transport.tex`, display `transport:log-jensen`). -/
theorem coherentAverage_log_le_of_pos {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) {c : ℝ} (hc : 0 < c) :
    coherentAverage k a (fun θ => Real.log (f θ)) ≤
      symProj (copyPerm Ω k) *
        CFC.log (coherentAverage k a f + c • (1 - symProj (copyPerm Ω k))) *
          symProj (copyPerm Ω k) := by
  set P := symProj (copyPerm Ω k)
  set Y := coherentAverage k a f + c • (1 - P)
  have hY : Y.PosDef := posDef_coherentAverage_add_smul k a hf hpos hc
  have hYP' : Y * P = coherentAverage k a f := mul_coherentAverage_add_smul_symProj k a hf c
  have hPY' : P * Y = coherentAverage k a f := symProj_mul_coherentAverage_add_smul k a hf c
  have hYP : Commute Y P := hYP'.trans hPY'.symm
  have hPYP : P * Y * P = coherentAverage k a f := by
    rw [hPY', coherentAverage_mul_symProj k a hf]
  obtain ⟨hintY, hlogY⟩ := integrableOn_cfc_logKernel hY
  obtain ⟨hintQ, hlogQ⟩ := coherentAverage_log_eq_integral k a hf hpos
  have hint1 := ((ContinuousLinearMap.mul ℂ _) P).integrable_comp hintY
  have hint2 := ((ContinuousLinearMap.mul ℂ _).flip P).integrable_comp hint1
  simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.flip_apply] at hint1 hint2
  rw [hlogY, mul_integral' P hintY, integral_mul' P hint1, hlogQ, ← sub_nonneg,
    ← integral_sub hint2 hintQ]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  change (0 : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) ≤ _
  exact sub_nonneg.mpr (coherentAverage_logKernel_le k a hf hpos hY hYP hPYP (le_of_lt hs))

end Jensen

/-- **Operator Jensen inequality for the logarithm** (`06-transport.tex`, display
`transport:log-jensen`, lines 526--546), compressed to `𝒮_k`: for continuous `f > 0`,
`Π 𝒬_k(log f) Π ≤ Π log(𝒬_k(f) + (1 - Π)) Π`. -/
theorem coherentAverage_log_le (k : ℕ) (a : Ω) {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) :
    coherentAverage k a (fun θ => Real.log (f θ)) ≤
      symProj (copyPerm Ω k) *
        CFC.log (coherentAverage k a f + (1 - symProj (copyPerm Ω k))) *
          symProj (copyPerm Ω k) := by
  simpa only [one_smul] using coherentAverage_log_le_of_pos k a hf hpos one_pos

/-- **Logarithmic passage** (`06-transport.tex` lines 520--575): a rank-one pin
`X ≥ e^{φ(θ)} P_{θ,k}` for all unit `θ`, with `X` positive definite and commuting with copy
permutations, gives `∫ φ dμ_ρ - log D_k ≤ Tr(ρ log X)` for every density matrix `ρ`
on `𝒮_k`. -/
theorem realCoherentIntegral_sub_log_le_re_trace_mul_log {k : ℕ} (a : Ω)
    {X : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hX : X.PosDef)
    (hXc : ∀ s, Commute (permOp (copyPerm Ω k) s) X) {φ : (Ω → ℂ) → ℝ} (hφ : Continuous φ)
    (hpin : ∀ θ : Ω → ℂ, star θ ⬝ᵥ θ = 1 → Real.exp (φ θ) • coherentProj k θ ≤ X)
    {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hsym : symProj (copyPerm Ω k) * ρ = ρ) :
    realCoherentIntegral k a ρ φ - Real.log (symDim Ω k) ≤ (ρ * CFC.log X).trace.re := by
  set P := symProj (copyPerm Ω k) with hPdef
  set D : ℕ := symDim Ω k
  have hD : (0 : ℝ) < D := by exact_mod_cast symDim_pos k a
  set μ := unitaryHaar Ω
  set θ : unitaryGroup Ω ℂ → Ω → ℂ := fun U => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1
  have hfe : Continuous fun θ => Real.exp (φ θ) := Real.continuous_exp.comp hφ
  set Q := coherentAverage k a (fun θ => Real.exp (φ θ))
  -- integrating the pin against Haar measure: `D⁻¹ 𝒬_k(e^φ) ≤ X`
  have hQX : (X - (D : ℝ)⁻¹ • Q).PosSemidef := by
    have hF := integrable_coherentIntegrand k a hfe
    have e1 : (D : ℝ)⁻¹ • Q = ∫ U, ((Real.exp (φ (θ U)) : ℝ) : ℂ) • coherentProj k (θ U) ∂μ := by
      simp only [Q, coherentAverage]
      rw [← Complex.coe_smul, smul_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
        inv_mul_cancel₀ (by exact_mod_cast hD.ne'), one_smul]
    rw [e1, ← Matrix.nonneg_iff_posSemidef]
    have e2 : X = ∫ _U, X ∂μ := by simp
    rw [e2, ← integral_sub (integrable_const X) hF]
    refine integral_nonneg fun U => ?_
    rw [Pi.zero_apply, sub_nonneg, Complex.coe_smul]
    exact hpin _ (star_coherentVec_dotProduct a U)
  -- a positive filler on the complement of `𝒮_k`
  have : Nonempty (Fin k → Ω) := ⟨fun _ => a⟩
  obtain ⟨ε, hε, hεX⟩ := (CFC.exists_pos_algebraMap_le_iff X hX.isHermitian.isSelfAdjoint).mpr
    fun x hx => hX.isStrictlyPositive.spectrum_pos hx
  rw [Algebra.algebraMap_eq_smul_one] at hεX
  have hc : 0 < (D : ℝ) * ε := mul_pos hD hε
  set Y := Q + ((D : ℝ) * ε) • (1 - P)
  have hY : Y.PosDef := posDef_coherentAverage_add_smul k a hfe (fun _ => Real.exp_pos _) hc
  have hPh : P.IsHermitian := isHermitian_symProj k
  have hPP : P * P = P := symProj_mul_self k
  have hXP : X * P = P * X := by
    simp only [hPdef, symProj, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => ((hXc σ).eq).symm
  have hQP : Q * P = Q := coherentAverage_mul_symProj k a hfe
  have hPQ : P * Q = Q := symProj_mul_coherentAverage k a hfe
  have hYX : (D : ℝ)⁻¹ • Y ≤ X := by
    rw [Matrix.le_iff]
    have e : X - (D : ℝ)⁻¹ • Y = Pᴴ * (X - (D : ℝ)⁻¹ • Q) * P +
        (1 - P)ᴴ * (X - ε • 1) * (1 - P) := by
      rw [conjTranspose_sub, conjTranspose_one, hPh.eq]
      simp only [Y, smul_add, smul_smul, inv_mul_cancel_left₀ hD.ne', mul_sub, sub_mul, one_mul,
        mul_one, smul_mul_assoc, mul_smul_comm, hPP, hQP, hPQ]
      rw [hXP, mul_assoc P X P, hXP, ← mul_assoc, hPP]
      module
    rw [e]
    exact (hQX.conjTranspose_mul_mul_same P).add
      ((Matrix.le_iff.mp hεX).conjTranspose_mul_mul_same (1 - P))
  -- operator monotonicity of the logarithm
  have hrY : ((D : ℝ)⁻¹ • Y).PosDef := hY.smul (inv_pos.mpr hD)
  have hlog : CFC.log ((D : ℝ)⁻¹ • Y) ≤ CFC.log X :=
    CFC.log_le_log hYX hrY.isStrictlyPositive
  rw [CFC.log_smul' Y (inv_pos.mpr hD) hY.isStrictlyPositive, Algebra.algebraMap_eq_smul_one,
    Real.log_inv] at hlog
  -- the Jensen step on `𝒮_k`
  have hJ := coherentAverage_log_le_of_pos k a hfe (fun _ => Real.exp_pos _) hc
  simp only [Real.log_exp] at hJ
  have hρP : ρ * P = ρ := by
    have h := congrArg conjTranspose hsym
    rwa [conjTranspose_mul, hρ.isHermitian.eq, hPh.eq] at h
  have hmono : ∀ {A B : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}, A ≤ B →
      (ρ * A).trace.re ≤ (ρ * B).trace.re := fun {A B} h => by
    have := (Complex.nonneg_iff.mp (hρ.trace_mul_nonneg (Matrix.le_iff.mp h))).1
    rwa [mul_sub, trace_sub, Complex.sub_re, sub_nonneg] at this
  have h1 := hmono hJ
  have h2 := hmono hlog
  rw [trace_mul_coherentAverage k a hφ] at h1
  have h3 : (ρ * (P * CFC.log Y * P)).trace = (ρ * CFC.log Y).trace := by
    rw [← mul_assoc, ← mul_assoc, hρP, trace_mul_comm, ← mul_assoc, hsym]
  rw [h3] at h1
  rw [mul_add, trace_add, Complex.add_re, mul_smul_comm, mul_one, trace_smul, htr] at h2
  simp only [Complex.real_smul, mul_one, Complex.ofReal_re] at h2
  linarith

/-- `D_k` is polynomial in `k`: `log D_k = O(log (k + 1))`. -/
theorem log_symDim_isBigO :
    (fun k : ℕ => Real.log (symDim Ω k)) =O[Filter.atTop] fun k : ℕ => Real.log (k + 1) := by
  refine Asymptotics.IsBigO.of_bound (Fintype.card Ω) (Filter.Eventually.of_forall fun k => ?_)
  have hk : (1 : ℝ) ≤ k + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg _),
    abs_of_nonneg (Real.log_nonneg hk)]
  rcases Nat.eq_zero_or_pos (symDim Ω k) with h | h
  · rw [h, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hk)
  · calc Real.log (symDim Ω k) ≤ Real.log (((k + 1) ^ Fintype.card Ω : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast symDim_le k)
      _ = Fintype.card Ω * Real.log (k + 1) := by push_cast; rw [Real.log_pow]

end TensorPower
