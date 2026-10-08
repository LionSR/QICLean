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
    (ρ * coherentAverage k a f).trace.re = coherentIntegral k a ρ f := by
  have hF := integrable_coherentIntegrand k a hf
  let L : Matrix (Fin k → Ω) (Fin k → Ω) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap _ ℂ ℂ) ∘ₗ LinearMap.mulLeft ℂ ρ)
  have hL : ∀ M, L M = (ρ * M).trace := fun M => rfl
  have hint : Integrable (fun U : unitaryGroup Ω ℂ => L ((f ((U : Matrix Ω Ω ℂ) *ᵥ
      Pi.single a 1) : ℂ) • coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)))
      (unitaryHaar Ω) := L.integrable_comp hF
  rw [coherentIntegral, coherentAverage, mul_smul_comm, trace_smul, ← hL,
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
theorem coherentIntegral_one {k : ℕ} (a : Ω) {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}
    (htr : ρ.trace = 1) (hsym : symProj (copyPerm Ω k) * ρ = ρ) :
    coherentIntegral k a ρ (fun _ => 1) = 1 := by
  rw [← trace_mul_coherentAverage k a continuous_const, coherentAverage_one, trace_mul_comm, hsym,
    htr, Complex.one_re]

/-- The coherent integrand of a continuous function is Haar integrable. -/
theorem integrable_coherentIntegral_integrand (k : ℕ) (a : Ω)
    (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) {g : (Ω → ℂ) → ℝ} (hg : Continuous g) :
    Integrable (fun U : unitaryGroup Ω ℂ => g ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) *
      (ρ * coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)).trace.re) (unitaryHaar Ω) :=
  ((hg.comp (continuous_coherentVec a)).mul (Complex.continuous_re.comp
    ((continuous_const.mul (continuous_coherentProj k (continuous_coherentVec a))).matrix_trace))
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The coherent integral against a state on `𝒮_k` is affine in the integrand. -/
theorem coherentIntegral_affine {k : ℕ} (a : Ω) {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}
    (htr : ρ.trace = 1) (hsym : symProj (copyPerm Ω k) * ρ = ρ) {F : (Ω → ℂ) → ℝ}
    (hF : Continuous F) (α β : ℝ) :
    coherentIntegral k a ρ (fun θ => α + β * F θ) = α + β * coherentIntegral k a ρ F := by
  have h1 := coherentIntegral_one a htr hsym
  unfold coherentIntegral at h1 ⊢
  beta_reduce at h1 ⊢
  set w : unitaryGroup Ω ℂ → ℝ := fun U =>
    (ρ * coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)).trace.re with hw
  have hI : ∫ U, (α + β * F ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)) * w U ∂(unitaryHaar Ω) =
      α * ∫ U, 1 * w U ∂(unitaryHaar Ω) +
        β * ∫ U, F ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) * w U ∂(unitaryHaar Ω) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      ((integrable_coherentIntegral_integrand k a ρ continuous_const).const_mul α)
      ((integrable_coherentIntegral_integrand k a ρ hF).const_mul β)]
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
  · refine integrableOn_Ioi_deriv_of_nonpos ?_ (fun s hs => hd s (Ioi_subset_Ici_self hs)) (fun s hs => ?_)
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

/-- **Operator Jensen inequality for the logarithm** (`06-transport.tex`, display
`transport:log-jensen`, lines 526--546), compressed to `𝒮_k`: for continuous `f > 0`,
`Π 𝒬_k(log f) Π ≤ Π log(𝒬_k(f) + (1 - Π)) Π`. -/
theorem coherentAverage_log_le (k : ℕ) (a : Ω) {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) :
    coherentAverage k a (fun θ => Real.log (f θ)) ≤
      symProj (copyPerm Ω k) *
        CFC.log (coherentAverage k a f + (1 - symProj (copyPerm Ω k))) *
          symProj (copyPerm Ω k) := by
  sorry

/-- **Logarithmic passage** (`06-transport.tex` lines 520--575): a rank-one pin
`X ≥ e^{φ(θ)} P_{θ,k}` for all unit `θ`, with `X` positive definite and commuting with copy
permutations, gives `∫ φ dμ_ρ - log D_k ≤ Tr(ρ log X)` for every density matrix `ρ`
on `𝒮_k`. -/
theorem coherentIntegral_sub_log_le_re_trace_mul_log {k : ℕ} (a : Ω)
    {X : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hX : X.PosDef)
    (hXc : ∀ s, Commute (permOp (copyPerm Ω k) s) X) {φ : (Ω → ℂ) → ℝ} (hφ : Continuous φ)
    (hpin : ∀ θ : Ω → ℂ, star θ ⬝ᵥ θ = 1 → Real.exp (φ θ) • coherentProj k θ ≤ X)
    {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hsym : symProj (copyPerm Ω k) * ρ = ρ) :
    coherentIntegral k a ρ φ - Real.log (symDim Ω k) ≤ (ρ * CFC.log X).trace.re := by
  sorry

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
