/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.SpectralRadiusPowerDecay
import QICLean.Channel.Semigroup.Primitivity.Helpers
import QICLean.Channel.Semigroup.Primitivity.SpectralMapping
import QICLean.Channel.Irreducible.FromSpectral
import QICLean.Channel.Peripheral.IrreducibleChannel
import QICLean.Channel.Semigroup.Primitivity.Basic

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal TNOperatorSpace
open Matrix Finset NormedSpace

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-! ## Proposition 7.5: Irreducibility implies primitivity for QDS -/

theorem primitive_channel_pow_tendsto_zero_of_trace_zero [NeZero D]
    (E : Mat →ₗ[ℂ] Mat) (hE : IsChannel E) (hIrr : IsIrreducibleMap E)
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D) (hσ_fix : E σ = σ)
    (hPrim : IsPrimitive E) {X : Mat} (htrX : Matrix.trace X = 0) :
    Filter.Tendsto (fun n : ℕ => (E ^ n) X) Filter.atTop (nhds 0) := by
  have htrσ : Matrix.trace σ ≠ 0 := by
    simp [hσ_mem.2]
  let P : Mat →ₗ[ℂ] Mat := fixedPointProj (D := D) σ htrσ
  have hσ_ne : σ ≠ 0 := ne_zero_of_mem_densityMatrices' hσ_mem
  have hcompl_lt : ∀ ν : ℂ, Module.End.HasEigenvalue (E - P) ν → ‖ν‖ < 1 := by
    intro ν hν
    exact compl_eigenvalue_norm_lt_one_of_primitive_of_irreducible_channel
      E hE hIrr σ hσ_fix hσ_ne htrσ hPrim ν hν
  have hsr_lt : spectralRadius ℂ ((Module.End.toContinuousLinearMap Mat) (E - P)) < 1 :=
    spectralRadius_lt_one_of_eigenvalues_lt_one (E - P) hcompl_lt
  have hpow0 : Filter.Tendsto
      (fun n : ℕ => ((Module.End.toContinuousLinearMap Mat) (E - P)) ^ n)
      Filter.atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one _ hsr_lt
  have hNpow0 : Filter.Tendsto (fun n : ℕ => ((E - P) ^ n) X) Filter.atTop (nhds 0) := by
    have hEval : Continuous (fun A : Mat →L[ℂ] Mat => A X) :=
      (ContinuousLinearMap.apply ℂ Mat X).continuous
    have hEvalT : Filter.Tendsto
        (fun n : ℕ => (((Module.End.toContinuousLinearMap Mat) (E - P)) ^ n) X)
        Filter.atTop (nhds 0) :=
      (hEval.tendsto 0).comp hpow0
    refine hEvalT.congr' ?_
    filter_upwards [] with n
    rw [(map_pow (Module.End.toContinuousLinearMap Mat) (E - P) n).symm]
    rfl
  have hPX : P X = 0 := by
    simp [P, fixedPointProj, htrX]
  refine hNpow0.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn1 : 1 ≤ n := by
    omega
  have hpowEq :=
    pow_eq_fixedPointProj_add_compl_pow (D := D) (E := E) (ρ := σ) htrσ hE.tp hσ_fix hn1
  have hsumX : (P + (E - P) ^ n) X = ((E - P) ^ n) X := by
    simp [LinearMap.add_apply, hPX]
  calc
    ((E - P) ^ n) X = (P + (E - P) ^ n) X := by symm; exact hsumX
    _ = (E ^ n) X := by rw [← hpowEq]

theorem fixedPoint_eq_trace_smul_of_irreducible_channel
    [NeZero D]
    (E : Mat →ₗ[ℂ] Mat)
    (hE_ch : IsChannel E)
    (hE_irr : IsIrreducibleMap E)
    {σ : Mat}
    (hσ_mem : σ ∈ densityMatrices D)
    (hσ_fix : E σ = σ)
    {V : Mat}
    (hV_fix : E V = V)
    (hV_ne : V ≠ 0) :
    V = Matrix.trace V • σ := by
  have hV_tr_ne : Matrix.trace V ≠ 0 := by
    intro htr
    exact hV_ne (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
      hE_ch hE_irr V hV_fix htr)
  have hW_fix : E (V - (Matrix.trace V) • σ) = V - (Matrix.trace V) • σ := by
    rw [map_sub, map_smul, hV_fix, hσ_fix]
  have hW_tr : Matrix.trace (V - (Matrix.trace V) • σ) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, hσ_mem.2, smul_eq_mul, mul_one, sub_self]
  exact sub_eq_zero.mp
    (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
      hE_ch hE_irr _ hW_fix hW_tr)

theorem trace_ne_zero_of_nonzero_fixedPoint_of_irreducible_channel
    [NeZero D]
    (E : Mat →ₗ[ℂ] Mat)
    (hE_ch : IsChannel E)
    (hE_irr : IsIrreducibleMap E)
    {V : Mat}
    (hV_fix : E V = V)
    (hV_ne : V ≠ 0) :
    Matrix.trace V ≠ 0 := by
  intro htr
  exact hV_ne (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
    hE_ch hE_irr V hV_fix htr)

/-- A peripheral eigenvalue of an irreducible QDS has a periodic fixed point:
there exists `p > 0` and a nonzero eigenvector `V` such that `T(p * t) V = V`. -/
theorem exists_power_fixed_eigenvector_of_peripheral
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s))
    {t : ℝ} (ht : 0 < t)
    {μ : ℂ} (hμ_eig : Module.End.HasEigenvalue (T t) μ) (hμ_norm : ‖μ‖ = 1) :
    ∃ p : ℕ, 0 < p ∧ ∃ V : Mat, V ≠ 0 ∧ (T t) V = μ • V ∧ T (↑p * t) V = V := by
  have hTt_ch : IsChannel (T t) := hT.channel t (le_of_lt ht)
  have hTt_irr : IsIrreducibleMap (T t) := hT_irr_all t ht
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  obtain ⟨σ, _, hσ_pd, hσ_fix, _⟩ :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible (E := T t) hTt_ch hTt_irr hD
  have hμ_periph : μ ∈ peripheralEigenvalues (T t) := ⟨hμ_eig, hμ_norm⟩
  have hpow_closed := peripheral_powers_closed_of_irreducible_channel_with_fixed
    (T t) hTt_ch hTt_irr σ hσ_pd hσ_fix hμ_periph
  obtain ⟨p, hp_pos, _, hμp⟩ :=
    bounded_root_of_peripheral_closed_powers (T t) μ hμ_periph hpow_closed
  obtain ⟨V, hV⟩ := hμ_eig.exists_hasEigenvector
  have hV_ne : V ≠ 0 := hV.2
  have hEV : (T t) V = μ • V := Module.End.mem_eigenspace_iff.mp hV.1
  have hpt_eq : T (↑p * t) = (T t) ^ p :=
    semigroup_pow T hT.semigroup.semigroup t (le_of_lt ht) p
  refine ⟨p, hp_pos, V, hV_ne, hEV, ?_⟩
  rw [hpt_eq, hV.pow_apply p, hμp, one_smul]

/-- A trace-nonzero eigenvector exists for peripheral eigenvalues of an irreducible QDS. -/
theorem exists_trace_ne_zero_eigenvector_of_peripheral
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s))
    {t : ℝ} (ht : 0 < t)
    {μ : ℂ} (hμ_eig : Module.End.HasEigenvalue (T t) μ) (hμ_norm : ‖μ‖ = 1) :
    ∃ V : Mat, V ≠ 0 ∧ (T t) V = μ • V ∧ Matrix.trace V ≠ 0 := by
  obtain ⟨p, hp_pos, V, hV_ne, hEV, hVfix⟩ :=
    exists_power_fixed_eigenvector_of_peripheral T hT hT_irr_all ht hμ_eig hμ_norm
  have hpt_pos : 0 < (↑p : ℝ) * t := mul_pos (Nat.cast_pos.mpr hp_pos) ht
  exact ⟨V, hV_ne, hEV,
    trace_ne_zero_of_nonzero_fixedPoint_of_irreducible_channel
      (T (↑p * t)) (hT.channel _ (le_of_lt hpt_pos)) (hT_irr_all _ hpt_pos) hVfix hV_ne⟩

theorem eigenvalue_eq_one_of_trace_preserving_eigenvector
    (E : Mat →ₗ[ℂ] Mat)
    (hE_tp : IsTracePreservingMap E)
    {μ : ℂ} {V : Mat}
    (hEV : E V = μ • V)
    (htrV_ne : Matrix.trace V ≠ 0) :
    μ = 1 := by
  have htrV : μ * Matrix.trace V = Matrix.trace V := by
    simpa [hEV, Matrix.trace_smul, smul_eq_mul] using hE_tp V
  have hzero : (μ - 1) * Matrix.trace V = 0 := by
    calc
      (μ - 1) * Matrix.trace V = μ * Matrix.trace V - Matrix.trace V := by ring
      _ = 0 := by rw [htrV, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right htrV_ne)

/-- All peripheral eigenvalues equal 1 when the QDS is irreducible at all positive times. -/
theorem peripheral_eq_one_of_irreducible_all
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s))
    {t : ℝ} (ht : 0 < t)
    {μ : ℂ} (hμ_eig : Module.End.HasEigenvalue (T t) μ) (hμ_norm : ‖μ‖ = 1) :
    μ = 1 := by
  obtain ⟨V, _, hEV, htrV⟩ :=
    exists_trace_ne_zero_eigenvector_of_peripheral T hT hT_irr_all ht hμ_eig hμ_norm
  exact eigenvalue_eq_one_of_trace_preserving_eigenvector
    (T t) (hT.channel t (le_of_lt ht)).tp hEV htrV

/-- Irreducibility at all positive times implies primitivity for a QDS. -/
theorem primitive_of_irreducible_all
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s)) :
    ∀ t : ℝ, 0 < t → IsPrimitive (T t) := by
  intro t ht
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hTt_ch : IsChannel (T t) := hT.channel t (le_of_lt ht)
  have hTt_irr : IsIrreducibleMap (T t) := hT_irr_all t ht
  obtain ⟨σ, hσ_mem, _, hσ_fix, _⟩ :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible (E := T t) hTt_ch hTt_irr hD
  have hσ_ne := ne_zero_of_mem_densityMatrices' hσ_mem
  exact isPrimitive_of_unique_norm_one (T t) σ hσ_fix hσ_ne
    (fun μ hμ_eig hμ_norm =>
      peripheral_eq_one_of_irreducible_all T hT hT_irr_all ht hμ_eig hμ_norm)

theorem fixedPoint_at_nat_mul
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T)
    (s : ℝ) (hs : 0 < s)
    {δ : Mat}
    (hδ_fix : T s δ = δ) :
    ∀ k : ℕ, T ((k : ℝ) * s) δ = δ := by
  intro k
  have hpow_fix : ∀ j : ℕ, ((T s) ^ j) δ = δ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ']
        simpa [ih] using hδ_fix
  rw [semigroup_pow T hT.semigroup.semigroup s (le_of_lt hs) k]
  exact hpow_fix k

theorem fixed_density_fixed_for_all_times_of_irreducible_time
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D)
    (hσ_fix : T t₀ σ = σ)
    (hσ_unique : ∀ τ ∈ densityMatrices D, T t₀ τ = τ → τ = σ) :
    ∀ u : ℝ, 0 ≤ u → T u σ = σ := by
  intro u hu
  exact hσ_unique (T u σ)
    (IsChannel.map_densityMatrices _ (hT.channel u hu) σ hσ_mem)
    (by
      have h1 := hT.semigroup.semigroup.comp t₀ u (le_of_lt ht₀) hu
      have h2 := hT.semigroup.semigroup.comp u t₀ hu (le_of_lt ht₀)
      change T t₀ (T u σ) = T u σ
      have heval1 : (T t₀).comp (T u) σ = T (t₀ + u) σ := by
        rw [h1]
      have heval2 : (T u).comp (T t₀) σ = T (u + t₀) σ := by
        rw [h2]
      simp only [LinearMap.comp_apply] at heval1 heval2
      rw [heval1, add_comm, ← heval2, hσ_fix])

theorem fixedPoint_eq_trace_smul_at_irreducible_time
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (t₀ : ℝ)
    (hTt₀_ch : IsChannel (T t₀))
    (hirr : IsIrreducibleMap (T t₀))
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D) (hσ_fix : T t₀ σ = σ) :
    ∀ X : Mat, T t₀ X = X → X = Matrix.trace X • σ := by
  intro X hX
  exact eq_of_sub_eq_zero
    (fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel hTt₀_ch hirr _
      (by rw [map_sub, map_smul, hX, hσ_fix])
      (by rw [Matrix.trace_sub, Matrix.trace_smul, hσ_mem.2, smul_eq_mul,
               mul_one, sub_self]))

theorem trace_zero_fixedPoint_tendsto_zero_of_primitive_slice
    [NeZero D]
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D)
    (u : ℝ) (hu_nonneg : 0 ≤ u)
    (hTu_ch : IsChannel (T u))
    (hTu_irr : IsIrreducibleMap (T u))
    (hTu_fix : T u σ = σ)
    (hTu_prim : IsPrimitive (T u))
    {δ : Mat}
    (hδ_tr : Matrix.trace δ = 0) :
    Filter.Tendsto (fun n : ℕ => T ((n : ℝ) * u) δ) Filter.atTop (nhds 0) := by
  have hpow_decay :=
    primitive_channel_pow_tendsto_zero_of_trace_zero
      (E := T u) hTu_ch hTu_irr σ hσ_mem hTu_fix hTu_prim hδ_tr
  refine hpow_decay.congr' ?_
  filter_upwards [] with n
  rw [← semigroup_pow T hT.semigroup.semigroup u hu_nonneg n]

theorem irreducible_all_of_irreducible_time
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hirr : IsIrreducibleMap (T t₀)) :
    ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s) := by
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hTt₀_ch : IsChannel (T t₀) := hT.channel t₀ (le_of_lt ht₀)
  obtain ⟨σ, hσ_mem, hσ_pd, hσ_fix, hσ_unique⟩ :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible (E := T t₀) hTt₀_ch hirr hD
  have hσ_fix_all : ∀ u : ℝ, 0 ≤ u → T u σ = σ :=
    fixed_density_fixed_for_all_times_of_irreducible_time
      T hT t₀ ht₀ σ hσ_mem hσ_fix hσ_unique
  have hfixed_1d : ∀ X : Matrix (Fin D) (Fin D) ℂ, T t₀ X = X →
      X = Matrix.trace X • σ :=
    fixedPoint_eq_trace_smul_at_irreducible_time T t₀ hTt₀_ch hirr σ hσ_mem hσ_fix
  have hkernel_1d : ∀ X : Mat, L X = 0 → X = Matrix.trace X • σ := by
    intro X hLX
    exact hfixed_1d X
      ((generator_apply_eq_zero_iff_fixed_nonneg L T hexp X).1 hLX t₀ (le_of_lt ht₀))
  obtain ⟨δ, hδ_pos, hfixed_small⟩ :=
    exists_pos_forall_lt_expSemigroup_fixedPoint_iff_generator_apply_eq_zero L
  have hfixed_small_T : ∀ u : ℝ, 0 < u → u < δ →
      ∀ X : Mat, T u X = X ↔ L X = 0 := by
    intro u hu huδ X
    rw [hexp u (le_of_lt hu)]
    exact hfixed_small u hu huδ X
  have hirr_small : ∀ u : ℝ, 0 < u → u < δ → IsIrreducibleMap (T u) := by
    intro u hu huδ
    apply isIrreducibleMap_of_channel_posDef_fixedPoint_unique
      (T u) (hT.channel u (le_of_lt hu)) σ hσ_pd
      (hσ_fix_all u (le_of_lt hu))
    intro τ _hτ_psd hτ_fix
    exact ⟨Matrix.trace τ, hkernel_1d τ ((hfixed_small_T u hu huδ τ).1 hτ_fix)⟩
  let u : ℝ := δ / (2 * Real.pi)
  have htwo_pi_pos : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  have hu_pos : 0 < u := by dsimp [u]; exact div_pos hδ_pos htwo_pi_pos
  have hu_lt : u < δ := by
    dsimp [u]
    rw [div_lt_iff₀ htwo_pi_pos]
    nlinarith [Real.two_le_pi]
  have hpi_u_eq : Real.pi * u = δ / 2 := by
    dsimp [u]
    field_simp [Real.pi_ne_zero]
  have hpi_u_pos : 0 < Real.pi * u := by rw [hpi_u_eq]; positivity
  have hpi_u_lt : Real.pi * u < δ := by rw [hpi_u_eq]; linarith
  have hTu_irr : IsIrreducibleMap (T u) := hirr_small u hu_pos hu_lt
  have hTpi_irr : IsIrreducibleMap (T (Real.pi * u)) :=
    hirr_small (Real.pi * u) hpi_u_pos hpi_u_lt
  have hno_nonzero_imaginary_eigenvalue :
      ∀ μ : ℂ, Module.End.HasEigenvalue L μ → μ.re = 0 → μ = 0 := by
    intro μ hμ_eig hμ_re
    obtain ⟨X, hX_eig⟩ := hμ_eig.exists_hasEigenvector
    have hLX : L X = μ • X := Module.End.mem_eigenspace_iff.mp hX_eig.1
    have hμ_form : μ = (μ.im : ℂ) * Complex.I := by
      apply Complex.ext
      · simp [hμ_re]
      · simp
    have hnorm_u : ‖Complex.exp ((u : ℂ) * μ)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, hμ_re]
    have hnorm_pi :
        ‖Complex.exp (((Real.pi * u : ℝ) : ℂ) * μ)‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, hμ_re]
    have heig_u : Module.End.HasEigenvalue (T u) (Complex.exp ((u : ℂ) * μ)) := by
      rw [hexp u (le_of_lt hu_pos)]
      exact hasEigenvalue_of_eigenvector_eq _ _ X
        (expSemigroup_apply_eigenvector L X μ hLX u) hX_eig.2
    have heig_pi : Module.End.HasEigenvalue (T (Real.pi * u))
        (Complex.exp (((Real.pi * u : ℝ) : ℂ) * μ)) := by
      rw [hexp (Real.pi * u) (le_of_lt hpi_u_pos)]
      exact hasEigenvalue_of_eigenvector_eq _ _ X
        (expSemigroup_apply_eigenvector L X μ hLX (Real.pi * u)) hX_eig.2
    obtain ⟨p₁, hp₁_pos, hp₁_root⟩ :=
      peripheral_isRootOfUnity_of_irreducible_channel
        (T u) (hT.channel u (le_of_lt hu_pos)) hTu_irr
        (Complex.exp ((u : ℂ) * μ)) ⟨heig_u, hnorm_u⟩
    obtain ⟨p₂, hp₂_pos, hp₂_root⟩ :=
      peripheral_isRootOfUnity_of_irreducible_channel
        (T (Real.pi * u))
        (hT.channel (Real.pi * u) (le_of_lt hpi_u_pos)) hTpi_irr
        (Complex.exp (((Real.pi * u : ℝ) : ℂ) * μ))
        ⟨heig_pi, hnorm_pi⟩
    have hphase_u : (u : ℂ) * μ = ↑(u * μ.im) * Complex.I := by
      calc
        (u : ℂ) * μ = (u : ℂ) * ((μ.im : ℂ) * Complex.I) :=
          congrArg ((u : ℂ) * ·) hμ_form
        _ = ↑(u * μ.im) * Complex.I := by push_cast; ring
    have hphase_pi :
        ((Real.pi * u : ℝ) : ℂ) * μ =
          ↑(Real.pi * (u * μ.im)) * Complex.I := by
      calc
        ((Real.pi * u : ℝ) : ℂ) * μ =
            ((Real.pi * u : ℝ) : ℂ) * ((μ.im : ℂ) * Complex.I) :=
          congrArg (((Real.pi * u : ℝ) : ℂ) * ·) hμ_form
        _ = ↑(Real.pi * (u * μ.im)) * Complex.I := by push_cast; ring
    have hroot_one : ∃ p : ℕ, 0 < p ∧
        Complex.exp (↑(u * μ.im) * Complex.I) ^ p = 1 := by
      refine ⟨p₁, hp₁_pos, ?_⟩
      rw [← hphase_u]
      exact hp₁_root
    have hroot_pi : ∃ p : ℕ, 0 < p ∧
        Complex.exp (↑(Real.pi * (u * μ.im)) * Complex.I) ^ p = 1 := by
      refine ⟨p₂, hp₂_pos, ?_⟩
      rw [← hphase_pi]
      exact hp₂_root
    have hphase_zero : u * μ.im = 0 :=
      eq_zero_of_exp_mul_I_isRootOfUnity_one_pi
        (u * μ.im) hroot_one hroot_pi
    have hμ_im : μ.im = 0 := (mul_eq_zero.mp hphase_zero).resolve_left hu_pos.ne'
    exact Complex.ext hμ_re hμ_im
  intro s hs
  apply isIrreducibleMap_of_channel_posDef_fixedPoint_unique (T s)
    (hT.channel s (le_of_lt hs)) σ hσ_pd (hσ_fix_all s (le_of_lt hs))
  intro τ _hτ_psd hτ_fix
  refine ⟨Matrix.trace τ, ?_⟩
  apply hkernel_1d
  by_contra hLτ_ne
  obtain ⟨μ, hμ_ne, hμ_eig, hμ_root⟩ :=
    exists_nonzero_generator_eigenvalue_of_expSemigroup_fixed_not_generator_fixed
      L s hs.ne' (by rw [← hexp s (le_of_lt hs)]; exact hτ_fix) hLτ_ne
  have hμ_norm : ‖Complex.exp ((s : ℂ) * μ)‖ = 1 := by
    rw [hμ_root, norm_one]
  have hμ_re : μ.re = 0 :=
    re_eq_zero_of_peripheral_generator μ s hs hμ_norm
  exact hμ_ne (hno_nonzero_imaginary_eigenvalue μ hμ_eig hμ_re)

end -- noncomputable section
