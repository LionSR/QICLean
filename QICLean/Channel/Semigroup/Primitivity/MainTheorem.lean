/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Semigroup.Primitivity.IrreducibleAnalysis
import QICLean.Channel.Semigroup.Primitivity.Basic

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal TNOperatorSpace
open Matrix Finset NormedSpace

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **Wolf Proposition 7.5** (1 → 3): If `T_{t₀}` is irreducible for some
`t₀ > 0`, then `T_t` is primitive for all `t > 0`.

The proof has two parts:

**Part 1 — Irreducibility propagation** (`hT_irr_all`):
`T_{t₀}` irreducible → `T_s` irreducible for ALL `s > 0`.
Uses the kernel characterization: `ker(L) = Span{σ}` where `σ` is the unique
faithful density fixed point of `T_{t₀}`. Then `σ` is fixed by all `T_s`
(semigroup commutativity + density uniqueness). For each `s > 0`, `T_s`
is shown irreducible via `isIrreducibleMap_of_channel_posDef_fixedPoint_unique`.

**Part 2 — Roots of unity → primitivity**:
Given irreducibility at all times, peripheral eigenvalues are roots of unity
(Wolf Theorem 6.6). If `μ` is a peripheral eigenvalue of `T_t` with `μ^p = 1`,
the eigenvector `V` is a fixed point of `T_{pt}`. By irreducibility of
`T_{pt}`, `V` must be proportional to the unique faithful density fixed
point `σ'`, giving `T_t σ' = μ σ'`. Trace preservation then forces `μ = 1`.

The Lean proof combines the propagation theorem
`irreducible_all_of_irreducible_time` with the primitive-slice analysis in
`IrreducibleAnalysis.lean`: `primitive_of_irreducible_all` reduces primitivity
to irreducibility at all positive times, while `exists_primitive_fraction_slice`
and `fixedPoint_eq_trace_smul_of_primitive_slice` supply the fixed-point input
for the propagation theorem. -/
theorem irreducible_semigroup_implies_primitive
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hirr : IsIrreducibleMap (T t₀)) :
    ∀ t : ℝ, 0 < t → IsPrimitive (T t) ∧ IsIrreducibleMap (T t) := by
  have hT_irr_all : ∀ s : ℝ, 0 < s → IsIrreducibleMap (T s) :=
    irreducible_all_of_irreducible_time L T hT hexp t₀ ht₀ hirr
  intro t ht
  exact ⟨
    primitive_of_irreducible_all T hT hT_irr_all t ht,
    hT_irr_all t ht
  ⟩

/-- **Wolf Proposition 7.5, items (1)--(3).** For a QDS of channels, the
following three conditions are equivalent:
1. There exists `t₀ > 0` such that `T_{t₀}` is irreducible.
2. `T_t` is irreducible for all `t > 0`.
3. `T_t` is primitive for all `t > 0`.
`(∃ t₀ > 0, IsIrreducibleMap (T t₀)) ↔ (∀ t > 0, IsPrimitive (T t) ∧ IsIrreducibleMap (T t))`.

The RHS includes `IsIrreducibleMap` alongside `IsPrimitive` because the definition
`IsPrimitive E := peripheralEigenvalues E = {1}` states only the *set* of peripheral
eigenvalues, which alone does not imply irreducibility (e.g. the identity map on
`M₂(ℂ)` is primitive but not irreducible). For quantum dynamical semigroups,
irreducibility at one time propagates to all times, making the conjunction equivalent
to item 2, and `IsPrimitive` then follows as a consequence. -/
theorem qds_irreducible_iff_primitive
    [NeZero D]
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (T : ℝ → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t) :
    (∃ t₀ : ℝ, 0 < t₀ ∧ IsIrreducibleMap (T t₀)) ↔
    (∀ t : ℝ, 0 < t → IsPrimitive (T t) ∧ IsIrreducibleMap (T t)) := by
  constructor
  · -- Forward: ∃ t₀, irreducible T_{t₀} → ∀ t, primitive ∧ irreducible T_t
    rintro ⟨t₀, ht₀, hirr⟩
    exact irreducible_semigroup_implies_primitive L T hT hexp t₀ ht₀ hirr
  · -- Backward: ∀ t > 0, primitive ∧ irreducible T_t → ∃ t₀ > 0, irreducible T_{t₀}
    intro h
    exact ⟨1, one_pos, (h 1 one_pos).2⟩

private theorem exists_semigroup_norm_bound_on_unit_interval
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖endEquiv (T s)‖ ≤ C := by
  have hbdd : BddAbove ((fun s : ℝ => ‖endEquiv (T s)‖) '' Set.Icc 0 1) :=
    isCompact_Icc.bddAbove_image
      (continuous_norm.comp hT.semigroup.continuous).continuousOn
  obtain ⟨B, hB⟩ := hbdd
  refine ⟨max B 0 + 1, by linarith [le_max_right B 0], ?_⟩
  intro s hs
  exact (hB ⟨s, hs, rfl⟩).trans (by linarith [le_max_left B 0])

private theorem det_eq_zero_of_mem_proper_compression
    {P ρ : Mat}
    (hP : IsOrthogonalProjection P) (hP_ne_one : P ≠ 1)
    (hρ : P * ρ * P = ρ) :
    Matrix.det ρ = 0 := by
  have hdetP : Matrix.det P = 0 := by
    by_contra hdetP
    have hPunit : IsUnit P :=
      (Matrix.isUnit_iff_isUnit_det P).2 ((isUnit_iff_ne_zero).2 hdetP)
    exact hP_ne_one ((IsIdempotentElem.iff_eq_one_of_isUnit hPunit).1 hP.2)
  have hdet := congrArg Matrix.det hρ
  simpa [Matrix.det_mul, hdetP] using hdet.symm

/-- Discrete decay for a primitive unit-time channel extends to the full
continuous semigroup. The proof writes
`t = ⌊t⌋₊ + (t - ⌊t⌋₊)` and bounds the residual factor uniformly on `[0, 1]`. -/
theorem trace_zero_tendsto_zero_of_primitive_unit_slice
    [NeZero D]
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T)
    (σ : Mat) (hσ_mem : σ ∈ densityMatrices D)
    (hσ_fix : T 1 σ = σ)
    (hT1_irr : IsIrreducibleMap (T 1))
    (hT1_prim : IsPrimitive (T 1))
    {δ : Mat} (hδ_tr : Matrix.trace δ = 0) :
    Filter.Tendsto (fun t : ℝ => T t δ) Filter.atTop (nhds 0) := by
  have hdisc : Filter.Tendsto (fun n : ℕ => T (n : ℝ) δ)
      Filter.atTop (nhds 0) := by
    simpa using trace_zero_fixedPoint_tendsto_zero_of_primitive_slice
      T hT σ hσ_mem 1 zero_le_one (hT.channel 1 zero_le_one)
        hT1_irr hσ_fix hT1_prim hδ_tr
  obtain ⟨C, _hC_pos, hC⟩ := exists_semigroup_norm_bound_on_unit_interval T hT
  have hfloor_disc : Filter.Tendsto
      (fun t : ℝ => T ((⌊t⌋₊ : ℕ) : ℝ) δ) Filter.atTop (nhds 0) :=
    hdisc.comp tendsto_nat_floor_atTop
  have hbound_tendsto : Filter.Tendsto
      (fun t : ℝ => C * ‖T ((⌊t⌋₊ : ℕ) : ℝ) δ‖) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hfloor_disc.norm
  apply squeeze_zero_norm'
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    let n : ℕ := ⌊t⌋₊
    let r : ℝ := t - (n : ℝ)
    have hr_nonneg : 0 ≤ r := by
      simpa [r, n] using Nat.zero_le_self_sub_floor ht
    have hr_le_one : r ≤ 1 := by
      simpa [r, n] using (Nat.self_sub_floor_lt_one t).le
    have ht_decomp : t = r + (n : ℝ) := by
      dsimp [r]
      ring
    calc
      ‖T t δ‖ = ‖T r (T (n : ℝ) δ)‖ := by
        rw [ht_decomp, hT.semigroup.semigroup.comp r (n : ℝ)
          hr_nonneg (Nat.cast_nonneg n)]
        rfl
      _ ≤ ‖endEquiv (T r)‖ * ‖T (n : ℝ) δ‖ := by
        exact ContinuousLinearMap.le_opNorm (endEquiv (T r)) (T (n : ℝ) δ)
      _ ≤ C * ‖T (n : ℝ) δ‖ :=
        mul_le_mul_of_nonneg_right (hC r ⟨hr_nonneg, hr_le_one⟩) (norm_nonneg _)
  · exact hbound_tendsto

/-- **Wolf Proposition 7.5, (1) → (4),(5).** An irreducible positive-time
slice determines a faithful density matrix `σ`; every density matrix relaxes to
`σ`, and `σ` spans the kernel of the generator. -/
theorem relaxation_and_simple_kernel_of_irreducible_time
    [NeZero D]
    (L : Mat →ₗ[ℂ] Mat)
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hirr : IsIrreducibleMap (T t₀)) :
    ∃ σ : Mat, RelaxesTo T σ ∧ HasSimpleKernel L σ := by
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hTt₀_ch : IsChannel (T t₀) := hT.channel t₀ (le_of_lt ht₀)
  obtain ⟨σ, hσ_mem, hσ_pd, hσ_fix, hσ_unique⟩ :=
    IsChannel.exists_unique_density_fixedPoint_of_irreducible
      (E := T t₀) hTt₀_ch hirr hD
  have hσ_fix_all : ∀ t : ℝ, 0 ≤ t → T t σ = σ :=
    fixed_density_fixed_for_all_times_of_irreducible_time
      T hT t₀ ht₀ σ hσ_mem hσ_fix hσ_unique
  have hT1 := irreducible_semigroup_implies_primitive
    L T hT hexp t₀ ht₀ hirr 1 one_pos
  have hrelax : RelaxesTo T σ := by
    refine ⟨hσ_mem, hσ_pd, ?_⟩
    intro ρ hρ_mem
    have htrace : Matrix.trace (ρ - σ) = 0 := by
      rw [Matrix.trace_sub, hρ_mem.2, hσ_mem.2, sub_self]
    have hzero := trace_zero_tendsto_zero_of_primitive_unit_slice
      T hT σ hσ_mem (hσ_fix_all 1 zero_le_one) hT1.2 hT1.1 htrace
    have hadd : Filter.Tendsto (fun t : ℝ => T t (ρ - σ) + σ)
        Filter.atTop (nhds σ) := by
      simpa using hzero.add tendsto_const_nhds
    refine hadd.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [map_sub, hσ_fix_all t ht, sub_add_cancel]
  have hkernel : L σ = 0 :=
    (generator_apply_eq_zero_iff_fixed_nonneg L T hexp σ).2 hσ_fix_all
  have hunique : ∀ X : Mat, L X = 0 → ∃ c : ℂ, X = c • σ := by
    intro X hLX
    refine ⟨Matrix.trace X, ?_⟩
    exact fixedPoint_eq_trace_smul_at_irreducible_time
      T t₀ hTt₀_ch hirr σ hσ_mem hσ_fix X
        ((generator_apply_eq_zero_iff_fixed_nonneg L T hexp X).1 hLX
          t₀ (le_of_lt ht₀))
  have hsimple : HasSimpleKernel L σ := ⟨hkernel, hσ_pd, hunique⟩
  exact ⟨σ, hrelax, hsimple⟩

/-- **Wolf Proposition 7.5, (4) → (1).** If a quantum dynamical semigroup
relaxes to a faithful density matrix, then its unit-time channel is
irreducible. -/
theorem irreducible_unit_of_relaxesTo
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T)
    {σ : Mat} (hrelax : RelaxesTo T σ) :
    IsIrreducibleMap (T 1) := by
  by_contra hirr
  rw [IsIrreducibleMap] at hirr
  push Not at hirr
  obtain ⟨P, hP, hpres, hP_ne_zero, hP_ne_one⟩ := hirr
  obtain ⟨τ, hτ_mem, hτ_compression, hτ_fix⟩ :=
    IsChannel.exists_fixed_density_of_preserves_compression
      (E := T 1) (hT.channel 1 zero_le_one) hP hP_ne_zero hpres
  have hτ_fix_nat : ∀ n : ℕ, T (n : ℝ) τ = τ := by
    intro n
    simpa using fixedPoint_at_nat_mul T hT 1 one_pos hτ_fix n
  have hsubseq : Filter.Tendsto (fun n : ℕ => T (n : ℝ) τ)
      Filter.atTop (nhds σ) :=
    (hrelax.2.2 τ hτ_mem).comp tendsto_natCast_atTop_atTop
  have hconstant : Filter.Tendsto (fun n : ℕ => T (n : ℝ) τ)
      Filter.atTop (nhds τ) :=
    tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => (hτ_fix_nat n).symm)
  have hστ : σ = τ := tendsto_nhds_unique hsubseq hconstant
  have hσ_compression : P * σ * P = σ := by
    rw [hστ]
    exact hτ_compression
  have hdet_zero :=
    det_eq_zero_of_mem_proper_compression hP hP_ne_one hσ_compression
  have hdet_ne : Matrix.det σ ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det σ).1 hrelax.2.1.isUnit).ne_zero
  exact hdet_ne hdet_zero

/-- **Wolf Proposition 7.5, (5) → (1).** If the generator kernel is
spanned by a faithful density matrix, then some positive-time channel is
irreducible.

Choose `t₀ > 0` so that the fixed-point space of `exp(t₀L)` equals `ker L`.
The unique fixed direction is then generated by the faithful matrix `σ`, so
Wolf's fixed-point characterization of irreducibility applies. -/
theorem exists_irreducible_time_of_simple_kernel
    [NeZero D]
    (L : Mat →ₗ[ℂ] Mat)
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t)
    {σ : Mat} (_hσ_mem : σ ∈ densityMatrices D)
    (hsimple : HasSimpleKernel L σ) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ IsIrreducibleMap (T t₀) := by
  obtain ⟨t₀, ht₀, hfix⟩ :=
    exists_pos_expSemigroup_fixedPoint_iff_generator_apply_eq_zero L
  have hσ_fix_exp : expSemigroup L t₀ σ = σ := (hfix σ).2 hsimple.kernel
  have hσ_fix : T t₀ σ = σ := by
    rw [hexp t₀ ht₀.le]
    exact hσ_fix_exp
  refine ⟨t₀, ht₀, isIrreducibleMap_of_channel_posDef_fixedPoint_unique
    (T t₀) (hT.channel t₀ ht₀.le) σ hsimple.posDef hσ_fix ?_⟩
  intro X _hX_psd hX_fix
  apply hsimple.unique X
  apply (hfix X).1
  rw [← hexp t₀ ht₀.le]
  exact hX_fix

/-- **Wolf Proposition 7.5 (full equivalence).** For a norm-continuous quantum
dynamical semigroup `T_t = exp(tL)`, the five conditions printed in Wolf are
equivalent:

1. some `T_{t₀}`, `t₀ > 0`, is irreducible;
2. every `T_t`, `t > 0`, is irreducible;
3. every `T_t`, `t > 0`, is primitive;
4. all density matrices converge to one faithful density matrix;
5. `ker L` is spanned by a faithful density matrix.

The third Lean predicate is paired with `IsIrreducibleMap`. In this library,
`IsPrimitive E` records only that the set of peripheral eigenvalues is `{1}`
and does not record algebraic multiplicity; the conjunction is the project
predicate corresponding to Wolf's use of “primitive”.

Source: `Notes/WolfNoteTexSource/ch07_semigroup_structure.tex`, lines 268--283. -/
theorem wolf_prop_7_5_full_equivalence
    [NeZero D]
    (L : Mat →ₗ[ℂ] Mat)
    (T : ℝ → Mat →ₗ[ℂ] Mat)
    (hT : IsQuantumDynSemigroup T)
    (hexp : ∀ t : ℝ, 0 ≤ t → T t = expSemigroup L t) :
    ((∃ t₀ : ℝ, 0 < t₀ ∧ IsIrreducibleMap (T t₀)) ↔
      (∀ t : ℝ, 0 < t → IsIrreducibleMap (T t))) ∧
    ((∀ t : ℝ, 0 < t → IsIrreducibleMap (T t)) ↔
      (∀ t : ℝ, 0 < t → IsPrimitive (T t) ∧ IsIrreducibleMap (T t))) ∧
    ((∀ t : ℝ, 0 < t → IsPrimitive (T t) ∧ IsIrreducibleMap (T t)) ↔
      IsRelaxingQDS T) ∧
    (IsRelaxingQDS T ↔ HasSimpleFaithfulKernel L) := by
  constructor
  · constructor
    · rintro ⟨t₀, ht₀, hirr⟩
      exact irreducible_all_of_irreducible_time L T hT hexp t₀ ht₀ hirr
    · intro hall
      exact ⟨1, one_pos, hall 1 one_pos⟩
  constructor
  · constructor
    · intro hall t ht
      exact ⟨primitive_of_irreducible_all T hT hall t ht, hall t ht⟩
    · intro hall t ht
      exact (hall t ht).2
  constructor
  · constructor
    · intro hall
      obtain ⟨σ, hrelax, _⟩ := relaxation_and_simple_kernel_of_irreducible_time
        L T hT hexp one_pos (hall 1 one_pos).2
      exact ⟨σ, hrelax⟩
    · rintro ⟨σ, hrelax⟩
      exact irreducible_semigroup_implies_primitive
        L T hT hexp 1 one_pos (irreducible_unit_of_relaxesTo T hT hrelax)
  · constructor
    · rintro ⟨σ, hrelax⟩
      obtain ⟨τ, hτ_relax, hτ_simple⟩ :=
        relaxation_and_simple_kernel_of_irreducible_time
          L T hT hexp one_pos (irreducible_unit_of_relaxesTo T hT hrelax)
      exact ⟨τ, hτ_relax.1, hτ_simple⟩
    · rintro ⟨σ, hσ_mem, hσ_simple⟩
      obtain ⟨t₀, ht₀, hirr⟩ :=
        exists_irreducible_time_of_simple_kernel L T hT hexp hσ_mem hσ_simple
      obtain ⟨τ, hτ_relax, _⟩ :=
        relaxation_and_simple_kernel_of_irreducible_time L T hT hexp ht₀ hirr
      exact ⟨τ, hτ_relax⟩


end -- noncomputable section
