/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Semigroup.Primitivity.MainTheorem
import QICLean.Channel.Semigroup.RelaxationConditions

/-!
# Wolf Corollary 7.2 — Necessary conditions for relaxation

This file packages the three algebraic criteria of Wolf, Corollary 7.2, with
the faithful stationary state and global relaxation conclusion obtained from
Propositions 7.5 and 7.6.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder TNOperatorSpace
open Matrix Finset Module

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- For a GKSL generator, non-reducibility is equivalent to irreducibility of
one positive-time channel. The forward implication chooses the non-resonant
time at which the fixed-point space of `expSemigroup L` is `ker L`, as in
Wolf, Propositions 7.5 and 7.6. -/
theorem not_isReducibleQDS_iff_exists_irreducible_time
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L) :
    (¬ IsReducibleQDS L) ↔
      ∃ t₀ : ℝ, 0 < t₀ ∧ IsIrreducibleMap (expSemigroup L t₀) := by
  constructor
  · intro hNotReducible
    obtain ⟨t₀, ht₀, hfixed⟩ :=
      exists_pos_expSemigroup_fixedPoint_iff_generator_apply_eq_zero L
    refine ⟨t₀, ht₀, ?_⟩
    intro P hP hP_pres
    by_cases hP_zero : P = 0
    · exact Or.inl hP_zero
    by_cases hP_one : P = 1
    · exact Or.inr hP_one
    exfalso
    obtain ⟨ρ, hρ_density, hρ_corner, hρ_fixed⟩ :=
      IsChannel.exists_fixed_density_of_preserves_compression
        (E := expSemigroup L t₀) (hGKSL t₀ ht₀.le) hP hP_zero hP_pres
    have hKernel : HasRankDeficientKernelElement L :=
      ⟨ρ, hρ_density, ⟨P, ⟨hP, hP_zero, hP_one⟩, hρ_corner⟩,
        (hfixed ρ).1 hρ_fixed⟩
    have hInvariant : HasInvariantCompression L :=
      (wolf_prop_7_6_full_equivalence hGKSL).2.1.mp hKernel
    exact hNotReducible hInvariant
  · rintro ⟨t₀, ht₀, hirreducible⟩ hReducible
    obtain ⟨P, hP, hP_pres⟩ := hReducible
    rcases hirreducible P hP.1 (hP_pres t₀ ht₀.le) with hP_zero | hP_one
    · exact hP.2.1 hP_zero
    · exact hP.2.2 hP_one

/-- A non-reducible GKSL semigroup relaxes to a faithful stationary density
matrix, which also spans the kernel of its generator. This is the direct
combination of Wolf, Propositions 7.6 and 7.5. -/
theorem relaxation_and_simple_kernel_of_not_isReducibleQDS
    [NeZero D]
    (L : Mat →ₗ[ℂ] Mat)
    (hGKSL : IsGKSLGenerator L)
    (hNotReducible : ¬ IsReducibleQDS L) :
    ∃ ρInf : Mat,
      RelaxesTo (expSemigroup L) ρInf ∧ HasSimpleKernel L ρInf := by
  obtain ⟨t₀, ht₀, hirreducible⟩ :=
    (not_isReducibleQDS_iff_exists_irreducible_time hGKSL).1 hNotReducible
  apply relaxation_and_simple_kernel_of_irreducible_time
    L (expSemigroup L)
  · exact ⟨expSemigroup_isContinuousDynSemigroup L, hGKSL⟩
  · intro _ _
    rfl
  · exact ht₀
  · exact hirreducible

/-- Wolf, Corollary 7.2(1): if the Lindblad operators together with `κ`
generate the full matrix algebra, the semigroup relaxes to a faithful
stationary density matrix. -/
theorem relaxation_and_simple_kernel_of_generates_full_algebra
    [NeZero D]
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ
      (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) = ⊤) :
    ∃ ρInf : Mat,
      RelaxesTo (expSemigroup F.toLinearMap) ρInf ∧
        HasSimpleKernel F.toLinearMap ρInf := by
  have hGKSL : IsGKSLGenerator F.toLinearMap :=
    (gksl_iff_lindbladForm F.toLinearMap).2 ⟨F, rfl⟩
  exact relaxation_and_simple_kernel_of_not_isReducibleQDS
    F.toLinearMap hGKSL
      (not_isReducible_of_generates_full_algebra F hGKSL hGen)

/-- Wolf, Corollary 7.2(2): if the Lindblad span is Hermitian and has scalar
commutant, the semigroup relaxes to a faithful stationary density matrix. -/
theorem relaxation_and_simple_kernel_of_hermitian_span_trivial_commutant
    [NeZero D]
    (F : LindbladForm D)
    (hHerm : IsLindbladSpanHermitianClosed F)
    (hComm : HasLindbladSpanTrivialCommutant F) :
    ∃ ρInf : Mat,
      RelaxesTo (expSemigroup F.toLinearMap) ρInf ∧
        HasSimpleKernel F.toLinearMap ρInf := by
  have hGKSL : IsGKSLGenerator F.toLinearMap :=
    (gksl_iff_lindbladForm F.toLinearMap).2 ⟨F, rfl⟩
  exact relaxation_and_simple_kernel_of_not_isReducibleQDS
    F.toLinearMap hGKSL
      (not_isReducible_of_hermitian_span_trivial_commutant
        F hGKSL hHerm hComm)

/-- Wolf, Corollary 7.2(3): under the literal source inequality
`D ^ 2 - D < rank(C)`, the semigroup relaxes to a faithful stationary density
matrix. -/
theorem TracelessBasisKossakowskiForm.relaxation_and_simple_kernel_of_rank_gt
    [NeZero D]
    (K : TracelessBasisKossakowskiForm D)
    (hRank : D ^ 2 - D < K.C.rank) :
    ∃ ρInf : Mat,
      RelaxesTo (expSemigroup K.toLinearMap) ρInf ∧
        HasSimpleKernel K.toLinearMap ρInf := by
  have hGKSL : IsGKSLGenerator K.toLinearMap :=
    (gksl_iff_tracelessBasisKossakowskiForm K.toLinearMap).2 ⟨K, rfl⟩
  exact relaxation_and_simple_kernel_of_not_isReducibleQDS
    K.toLinearMap hGKSL (K.not_isReducible_of_rank_gt hRank)

/-- **Wolf Corollary 7.2 (complete relaxation conclusion).** Let `L` be
represented in Lindblad form, or in the fixed-traceless-basis Kossakowski
form. Each of Wolf's three stated alternatives produces one faithful
stationary density matrix to which every density matrix converges. The same
density matrix spans `ker L`.

This is `Notes/WolfNoteTexSource/ch07_semigroup_structure.tex`, lines 313--325.
-/
theorem wolf_corollary_7_2
    [NeZero D]
    {L : Mat →ₗ[ℂ] Mat}
    (hCondition :
      (∃ F : LindbladForm D,
        F.toLinearMap = L ∧
          Algebra.adjoin ℂ
            (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) = ⊤) ∨
      (∃ F : LindbladForm D,
        F.toLinearMap = L ∧ IsLindbladSpanHermitianClosed F ∧
          HasLindbladSpanTrivialCommutant F) ∨
      ∃ K : TracelessBasisKossakowskiForm D,
        K.toLinearMap = L ∧ D ^ 2 - D < K.C.rank) :
    ∃ ρInf : Mat,
      RelaxesTo (expSemigroup L) ρInf ∧ HasSimpleKernel L ρInf := by
  rcases hCondition with hGen | hHerm | hRank
  · obtain ⟨F, hFL, hGen⟩ := hGen
    simpa only [hFL] using
      (relaxation_and_simple_kernel_of_generates_full_algebra F hGen)
  · obtain ⟨F, hFL, hHerm, hComm⟩ := hHerm
    simpa only [hFL] using
      (relaxation_and_simple_kernel_of_hermitian_span_trivial_commutant
        F hHerm hComm)
  · obtain ⟨K, hKL, hRank⟩ := hRank
    simpa only [hKL] using
      (K.relaxation_and_simple_kernel_of_rank_gt hRank)

end -- noncomputable section
