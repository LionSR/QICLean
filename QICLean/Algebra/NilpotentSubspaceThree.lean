/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.NilpotentSubspaceTwo
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Nilpotent subspaces of 3×3 complex matrices

A **nilpotent subspace** of `M₃(ℂ)` is a linear subspace all of whose elements
are nilpotent.  This file proves the three-dimensional classification: every
nilpotent subspace of `3 × 3` complex matrices either has a common kernel
vector or is, up to a simultaneous similarity, contained in the
two-dimensional *exceptional* space

```
N₃ = { (0 u 0; v 0 u; 0 -v 0) : u v : ℂ }.
```

Together with the trace-preserving and primitivity obstructions proved in
`QICLean.Channel.WielandtLowDim`, this is the `D = 3` case of the
classification used for the low-dimensional quantum Wielandt corollary
(Sanz–Pérez-García–Wolf–Cirac, arXiv:0909.5347, remark after Theorem 1;
Wolf, *Quantum Channels & Operations*, Chapter 6, corollary after
Theorem 6.9, `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`
lines 1111–1127), where the classification is cited without proof from
M. A. Fasoli, *Classification of nilpotent linear spaces in M(4; ℂ)*,
Communications in Algebra 25(6):1919–1932, 1997.

## Main results

* `common_ker_or_conjugate_windmill_of_isNilpotent_submodule_fin_three`:
  the classification of nilpotent subspaces of `M₃(ℂ)`.

## Proof outline

If every element of the subspace squares to zero, a direct
`AM + MA = 0` argument yields a common kernel vector.  Otherwise some
element `A` has `A² ≠ 0`, hence (being nilpotent of rank two) is cyclic;
conjugating `A` to the Jordan block `J₃`, the trace conditions
`tr((xJ₃ + M)²) = tr((xJ₃ + M)³) = 0` force every `M` of the subspace into
a one-parameter family, and a second explicit conjugation by
`s • 1 - p • J₃` (built from an element with nonzero `(1,0)` entry) either
lands the whole subspace inside `N₃` or exhibits the common kernel `e₁`.
-/

open scoped Matrix

namespace QICLean

variable {S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)}

/-- The nilpotent `3 × 3` Jordan block. -/
def jordanThree : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 1; 0, 0, 0]

/-- The exceptional nilpotent-space matrix pattern in dimension three. -/
def windmillMat (u v : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := !![0, u, 0; v, 0, u; 0, -v, 0]

/-- The Jordan block is the `v = 0` exceptional matrix. -/
theorem jordanThree_eq_windmillMat : jordanThree = windmillMat 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jordanThree, windmillMat]

/-- The trace of a positive power of a nilpotent complex matrix vanishes. -/
theorem IsNilpotent.trace_pow_eq_zero {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : IsNilpotent M) {k : ℕ} (hk : 0 < k) : (M ^ k).trace = 0 :=
  IsNilpotent.eq_zero
    (Matrix.isNilpotent_trace_of_isNilpotent (IsNilpotent.pow_of_pos hM (by omega)))

/-- A nilpotent `3 × 3` complex matrix cubes to zero. -/
theorem IsNilpotent.cube_eq_zero {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : IsNilpotent M) : M ^ 3 = 0 := by
  have hcp : M.charpoly = Polynomial.X ^ 3 := by
    have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM
    simp only [Fintype.card_fin] at h1
    exact sub_eq_zero.mp (IsNilpotent.eq_zero h1)
  have hCH := Matrix.aeval_self_charpoly M
  rw [hcp] at hCH
  simpa using hCH

/-- The trace of a cube of a sum, in noncommutative normal form. -/
theorem trace_cube_add (A M : Matrix (Fin 3) (Fin 3) ℂ) :
    ((A + M) ^ 3).trace =
      (A ^ 3).trace + 3 * (A ^ 2 * M).trace + 3 * (A * M ^ 2).trace + (M ^ 3).trace := by
  have hexp : (A + M) ^ 3 =
      A ^ 3 + (A ^ 2 * M + A * M * A + M * A ^ 2) +
        (A * M ^ 2 + M * A * M + M ^ 2 * A) + M ^ 3 := by
    noncomm_ring
  have c1 : (A * M * A).trace = (A ^ 2 * M).trace := by
    rw [Matrix.trace_mul_comm (A * M) A]
    congr 1
    noncomm_ring
  have c2 : (M * A ^ 2).trace = (A ^ 2 * M).trace := Matrix.trace_mul_comm _ _
  have c3 : (M * A * M).trace = (A * M ^ 2).trace := by
    rw [Matrix.trace_mul_comm (M * A) M, show M * (M * A) = M ^ 2 * A by noncomm_ring,
      Matrix.trace_mul_comm (M ^ 2) A]
  have c4 : (M ^ 2 * A).trace = (A * M ^ 2).trace := Matrix.trace_mul_comm _ _
  rw [hexp]
  simp only [Matrix.trace_add, c1, c2, c3, c4]
  ring

/-- If `A`, `M`, `A + M`, and `A - M` all have traceless cubes, the mixed
traces `tr(A²M)` and `tr(AM²)` vanish. -/
theorem trace_sq_mul_eq_zero_of_cube_add_sub
    {A M : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : (A ^ 3).trace = 0) (hM : (M ^ 3).trace = 0)
    (hp : ((A + M) ^ 3).trace = 0) (hm : ((A - M) ^ 3).trace = 0) :
    (A ^ 2 * M).trace = 0 ∧ (A * M ^ 2).trace = 0 := by
  have hp' := trace_cube_add A M
  have hm' := trace_cube_add A (-M)
  rw [← sub_eq_add_neg] at hm'
  rw [hp] at hp'
  rw [hm] at hm'
  have hM3 : ((-M) ^ 3).trace = -((M ^ 3).trace) := by
    rw [show (-M) ^ 3 = -(M ^ 3) by noncomm_ring, Matrix.trace_neg]
  have h2 : (A ^ 2 * (-M)).trace = -((A ^ 2 * M).trace) := by
    rw [show A ^ 2 * (-M) = -(A ^ 2 * M) by noncomm_ring, Matrix.trace_neg]
  have h3 : (A * (-M) ^ 2).trace = (A * M ^ 2).trace := by
    rw [show (-M) ^ 2 = M ^ 2 by noncomm_ring]
  rw [hM3, hM, h2, h3] at hm'
  simp only [neg_zero] at hm'
  rw [hA, hM] at hp'
  rw [hA] at hm'
  constructor
  · linear_combination (norm := ring1) (hm' - hp') / 6
  · linear_combination (norm := ring1) (hp' + hm') / -6

/-- The trace of `A * M` vanishes when `A`, `M`, and `A + M` have traceless
squares. -/
theorem trace_mul_eq_zero_of_sq_add
    {A M : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : (A ^ 2).trace = 0) (hM : (M ^ 2).trace = 0)
    (hp : ((A + M) ^ 2).trace = 0) :
    (A * M).trace = 0 := by
  have hexp : (A + M) ^ 2 = A ^ 2 + (A * M + M * A) + M ^ 2 := by noncomm_ring
  have c1 : (M * A).trace = (A * M).trace := Matrix.trace_mul_comm _ _
  rw [hexp] at hp
  simp only [Matrix.trace_add, c1] at hp
  linear_combination (norm := ring1) (hp - hA - hM) / 2


/-! ### Part 2: the square-zero case -/

/-- A square-zero `3 × 3` complex matrix has rank at most one. -/
theorem Matrix.rank_le_one_of_sq_eq_zero {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : M ^ 2 = 0) : Matrix.rank M ≤ 1 := by
  have hsub : LinearMap.range (Matrix.toLin' M) ≤ LinearMap.ker (Matrix.toLin' M) := by
    rintro y ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, ← pow_two, hM, Matrix.zero_mulVec]
  have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  have hle := Submodule.finrank_mono hsub
  have h3 : Module.finrank ℂ (Fin 3 → ℂ) = 3 := by
    simp [Module.finrank_fintype_fun_eq_card]
  rw [h3] at hrk
  have hrank : Matrix.rank M = Module.finrank ℂ (LinearMap.range (Matrix.toLin' M)) :=
    rfl
  omega

/-- A nonzero matrix of rank at most one has a one-dimensional range. -/
theorem exists_range_eq_span_singleton_of_rank_le_one {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : M ≠ 0) (hrank : Matrix.rank M ≤ 1) :
    ∃ u : Fin 3 → ℂ, u ≠ 0 ∧ LinearMap.range (Matrix.toLin' M) = ℂ ∙ u := by
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hM (Matrix.ext fun i j => h i j)
  have hu0 : M *ᵥ Pi.single j 1 ≠ 0 := by
    intro hzero
    have h_entry := congr_fun hzero i
    rw [Matrix.mulVec_single] at h_entry
    simp only [MulOpposite.op_one, one_smul] at h_entry
    rw [Matrix.col_apply] at h_entry
    exact hij h_entry
  refine ⟨M *ᵥ (Pi.single j 1), hu0, ?_⟩
  · have hmem : M *ᵥ (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' M) :=
      ⟨Pi.single j 1, by simp [Matrix.toLin'_apply]⟩
    have hle : ℂ ∙ (M *ᵥ Pi.single j 1) ≤ LinearMap.range (Matrix.toLin' M) :=
      (Submodule.span_singleton_le_iff_mem _ _).2 hmem
    have hfin1 : Module.finrank ℂ (ℂ ∙ (M *ᵥ Pi.single j 1) : Submodule ℂ _) = 1 :=
      finrank_span_singleton hu0
    have hfinr : Module.finrank ℂ (LinearMap.range (Matrix.toLin' M)) = 1 := by
      have hpos : 0 < Module.finrank ℂ (LinearMap.range (Matrix.toLin' M)) := by
        have hn : Nontrivial (LinearMap.range (Matrix.toLin' M)) :=
          ⟨⟨M *ᵥ Pi.single j 1, hmem⟩, ⟨0, Submodule.zero_mem _⟩,
            fun hcon => hu0 (Subtype.ext_iff.mp hcon)⟩
        exact Module.finrank_pos_iff.mpr hn
      have hle1 : Module.finrank ℂ (LinearMap.range (Matrix.toLin' M)) ≤ 1 := by
        have := hrank
        rwa [Matrix.rank] at this
      omega
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin1, hfinr])).symm

/-- A nilpotent matrix has no nonzero eigenvalues: if `M *ᵥ u = μ • u` with
`u ≠ 0` and `M` nilpotent, then `μ = 0`. -/
theorem IsNilpotent.eq_zero_of_mulVec_eq_smul {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : IsNilpotent M) {u : Fin 3 → ℂ} (hu : u ≠ 0) {μ : ℂ}
    (h : M *ᵥ u = μ • u) : μ = 0 := by
  obtain ⟨k, hk⟩ := hM
  have hiter : ∀ j : ℕ, (M ^ j) *ᵥ u = (μ ^ j) • u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, ← pow_succ]
  have h0 := hiter k
  rw [hk, Matrix.zero_mulVec] at h0
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact one_ne_zero hk
  have hμk : μ ^ k = 0 := (smul_eq_zero.mp h0.symm).resolve_right hu
  exact (pow_eq_zero_iff hk0).mp hμk

/-- Every vector is the sum of its standard-unit components. -/
theorem eq_sum_single (x : Fin 3 → ℂ) :
    x = ∑ j : Fin 3, x j • Pi.single j (1 : ℂ) := by
  ext i
  simp [Pi.single_apply]

/-- **Square-zero case**: a submodule of `3 × 3` complex matrices in which
every element squares to zero has a common kernel vector. -/
theorem exists_common_ker_of_forall_sq_eq_zero
    (S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ))
    (hS : ∀ M ∈ S, M ^ 2 = 0) :
    ∃ u : Fin 3 → ℂ, u ≠ 0 ∧ ∀ M ∈ S, M *ᵥ u = 0 := by
  rcases eq_or_ne S ⊥ with rfl | hbot
  · refine ⟨![1, 0, 0], ?_, fun M hM => ?_⟩
    · intro h
      have := congr_fun h 0
      simp at this
    · rw [Submodule.mem_bot] at hM
      subst hM
      simp
  obtain ⟨A, hAS, hA0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨u, hu, hrange⟩ :=
    exists_range_eq_span_singleton_of_rank_le_one hA0
      (Matrix.rank_le_one_of_sq_eq_zero (hS A hAS))
  -- Decompose `A` as `x ↦ ℓ x • u`.
  have hc : ∀ j : Fin 3, ∃ c : ℂ, A *ᵥ (Pi.single j 1) = c • u := by
    intro j
    have hmem : A *ᵥ (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' A) :=
      ⟨Pi.single j 1, by simp [Matrix.toLin'_apply]⟩
    rw [hrange] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  choose c hc using hc
  let ℓ : (Fin 3 → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => ∑ j : Fin 3, c j * x j
      map_add' := by
        intro x y
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring }
  have hentry : ∀ i j : Fin 3, A i j = c j * u i := by
    intro i j
    have h := congr_fun (hc j) i
    rw [Matrix.mulVec_single] at h
    simpa [Matrix.col_apply] using h
  have hA_eq : ∀ x : Fin 3 → ℂ, A *ᵥ x = ℓ x • u := by
    intro x
    ext i
    simp only [Matrix.mulVec, dotProduct, ℓ, Pi.smul_apply, smul_eq_mul]
    simp_rw [hentry]
    change (∑ j : Fin 3, c j * u i * x j) = (∑ j : Fin 3, c j * x j) * u i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- `ℓ` is nontrivial since `A ≠ 0`.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin 3 → ℂ, ℓ x₀ = 1 := by
    by_contra h
    push Not at h
    have hℓ0 : ∀ x, ℓ x = 0 := by
      intro x
      by_contra hx
      exact h ((ℓ x)⁻¹ • x) (by simp [map_smul, hx])
    refine hA0 ?_
    ext i j
    have h1 : A *ᵥ (Pi.single j 1) = ℓ (Pi.single j 1) • u := hA_eq _
    rw [hℓ0, zero_smul] at h1
    have := congr_fun h1 i
    rw [Matrix.mulVec_single] at this
    simpa [Matrix.col_apply] using this
  -- For every `M ∈ S`, `M *ᵥ u ∈ ℂ ∙ u`.
  have hMu : ∀ M ∈ S, ∃ μ : ℂ, M *ᵥ u = μ • u := by
    intro M hMS
    have hsq : (A + M) ^ 2 = A ^ 2 + A * M + M * A + M ^ 2 := by noncomm_ring
    rw [hS (A + M) (S.add_mem hAS hMS), hS A hAS, hS M hMS] at hsq
    have key : A * M + M * A = 0 := by
      have h' := hsq.symm
      simpa using h'
    have happ : (A * M + M * A) *ᵥ x₀ = 0 := by rw [key, Matrix.zero_mulVec]
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at happ
    rw [hA_eq, hA_eq, hx₀, one_smul] at happ
    -- happ : ℓ (M *ᵥ x₀) • u + M *ᵥ u = 0
    refine ⟨-ℓ (M *ᵥ x₀), ?_⟩
    exact (eq_neg_of_add_eq_zero_right happ).trans (neg_smul _ _).symm
  -- A nilpotent matrix has no nonzero eigenvalues, so `M *ᵥ u = 0`.
  refine ⟨u, hu, fun M hMS => ?_⟩
  obtain ⟨μ, hμ⟩ := hMu M hMS
  have hnil : IsNilpotent M := ⟨2, hS M hMS⟩
  rw [IsNilpotent.eq_zero_of_mulVec_eq_smul hnil hu hμ, zero_smul] at hμ
  exact hμ

end QICLean