/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import QICLean.Algebra.MatrixIsometryEntries
import QICLean.Algebra.TracePurity
import QICLean.Analysis.TraceNormContractionCoefficient
import QICLean.Channel.FixedPoint.DirectSumExtension

/-!
# Convex-extreme density states in matrix algebras and finite direct sums

Wolf calls a density operator **pure** when it has no nontrivial convex
decomposition.  In a full finite-dimensional matrix algebra these are exactly
the rank-one orthogonal projections.  In a finite direct sum of full matrix
algebras, the relative pure states have exactly one nonzero block, and that
block is a rank-one orthogonal projection.

The direct-sum state space below uses the dependent matrix-family coordinates
already used by `Matrix.directSumDiagonalEmbedding` and the direct-sum map APIs.
It therefore does not introduce a parallel block decomposition.

## Main declarations

* `pureDensityMatrices`: rank-one orthogonal projections, viewed as density states.
* `extremePoints_densityMatrices`: Wolf's pure-state characterization.
* `directSumDensityMatrices`: positive matrix families of total trace one.
* `pureDirectSumDensityMatrices`: one rank-one block and zero elsewhere.
* `extremePoints_directSumDensityMatrices`: the relative pure-state characterization.

## References

* M. M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 1,
  `Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 102--108.
* M. M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6,
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1641--1652.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators Convex

noncomputable section

namespace Matrix

variable {D : ℕ}

/-- The pure density states in a full matrix algebra: rank-one orthogonal
projections.  The convex-extreme characterization is
`extremePoints_densityMatrices` below. -/
def pureDensityMatrices (D : ℕ) : Set (Matrix (Fin D) (Fin D) ℂ) :=
  {P | IsRankOneOrthogonalProjection P}

@[simp]
theorem mem_pureDensityMatrices {P : Matrix (Fin D) (Fin D) ℂ} :
    P ∈ pureDensityMatrices D ↔ IsRankOneOrthogonalProjection P :=
  Iff.rfl

/-- A rank-one orthogonal projection is a density matrix. -/
theorem IsRankOneOrthogonalProjection.mem_densityMatrices
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : IsRankOneOrthogonalProjection P) :
    P ∈ densityMatrices D := by
  refine ⟨isOrthogonalProjection_posSemidef hP.1, ?_⟩
  have hrankTrace := hP.1.1.rank_eq_trace_re_of_idem hP.1.2
  rw [hP.2] at hrankTrace
  have htrRe : P.trace.re = 1 := by exact_mod_cast hrankTrace.symm
  have htrIm : P.trace.im = 0 :=
    (Complex.nonneg_iff.mp (isOrthogonalProjection_posSemidef hP.1).trace_nonneg).2.symm
  exact Complex.ext htrRe htrIm

/-- A unit-vector projector is a rank-one orthogonal projection. -/
theorem IsUnitVector.isRankOneOrthogonalProjection_pureStateProj
    {psi : Fin D → ℂ} (hpsi : IsUnitVector psi) :
    IsRankOneOrthogonalProjection (pureStateProj psi) := by
  have hmem := pureStateProj_mem_densityMatrices hpsi
  have hidem : pureStateProj psi * pureStateProj psi = pureStateProj psi := by
    change Matrix.vecMulVec psi (fun p => star (psi p)) *
      Matrix.vecMulVec psi (fun p => star (psi p)) =
        Matrix.vecMulVec psi (fun p => star (psi p))
    rw [Matrix.vecMulVec_mul_vecMulVec, hpsi, one_smul]
  refine ⟨⟨hmem.1.isHermitian, hidem⟩, ?_⟩
  have hrankTrace := hmem.1.isHermitian.rank_eq_trace_re_of_idem hidem
  rw [hmem.2] at hrankTrace
  exact_mod_cast hrankTrace

/-- Every rank-one orthogonal projection is the projector onto a unit vector. -/
theorem IsRankOneOrthogonalProjection.exists_isUnitVector_pureStateProj
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : IsRankOneOrthogonalProjection P) :
    ∃ psi : Fin D → ℂ, IsUnitVector psi ∧ pureStateProj psi = P := by
  classical
  obtain ⟨n, V, hVstarV, hVVstar⟩ := hP.1.exists_range_isometry
  have htraceP : P.trace = 1 :=
    (IsRankOneOrthogonalProjection.mem_densityMatrices hP).2
  have hnC : (n : ℂ) = 1 := by
    calc
      (n : ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ).trace := by simp
      _ = (Vᴴ * V).trace := congrArg Matrix.trace hVstarV |>.symm
      _ = (V * Vᴴ).trace := Matrix.trace_mul_comm _ _
      _ = P.trace := congrArg Matrix.trace hVVstar
      _ = 1 := htraceP
  have hn : n = 1 := by exact_mod_cast hnC
  subst n
  let psi : Fin D → ℂ := fun i ↦ V i 0
  refine ⟨psi, ?_, ?_⟩
  · change (∑ p : Fin D, star (V p 0) * V p 0) = 1
    simpa using Matrix.sum_star_mul_eq_ite_of_conjTranspose_mul_eq_one
      V hVstarV (0 : Fin 1) (0 : Fin 1)
  · calc
      pureStateProj psi = V * Vᴴ := by
        ext i j
        simp [pureStateProj, Matrix.vecMulVec_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, psi]
      _ = P := hVVstar

/-- Pure density states are convex-extreme among all density matrices. -/
theorem IsRankOneOrthogonalProjection.mem_extremePoints_densityMatrices
    {P : Matrix (Fin D) (Fin D) ℂ} (hP : IsRankOneOrthogonalProjection P) :
    P ∈ Set.extremePoints ℝ (densityMatrices D) := by
  refine mem_extremePoints_iff_left.mpr
    ⟨IsRankOneOrthogonalProjection.mem_densityMatrices hP, ?_⟩
  intro A hA B hB hsegment
  rcases hsegment with ⟨a, b, ha, hb, hab, hcombo⟩
  obtain ⟨psi, hpsi, hpsiP⟩ :=
    IsRankOneOrthogonalProjection.exists_isUnitVector_pureStateProj hP
  have hcomboC : (a : ℂ) • A + (b : ℂ) • B = P := by
    simpa only [Complex.coe_smul] using hcombo
  have haC : (0 : ℂ) ≤ a := by exact_mod_cast ha.le
  have hbC : (0 : ℂ) ≤ b := by exact_mod_cast hb.le
  have hscaledA : ((a : ℂ) • A).PosSemidef := hA.1.smul haC
  have hscaledB : ((b : ℂ) • B).PosSemidef := hB.1.smul hbC
  have hdom : (a : ℂ) • A ≤ pureStateProj psi := by
    rw [Matrix.le_iff]
    have heq : pureStateProj psi - (a : ℂ) • A = (b : ℂ) • B := by
      rw [hpsiP, ← hcomboC]
      abel
    rw [heq]
    exact hscaledB
  have hdom' : (a : ℂ) • A ≤
      (1 : ℂ) • Matrix.vecMulVec psi (fun p ↦ star (psi p)) := by
    simpa [pureStateProj] using hdom
  obtain ⟨c, hc, hcEq⟩ :=
    hscaledA.eq_nonneg_smul_vecMulVec_of_le_smul_vecMulVec psi hdom'
  have htraceEq := congrArg Matrix.trace hcEq
  have hstar : star psi = fun p ↦ star (psi p) := by
    ext p
    rfl
  have hvecTrace : (Matrix.vecMulVec psi (star psi)).trace = 1 := by
    rw [Matrix.trace_vecMulVec, hstar, dotProduct_comm]
    exact hpsi
  have hvecP : Matrix.vecMulVec psi (star psi) = P := by
    rw [hstar]
    simpa only [pureStateProj] using hpsiP
  have hac : (a : ℂ) = c := by
    rw [Matrix.trace_smul, hA.2, Matrix.trace_smul, hvecTrace] at htraceEq
    simpa using htraceEq
  have hscaledEq : (a : ℂ) • A = (a : ℂ) • P := by
    calc
      (a : ℂ) • A = c • Matrix.vecMulVec psi (star psi) := hcEq
      _ = (a : ℂ) • P := by rw [← hac, hvecP]
  exact smul_right_injective _ (by exact_mod_cast ha.ne') hscaledEq

/-- Every density matrix is a convex combination of rank-one orthogonal
projections, exactly as in Wolf's spectral-decomposition argument. -/
theorem densityMatrices_eq_convexHull_pureDensityMatrices :
    densityMatrices D = convexHull ℝ (pureDensityMatrices D) := by
  apply Set.Subset.antisymm
  · intro A hA
    let w : Fin D → ℝ := hA.1.isHermitian.eigenvalues
    let z : Fin D → Matrix (Fin D) (Fin D) ℂ := fun i ↦
      pureStateProj (fun p ↦ hA.1.isHermitian.eigenvectorUnitary p i)
    apply mem_convexHull_of_exists_fintype w z
    · intro i
      exact hA.1.eigenvalues_nonneg i
    · exact hA.1.sum_eigenvalues_eq_one hA.2
    · intro i
      exact IsUnitVector.isRankOneOrthogonalProjection_pureStateProj
        (eigenvectorUnitary_isUnitVector hA.1.isHermitian i)
    · have hdecomp := hA.1.eq_sum_eigenvalue_smul_eigenprojector
      simpa only [w, z, pureStateProj, Complex.coe_smul] using hdecomp.symm
  · exact convexHull_min
      (fun _ hP ↦ IsRankOneOrthogonalProjection.mem_densityMatrices hP)
      densityMatrices_isConvex

/-- Wolf's pure-state characterization: the convex-extreme density matrices
are exactly the rank-one orthogonal projections. -/
theorem extremePoints_densityMatrices :
    Set.extremePoints ℝ (densityMatrices D) = pureDensityMatrices D := by
  apply Set.Subset.antisymm
  · rw [densityMatrices_eq_convexHull_pureDensityMatrices]
    exact extremePoints_convexHull_subset
  · intro P hP
    exact IsRankOneOrthogonalProjection.mem_extremePoints_densityMatrices hP

/-- Membership form of Wolf's pure-state characterization. -/
@[simp]
theorem mem_extremePoints_densityMatrices_iff
    {P : Matrix (Fin D) (Fin D) ℂ} :
    P ∈ Set.extremePoints ℝ (densityMatrices D) ↔
      IsRankOneOrthogonalProjection P := by
  rw [extremePoints_densityMatrices]
  rfl

section DirectSum

variable {iota : Type*} [Fintype iota] [DecidableEq iota]
variable (d : iota → ℕ)

/-- Density states of the finite direct sum `⊕ k, M_(d k)`: every block is
positive semidefinite and the sum of the block traces is one. -/
def directSumDensityMatrices :
    Set (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :=
  {A | (∀ k, (A k).PosSemidef) ∧ ∑ k, (A k).trace = 1}

omit [DecidableEq iota] in
@[simp]
theorem mem_directSumDensityMatrices
    {A : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ} :
    A ∈ directSumDensityMatrices d ↔
      (∀ k, (A k).PosSemidef) ∧ ∑ k, (A k).trace = 1 :=
  Iff.rfl

omit [DecidableEq iota] in
/-- The total-trace-one positive cone of a finite direct sum is convex. -/
theorem directSumDensityMatrices_isConvex :
    Convex ℝ (directSumDensityMatrices d) := by
  intro A hA B hB a b ha hb hab
  have haC : (0 : ℂ) ≤ a := by exact_mod_cast ha
  have hbC : (0 : ℂ) ≤ b := by exact_mod_cast hb
  constructor
  · intro k
    have hpos := (hA.1 k).smul haC |>.add ((hB.1 k).smul hbC)
    simpa only [Pi.add_apply, Pi.smul_apply, Complex.coe_smul] using hpos
  · simp_rw [Pi.add_apply, Pi.smul_apply, Matrix.trace_add, Matrix.trace_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hA.2, hB.2]
    simpa only [Complex.real_smul, mul_one, Complex.ofReal_add, Complex.ofReal_one] using
      congrArg (fun r : ℝ ↦ (r : ℂ)) hab

/-- The relative pure states of a finite direct sum: one rank-one projection
in one block and zero in every other block. -/
def pureDirectSumDensityMatrices :
    Set (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :=
  {A | ∃ k P, IsRankOneOrthogonalProjection P ∧ A = Pi.single k P}

omit [Fintype iota] in
@[simp]
theorem mem_pureDirectSumDensityMatrices
    {A : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ} :
    A ∈ pureDirectSumDensityMatrices d ↔
      ∃ k P, IsRankOneOrthogonalProjection P ∧ A = Pi.single k P :=
  Iff.rfl

/-- A one-block rank-one state belongs to the total-trace-one direct-sum state
space. -/
theorem pureDirectSumDensityMatrices_subset_directSumDensityMatrices :
    pureDirectSumDensityMatrices d ⊆ directSumDensityMatrices d := by
  classical
  rintro _ ⟨k, P, hP, rfl⟩
  constructor
  · intro l
    by_cases hl : l = k
    · subst l
      rw [Pi.single_eq_same]
      exact isOrthogonalProjection_posSemidef hP.1
    · rw [Pi.single_eq_of_ne hl]
      exact PosSemidef.zero
  · rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same]
      exact (IsRankOneOrthogonalProjection.mem_densityMatrices hP).2
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, Matrix.trace_zero]
    · simp

/-- The direct-sum density states are the convex hull of the one-block
rank-one states. -/
theorem directSumDensityMatrices_eq_convexHull_pureDirectSumDensityMatrices :
    directSumDensityMatrices d = convexHull ℝ (pureDirectSumDensityMatrices d) := by
  classical
  apply Set.Subset.antisymm
  · intro A hA
    let w : ((k : iota) × Fin (d k)) → ℝ := fun x ↦
      (hA.1 x.1).isHermitian.eigenvalues x.2
    let z : ((k : iota) × Fin (d k)) →
        (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) := fun x ↦
      Pi.single x.1
        (pureStateProj (fun p ↦ (hA.1 x.1).isHermitian.eigenvectorUnitary p x.2))
    apply mem_convexHull_of_exists_fintype w z
    · intro x
      exact (hA.1 x.1).eigenvalues_nonneg x.2
    · calc
        ∑ x, w x = ∑ k, ∑ i, w ⟨k, i⟩ := by
          simpa using Fintype.sum_sigma' (fun k i ↦ w ⟨k, i⟩)
        _ = ∑ k, (A k).trace.re := by
          apply Finset.sum_congr rfl
          intro k _
          have htrace := congrArg Complex.re
            (hA.1 k).isHermitian.trace_eq_sum_eigenvalues
          simpa [w, Complex.re_sum] using htrace.symm
        _ = (∑ k, (A k).trace).re := by rw [Complex.re_sum]
        _ = 1 := by rw [hA.2]; norm_num
    · intro x
      refine ⟨x.1,
        pureStateProj (fun p ↦ (hA.1 x.1).isHermitian.eigenvectorUnitary p x.2), ?_, rfl⟩
      exact IsUnitVector.isRankOneOrthogonalProjection_pureStateProj
        (eigenvectorUnitary_isUnitVector (hA.1 x.1).isHermitian x.2)
    · funext k
      simp only [Finset.sum_apply, Pi.smul_apply]
      calc
        ∑ x, w x • z x k = ∑ l, ∑ i, w ⟨l, i⟩ • z ⟨l, i⟩ k := by
          simpa using Fintype.sum_sigma'
            (fun l i ↦ w ⟨l, i⟩ • z ⟨l, i⟩ k)
        _ = ∑ i, w ⟨k, i⟩ • z ⟨k, i⟩ k := by
          rw [Finset.sum_eq_single k]
          · intro l _ hl
            apply Finset.sum_eq_zero
            intro i _
            simp only [z]
            rw [Pi.single_eq_of_ne (Ne.symm hl), smul_zero]
          · simp
        _ = ∑ i, ((hA.1 k).isHermitian.eigenvalues i : ℂ) •
              pureStateProj
                (fun p ↦ (hA.1 k).isHermitian.eigenvectorUnitary p i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [w, z, Complex.coe_smul, Pi.single_eq_same]
        _ = A k := by
          have hdecomp := (hA.1 k).eq_sum_eigenvalue_smul_eigenprojector
          simpa only [pureStateProj] using hdecomp.symm
  · exact convexHull_min
      (pureDirectSumDensityMatrices_subset_directSumDensityMatrices (d := d))
      (directSumDensityMatrices_isConvex (d := d))

/-- A one-block rank-one state is convex-extreme in the direct-sum density
state space. -/
theorem pureDirectSumDensityMatrices_subset_extremePoints :
    pureDirectSumDensityMatrices d ⊆
      Set.extremePoints ℝ (directSumDensityMatrices d) := by
  classical
  rintro _ ⟨k, P, hP, rfl⟩
  refine mem_extremePoints_iff_left.mpr
    ⟨pureDirectSumDensityMatrices_subset_directSumDensityMatrices
      (d := d) ⟨k, P, hP, rfl⟩, ?_⟩
  intro A hA B hB hsegment
  rcases hsegment with ⟨a, b, ha, hb, hab, hcombo⟩
  have hcomboC : (a : ℂ) • A + (b : ℂ) • B = Pi.single k P := by
    simpa only [Complex.coe_smul] using hcombo
  have haC : (0 : ℂ) ≤ a := by exact_mod_cast ha.le
  have hbC : (0 : ℂ) ≤ b := by exact_mod_cast hb.le
  have hoff : ∀ l, l ≠ k → A l = 0 ∧ B l = 0 := by
    intro l hl
    have hsum := congrFun hcomboC l
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      Pi.single_eq_of_ne hl] at hsum
    have hscaledA : ((a : ℂ) • A l).PosSemidef := (hA.1 l).smul haC
    have hscaledB : ((b : ℂ) • B l).PosSemidef := (hB.1 l).smul hbC
    have hAz : (a : ℂ) • A l = 0 := by
      rw [Matrix.ext_iff_mulVec]
      intro v
      rw [Matrix.zero_mulVec]
      apply hscaledA.mulVec_eq_zero_left hscaledB v
      rw [hsum, Matrix.zero_mulVec]
    have hBz : (b : ℂ) • B l = 0 := by
      rw [Matrix.ext_iff_mulVec]
      intro v
      rw [Matrix.zero_mulVec]
      apply hscaledB.mulVec_eq_zero_left hscaledA v
      rw [add_comm, hsum, Matrix.zero_mulVec]
    constructor
    · exact smul_eq_zero.mp hAz |>.resolve_left (by exact_mod_cast ha.ne')
    · exact smul_eq_zero.mp hBz |>.resolve_left (by exact_mod_cast hb.ne')
  have htraceA : (A k).trace = 1 := by
    calc
      (A k).trace = ∑ l, (A l).trace := by
        symm
        rw [Finset.sum_eq_single k]
        · intro l _ hl
          rw [(hoff l hl).1, Matrix.trace_zero]
        · simp
      _ = 1 := hA.2
  have htraceB : (B k).trace = 1 := by
    calc
      (B k).trace = ∑ l, (B l).trace := by
        symm
        rw [Finset.sum_eq_single k]
        · intro l _ hl
          rw [(hoff l hl).2, Matrix.trace_zero]
        · simp
      _ = 1 := hB.2
  have hsegmentK : P ∈ openSegment ℝ (A k) (B k) := by
    refine ⟨a, b, ha, hb, hab, ?_⟩
    have hk := congrFun hcombo k
    simpa only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same] using hk
  have hAk : A k = P :=
    (IsRankOneOrthogonalProjection.mem_extremePoints_densityMatrices hP).2
      ⟨hA.1 k, htraceA⟩ ⟨hB.1 k, htraceB⟩ hsegmentK
  funext l
  by_cases hl : l = k
  · subst l
    rw [Pi.single_eq_same]
    exact hAk
  · rw [Pi.single_eq_of_ne hl]
    exact (hoff l hl).1

/-- Wolf's relative pure-state characterization for a finite direct sum: the
convex-extreme states have one rank-one block and all other blocks zero. -/
theorem extremePoints_directSumDensityMatrices :
    Set.extremePoints ℝ (directSumDensityMatrices d) =
      pureDirectSumDensityMatrices d := by
  apply Set.Subset.antisymm
  · rw [directSumDensityMatrices_eq_convexHull_pureDirectSumDensityMatrices]
    exact extremePoints_convexHull_subset
  · exact pureDirectSumDensityMatrices_subset_extremePoints (d := d)

/-- Membership form of Wolf's relative pure-state characterization for a
finite direct sum. -/
@[simp]
theorem mem_extremePoints_directSumDensityMatrices_iff
    {A : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ} :
    A ∈ Set.extremePoints ℝ (directSumDensityMatrices d) ↔
      ∃ k P, IsRankOneOrthogonalProjection P ∧ A = Pi.single k P := by
  rw [extremePoints_directSumDensityMatrices]
  rfl

end DirectSum

end Matrix
