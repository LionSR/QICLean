/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Irreducible.Growth

/-!
# Collatz--Wielandt argument for irreducible positive maps

This file follows Wolf Theorem 6.3.  The proof begins with the lower
Collatz--Wielandt variational problem.  A real number `a ≥ 0` is feasible at a
density matrix `X` when `T X - a X ≥ 0`.  The feasible pairs form, after a
uniform trace bound on `a`, a compact set.  Hence the lower value has a
maximizer.

The upper Collatz--Wielandt quantity is not introduced at this stage.  Wolf's
proof first turns the lower maximizer into a positive-definite eigenvector by
Equation (6.31) and irreducibility; only then are the two global variational
quantities identified.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.3,
  local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`,
  lines 608--651.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A nonnegative real number `a` is lower Collatz--Wielandt feasible at `X`
for `T` when `X` is a density matrix and `T X - a X` is positive semidefinite.

This is the predicate `a ≤ r(X)` in Wolf's notation at lines 608--615. -/
def LowerCollatzWielandtFeasible (T : Mat →ₗ[ℂ] Mat) (X : Mat) (a : ℝ) : Prop :=
  X ∈ densityMatrices D ∧ 0 ≤ a ∧ (T X - (a : ℂ) • X).PosSemidef

/-- The lower Collatz--Wielandt feasible value is bounded by the trace
functional: if `T X - a X ≥ 0` and `tr X = 1`, then
`a ≤ Re tr(T X)`. -/
theorem lowerCollatzWielandtFeasible_le_re_trace
    (T : Mat →ₗ[ℂ] Mat) {X : Mat} {a : ℝ}
    (h : LowerCollatzWielandtFeasible T X a) :
    a ≤ (Matrix.trace (T X)).re := by
  have htr := h.2.2.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, h.1.2, smul_eq_mul, mul_one] at htr
  have hre := (Complex.nonneg_iff.mp htr).1
  change 0 ≤ (Matrix.trace (T X)).re - a at hre
  linarith

/-- **Wolf Theorem 6.3, lower-functional maximizer.**

For a positive map on a nonzero matrix algebra, the lower
Collatz--Wielandt feasible value attains a global maximum on density matrices.
The maximizing value is real and nonnegative. -/
theorem exists_lowerCollatzWielandt_maximizer [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) :
    ∃ X : Mat, ∃ r : ℝ,
      LowerCollatzWielandtFeasible T X r ∧
        ∀ Y : Mat, ∀ a : ℝ, LowerCollatzWielandtFeasible T Y a → a ≤ r := by
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hdensity : (densityMatrices D).Nonempty := densityMatrices_nonempty hD
  let f : Mat → ℝ := fun X => (Matrix.trace (T X)).re
  have hf : Continuous f := by
    exact Complex.continuous_re.comp
      ((T.continuous_of_finiteDimensional).matrix_trace)
  obtain ⟨Xmax, hXmax, hXmaximal⟩ :=
    densityMatrices_isCompact.exists_isMaxOn hdensity hf.continuousOn
  let M : ℝ := f Xmax
  have hM_nonneg : 0 ≤ M := by
    have hTXmax : (T Xmax).PosSemidef := hT Xmax hXmax.1
    exact (Complex.nonneg_iff.mp hTXmax.trace_nonneg).1
  let K : Set (Mat × ℝ) :=
    (densityMatrices D ×ˢ Set.Icc (0 : ℝ) M) ∩
      {p | (T p.1 - (p.2 : ℂ) • p.1).PosSemidef}
  have hresidual : Continuous (fun p : Mat × ℝ => T p.1 - (p.2 : ℂ) • p.1) := by
    fun_prop
  have hKcompact : IsCompact K := by
    exact (densityMatrices_isCompact.prod isCompact_Icc).inter_right
      (Matrix.posSemidef_is_closed.preimage hresidual)
  obtain ⟨X₀, hX₀⟩ := hdensity
  have hKnonempty : K.Nonempty := by
    refine ⟨(X₀, 0), ?_⟩
    exact ⟨⟨hX₀, ⟨le_rfl, hM_nonneg⟩⟩, by simpa using hT X₀ hX₀.1⟩
  obtain ⟨p, hpK, hpmax⟩ :=
    hKcompact.exists_isMaxOn hKnonempty continuous_snd.continuousOn
  refine ⟨p.1, p.2, ?_, ?_⟩
  · exact ⟨hpK.1.1, hpK.1.2.1, hpK.2⟩
  · intro Y a hYa
    have haM : a ≤ M :=
      (lowerCollatzWielandtFeasible_le_re_trace T hYa).trans
        (by simpa [M, f] using hXmaximal hYa.1)
    have hpair : (Y, a) ∈ K :=
      ⟨⟨hYa.1, ⟨hYa.2.1, haM⟩⟩, hYa.2.2⟩
    exact hpmax hpair

/-- **Wolf Equation (6.31).**  The polynomial `(id + T)^n` commutes with
`T - r id`. -/
theorem idPlus_pow_apply_map_sub_smul
    (T : Mat →ₗ[ℂ] Mat) (X : Mat) (r : ℂ) (n : ℕ) :
    ((LinearMap.id + T : Module.End ℂ Mat) ^ n) (T X - r • X) =
      T (((LinearMap.id + T : Module.End ℂ Mat) ^ n) X) -
        r • ((LinearMap.id + T : Module.End ℂ Mat) ^ n) X := by
  let S : Module.End ℂ Mat := (LinearMap.id + T) ^ n
  have hbase : Commute T (LinearMap.id + T : Module.End ℂ Mat) := by
    exact (Commute.one_right T).add_right (Commute.refl T)
  have hcomm : Commute T S := by
    simpa [S] using hbase.pow_right n
  have happly : T (S X) = S (T X) := by
    have h := congrArg (fun F : Module.End ℂ Mat => F X) hcomm.eq
    simpa only [Module.End.mul_apply] using h
  change S (T X - r • X) = T (S X) - r • S X
  rw [map_sub, map_smul, happly]

namespace IsPositiveMap

section

open scoped Matrix.Norms.L2Operator

/-- A positive map which annihilates a positive-definite matrix is the zero
map.  Indeed, every positive semidefinite matrix is dominated by a positive
multiple of the given positive-definite matrix, and arbitrary matrices are
complex linear combinations of four positive ones. -/
theorem eq_zero_of_map_posDef_eq_zero [NeZero D]
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T)
    {X : Mat} (hX : X.PosDef) (hTX : T X = 0) :
    T = 0 := by
  obtain ⟨c, -, hsupport_le⟩ :=
    IsPositiveMap.exists_supportProj_le_smul hX.posSemidef
  have hOne_le : (1 : Mat) ≤ c • X := by
    simpa [Kraus.stationaryProj, hX.supportProj_eq_one] using hsupport_le
  have hcX_gap : (c • X - (1 : Mat)).PosSemidef :=
    (sub_nonneg.mpr hOne_le).posSemidef
  have hmap_psd_zero (B : Mat) (hB : B.PosSemidef) : T B = 0 := by
    have htrace_gap : (B.trace • (1 : Mat) - B).PosSemidef :=
      hB.trace_smul_one_sub_self_posSemidef
    have hscaled := hcX_gap.smul hB.trace_nonneg
    have hbound : ((B.trace * c) • X - B).PosSemidef := by
      have heq :
          B.trace • (c • X - (1 : Mat)) +
              (B.trace • (1 : Mat) - B) =
            (B.trace * c) • X - B := by module
      rw [← heq]
      exact hscaled.add htrace_gap
    have himage := hT _ hbound
    rw [T.map_sub, T.map_smul, hTX, smul_zero, zero_sub] at himage
    exact le_antisymm (neg_nonneg.mp himage.nonneg) (hT B hB).nonneg
  apply LinearMap.ext
  intro Z
  obtain ⟨B, hB, -, hZ⟩ := CStarAlgebra.exists_sum_four_nonneg Z
  rw [hZ, map_sum]
  simp only [map_smul, hmap_psd_zero _ (Matrix.nonneg_iff_posSemidef.mp (hB _)),
    smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

end

end IsPositiveMap

/-- **Wolf Theorem 6.3, Perron pair from the lower maximizer.**

An irreducible positive map on a nonzero matrix algebra has a density matrix
`X > 0` and a real `r ≥ 0` such that `T X = r X`.  Moreover, `r` is the largest
lower Collatz--Wielandt feasible value.

The proof follows Wolf's Equation (6.31).  If the residual at a lower
maximizer were nonzero, the growth condition of Theorem 6.2 would make both
the transformed maximizer and transformed residual positive definite.  A
small positive multiple of the former could then be subtracted from the
latter, producing a strictly larger feasible value. -/
theorem exists_posDef_eigenvector_of_irreducible_positive [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T) :
    ∃ X : Mat, ∃ r : ℝ,
      X ∈ densityMatrices D ∧ 0 ≤ r ∧ X.PosDef ∧ T X = (r : ℂ) • X ∧
        ∀ Y : Mat, ∀ a : ℝ, LowerCollatzWielandtFeasible T Y a → a ≤ r := by
  obtain ⟨X, r, hXr, hmax⟩ := exists_lowerCollatzWielandt_maximizer T hT
  have hX_ne : X ≠ 0 := by
    intro hXzero
    have htrace := hXr.1.2
    rw [hXzero, Matrix.trace_zero] at htrace
    norm_num at htrace
  let A : Mat := T X - (r : ℂ) • X
  have hA : A.PosSemidef := hXr.2.2
  have hA_zero : A = 0 := by
    by_contra hA_ne
    let S : Module.End ℂ Mat := (LinearMap.id + T) ^ (D - 1)
    have hSX : (S X).PosDef := by
      simpa [S] using growth_posDef_of_irreducible T hT hIrr X hXr.1.1 hX_ne
    have hSA : (S A).PosDef := by
      simpa [S] using growth_posDef_of_irreducible T hT hIrr A hA hA_ne
    have hEq31 : S A = T (S X) - (r : ℂ) • S X := by
      simpa [S, A] using
        idPlus_pow_apply_map_sub_smul T X (r : ℂ) (D - 1)
    let t : ℝ := (Matrix.trace (S X)).re
    have ht : 0 < t := by
      exact (Complex.lt_def.mp hSX.trace_pos).1
    have htraceSX : Matrix.trace (S X) = (t : ℂ) := by
      apply Complex.ext
      · simp [t]
      · simpa using (Complex.nonneg_iff.mp hSX.posSemidef.trace_nonneg).2.symm
    let s : ℝ := t⁻¹
    let Y : Mat := (s : ℂ) • S X
    have hs_nonneg : (0 : ℂ) ≤ (s : ℂ) := by
      exact_mod_cast inv_nonneg.mpr ht.le
    have hYpsd : Y.PosSemidef := hSX.posSemidef.smul hs_nonneg
    have hYtrace : Matrix.trace Y = 1 := by
      change Matrix.trace ((t⁻¹ : ℝ) • S X) = 1
      rw [Matrix.trace_smul, htraceSX]
      rw [Complex.real_smul]
      norm_cast
      exact inv_mul_cancel₀ ht.ne'
    let μ : ℝ := minEigenvalue hSA.isHermitian
    have hμ : 0 < μ := minEigenvalue_pos_of_posDef hSA.isHermitian hSA
    have hSA_mu : (S A - (μ : ℂ) • (1 : Mat)).PosSemidef := by
      simpa [μ] using sub_minEigenvalue_smul_one_posSemidef hSA.isHermitian
    have htrace_gap : ((t : ℂ) • (1 : Mat) - S X).PosSemidef := by
      simpa [htraceSX] using hSX.posSemidef.trace_smul_one_sub_self_posSemidef
    let δ : ℝ := μ / t
    have hδ : 0 < δ := div_pos hμ ht
    have hδ_nonneg : (0 : ℂ) ≤ (δ : ℂ) := by exact_mod_cast hδ.le
    have hδt : (δ : ℂ) * (t : ℂ) = (μ : ℂ) := by
      exact_mod_cast div_mul_cancel₀ μ ht.ne'
    have hscaled_gap := htrace_gap.smul hδ_nonneg
    have hSA_delta : (S A - (δ : ℂ) • S X).PosSemidef := by
      have heq :
          (S A - (μ : ℂ) • (1 : Mat)) +
              (δ : ℂ) • ((t : ℂ) • (1 : Mat) - S X) =
            S A - (δ : ℂ) • S X := by
        rw [smul_sub, smul_smul, hδt]
        module
      rw [← heq]
      exact hSA_mu.add hscaled_gap
    have hres_unscaled :
        T (S X) - ((r + δ : ℝ) : ℂ) • S X =
          S A - (δ : ℂ) • S X := by
      calc
        T (S X) - ((r + δ : ℝ) : ℂ) • S X =
            (T (S X) - (r : ℂ) • S X) - (δ : ℂ) • S X := by
              push_cast
              module
        _ = S A - (δ : ℂ) • S X := by rw [← hEq31]
    have hYresidual :
        (T Y - ((r + δ : ℝ) : ℂ) • Y).PosSemidef := by
      have hscaled := hSA_delta.smul hs_nonneg
      have heq :
          T Y - ((r + δ : ℝ) : ℂ) • Y =
            (s : ℂ) • (S A - (δ : ℂ) • S X) := by
        calc
          T Y - ((r + δ : ℝ) : ℂ) • Y =
              (s : ℂ) •
                (T (S X) - ((r + δ : ℝ) : ℂ) • S X) := by
                  simp only [Y, map_smul]
                  module
          _ = (s : ℂ) • (S A - (δ : ℂ) • S X) := by rw [hres_unscaled]
      rw [heq]
      exact hscaled
    have hYfeasible : LowerCollatzWielandtFeasible T Y (r + δ) :=
      ⟨⟨hYpsd, hYtrace⟩, add_nonneg hXr.2.1 hδ.le, hYresidual⟩
    exact (not_lt_of_ge (hmax Y (r + δ) hYfeasible)) (lt_add_of_pos_right r hδ)
  have hEig : T X = (r : ℂ) • X := by
    apply sub_eq_zero.mp
    simpa [A] using hA_zero
  have hXpd : X.PosDef :=
    posDef_of_posSemidef_eigenvector_irreducible
      T hT hIrr X (r : ℂ) hXr.1.1 hX_ne hEig
  exact ⟨X, r, hXr.1, hXr.2.1, hXpd, hEig, hmax⟩

/-- **Wolf Theorem 6.3, nonzero-map form.**

If the irreducible positive map is nonzero, the Perron value supplied by
`exists_posDef_eigenvector_of_irreducible_positive` is strictly positive.
The explicit hypothesis is necessary in dimension one: the zero map on
`M₁(ℂ)` is irreducible under Wolf's projection definition, but its only
eigenvalue is zero. -/
theorem exists_posDef_eigenvector_of_irreducible_positive_of_ne_zero [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T)
    (hT_ne : T ≠ 0) :
    ∃ X : Mat, ∃ r : ℝ,
      X ∈ densityMatrices D ∧ 0 < r ∧ X.PosDef ∧ T X = (r : ℂ) • X ∧
        ∀ Y : Mat, ∀ a : ℝ, LowerCollatzWielandtFeasible T Y a → a ≤ r := by
  obtain ⟨X, r, hX, hr, hXpd, hEig, hmax⟩ :=
    exists_posDef_eigenvector_of_irreducible_positive T hT hIrr
  have hrpos : 0 < r := by
    apply lt_of_le_of_ne hr
    intro hzero
    apply hT_ne
    apply hT.eq_zero_of_map_posDef_eq_zero hXpd
    simpa [hzero.symm] using hEig
  exact ⟨X, r, hX, hrpos, hXpd, hEig, hmax⟩
