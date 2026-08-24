/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Irreducible.FixedPointUniqueness
import QICLean.Channel.Irreducible.Growth
import QICLean.Channel.Irreducible.AdjointFamily

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

/-- A positive-definite weight has strictly positive trace pairing with every
nonzero positive semidefinite matrix. -/
private theorem trace_mul_pos_of_posDef_posSemidef_ne_zero
    {X₀ Y : Mat} (hX₀ : X₀.PosDef) (hY : Y.PosSemidef) (hY_ne : Y ≠ 0) :
    0 < Matrix.trace (X₀ * Y) := by
  have hnonneg : 0 ≤ Matrix.trace (X₀ * Y) :=
    hX₀.posSemidef.trace_mul_nonneg hY
  have hne : Matrix.trace (X₀ * Y) ≠ 0 := by
    intro hzero
    exact hY_ne
      (Matrix.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero hY hX₀ hzero)
  exact lt_of_le_of_ne hnonneg (by simpa only [ne_eq, eq_comm] using hne)

/-- A real number `a` is lower Collatz--Wielandt feasible at `X` for `T` when
`X` is a density matrix and `T X - a X` is positive semidefinite.

This is the predicate `a ≤ r(X)` in Wolf's notation at lines 608--615. -/
def LowerCollatzWielandtFeasible (T : Mat →ₗ[ℂ] Mat) (X : Mat) (a : ℝ) : Prop :=
  X ∈ densityMatrices D ∧ (T X - (a : ℂ) • X).PosSemidef

/-- A real number `a` is upper Collatz--Wielandt feasible at `X` when `X` is a
density matrix and `a X - T X` is positive semidefinite.

This is the predicate `tilde r(X) ≤ a` in Wolf Equation (6.30).  The global
upper quantity is an infimum, correcting the second supremum printed on Wolf
line 618. -/
def UpperCollatzWielandtFeasible (T : Mat →ₗ[ℂ] Mat) (X : Mat) (a : ℝ) : Prop :=
  X ∈ densityMatrices D ∧ ((a : ℂ) • X - T X).PosSemidef

/-- A nonnegative eigenvalue with a density-matrix eigenvector is feasible
for both the lower and upper Collatz--Wielandt problems at that vector. -/
theorem lower_and_upperCollatzWielandtFeasible_of_eigenvector
    (T : Mat →ₗ[ℂ] Mat) {X : Mat} {r : ℝ}
    (hX : X ∈ densityMatrices D) (hEig : T X = (r : ℂ) • X) :
    LowerCollatzWielandtFeasible T X r ∧
      UpperCollatzWielandtFeasible T X r := by
  constructor
  · exact ⟨hX, by rw [hEig, sub_self]; exact Matrix.PosSemidef.zero⟩
  · exact ⟨hX, by rw [hEig, sub_self]; exact Matrix.PosSemidef.zero⟩

/-- The lower Collatz--Wielandt feasible value is bounded by the trace
functional: if `T X - a X ≥ 0` and `tr X = 1`, then
`a ≤ Re tr(T X)`. -/
theorem lowerCollatzWielandtFeasible_le_re_trace
    (T : Mat →ₗ[ℂ] Mat) {X : Mat} {a : ℝ}
    (h : LowerCollatzWielandtFeasible T X a) :
    a ≤ (Matrix.trace (T X)).re := by
  have htr := h.2.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, h.1.2, smul_eq_mul, mul_one] at htr
  have hre := (Complex.nonneg_iff.mp htr).1
  change 0 ≤ (Matrix.trace (T X)).re - a at hre
  linarith

/-- Every upper Collatz--Wielandt feasible value for a positive map is
nonnegative.  This is a consequence of positivity and the trace-one
normalization, rather than part of the source feasibility predicate. -/
theorem upperCollatzWielandtFeasible_nonneg
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) {X : Mat} {a : ℝ}
    (h : UpperCollatzWielandtFeasible T X a) :
    0 ≤ a := by
  have hTX : (T X).PosSemidef := hT X h.1.1
  have hTXtrace := hTX.trace_nonneg
  have hgaptrace := h.2.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, h.1.2, smul_eq_mul, mul_one] at hgaptrace
  have hTXre : 0 ≤ (Matrix.trace (T X)).re :=
    (Complex.nonneg_iff.mp hTXtrace).1
  have hgapre := (Complex.nonneg_iff.mp hgaptrace).1
  change 0 ≤ a - (Matrix.trace (T X)).re at hgapre
  linarith

/-- **Wolf Theorem 6.3, lower-functional maximizer.**

For a positive map on a nonzero matrix algebra, the lower
Collatz--Wielandt feasible value attains a global maximum on density matrices.
The maximizing value is real and nonnegative. -/
theorem exists_lowerCollatzWielandt_maximizer [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) :
    ∃ X : Mat, ∃ r : ℝ,
      0 ≤ r ∧ LowerCollatzWielandtFeasible T X r ∧
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
  refine ⟨p.1, p.2, hpK.1.2.1, ?_, ?_⟩
  · exact ⟨hpK.1.1, hpK.2⟩
  · intro Y a hYa
    by_cases ha : 0 ≤ a
    · have haM : a ≤ M :=
        (lowerCollatzWielandtFeasible_le_re_trace T hYa).trans
          (by simpa [M, f] using hXmaximal hYa.1)
      have hpair : (Y, a) ∈ K :=
        ⟨⟨hYa.1, ⟨ha, haM⟩⟩, hYa.2⟩
      exact hpmax hpair
    · exact (le_of_not_ge ha).trans hpK.1.2.1

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

/-- **Wolf Equation (6.32), algebraic identity.**  If `T X = r X` for a real
`r`, then `(id + T)^n X = (1 + r)^n X`. -/
theorem idPlus_pow_apply_of_real_eigenvector
    (T : Mat →ₗ[ℂ] Mat) (X : Mat) (r : ℝ)
    (hEig : T X = (r : ℂ) • X) (n : ℕ) :
    ((LinearMap.id + T : Module.End ℂ Mat) ^ n) X =
      (((1 + r) ^ n : ℝ) : ℂ) • X := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul]
      simp only [LinearMap.add_apply, LinearMap.id_apply, hEig]
      push_cast
      rw [pow_succ]
      module

section

open scoped Matrix.Norms.L2Operator

/-- A Hermitian matrix becomes positive definite after adding a sufficiently
large positive multiple of a prescribed positive-definite matrix. -/
private theorem exists_posDef_add_real_smul [NeZero D]
    {X H : Mat} (hX : X.PosDef) (hH : H.IsHermitian) :
    ∃ b : ℝ, 0 < b ∧ ((b : ℂ) • X + H).PosDef := by
  classical
  let μ : ℝ := minEigenvalue hX.isHermitian
  have hμ : 0 < μ := minEigenvalue_pos_of_posDef hX.isHermitian hX
  let b : ℝ := (‖H‖ + 1) / μ
  have hb : 0 < b := div_pos (by positivity) hμ
  have hXgap : (X - (μ : ℂ) • (1 : Mat)).PosSemidef := by
    simpa [μ] using sub_minEigenvalue_smul_one_posSemidef hX.isHermitian
  have hHlower : ((-‖H‖ : ℝ) : ℂ) • (1 : Mat) ≤ H := by
    simpa [Algebra.algebraMap_eq_smul_one] using
      (isSelfAdjoint_iff.mpr hH).neg_algebraMap_norm_le_self
  have hHgap : (H + ((‖H‖ : ℝ) : ℂ) • (1 : Mat)).PosSemidef := by
    have h := (sub_nonneg.mpr hHlower).posSemidef
    push_cast at h
    simpa only [neg_smul, sub_neg_eq_add] using h
  have hb_nonneg : (0 : ℂ) ≤ (b : ℂ) := by exact_mod_cast hb.le
  have hscaled := hXgap.smul hb_nonneg
  have hbμ : (b : ℂ) * (μ : ℂ) = (((‖H‖ + 1 : ℝ)) : ℂ) := by
    exact_mod_cast div_mul_cancel₀ (‖H‖ + 1) hμ.ne'
  have hsum : ((b : ℂ) • X + H - (1 : Mat)).PosSemidef := by
    have heq :
        (b : ℂ) • (X - (μ : ℂ) • (1 : Mat)) +
            (H + ((‖H‖ : ℝ) : ℂ) • (1 : Mat)) =
          (b : ℂ) • X + H - (1 : Mat) := by
      rw [smul_sub, smul_smul, hbμ]
      push_cast
      module
    rw [← heq]
    exact hscaled.add hHgap
  refine ⟨b, hb, ?_⟩
  have hpd := Matrix.PosDef.one.add_posSemidef hsum
  have heq : (1 : Mat) + ((b : ℂ) • X + H - 1) = (b : ℂ) • X + H := by
    module
  rw [heq] at hpd
  exact hpd

end

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
  obtain ⟨X, r, hr, hXr, hmax⟩ := exists_lowerCollatzWielandt_maximizer T hT
  have hX_ne : X ≠ 0 := by
    intro hXzero
    have htrace := hXr.1.2
    rw [hXzero, Matrix.trace_zero] at htrace
    norm_num at htrace
  let A : Mat := T X - (r : ℂ) • X
  have hA : A.PosSemidef := hXr.2
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
      ⟨⟨hYpsd, hYtrace⟩, hYresidual⟩
    exact (not_lt_of_ge (hmax Y (r + δ) hYfeasible)) (lt_add_of_pos_right r hδ)
  have hEig : T X = (r : ℂ) • X := by
    apply sub_eq_zero.mp
    simpa [A] using hA_zero
  have hXpd : X.PosDef :=
    posDef_of_posSemidef_eigenvector_irreducible
      T hT hIrr X (r : ℂ) hXr.1.1 hX_ne hEig
  exact ⟨X, r, hXr.1, hr, hXpd, hEig, hmax⟩

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

/-! ## Wolf Equation (6.32): one-dimensional Perron eigenspace -/

/-- A Hermitian eigenvector at the nonnegative Perron value is proportional to a
positive-definite Perron eigenvector.

The proof is Wolf's boundary argument.  After shifting `H` by a large multiple
of `X`, the critical-scalar construction gives a nonzero positive-semidefinite
boundary eigenvector `W` unless `H` is already proportional to `X`.  Theorem
6.2 and Equation (6.32) make that `W` positive definite, contradicting its
boundary construction. -/
theorem isHermitian_eigenvector_eq_smul_of_irreducible_positive [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T)
    {X H : Mat} {r : ℝ} (hr : 0 ≤ r)
    (hX : X.PosDef) (hX_eig : T X = (r : ℂ) • X)
    (hH : H.IsHermitian) (hH_eig : T H = (r : ℂ) • H) :
    ∃ c : ℂ, H = c • X := by
  obtain ⟨b, hb, hσpd⟩ := exists_posDef_add_real_smul hX hH
  let σ : Mat := (b : ℂ) • X + H
  have hσ_eig : T σ = (r : ℂ) • σ := by
    simp only [σ, map_add, map_smul, hX_eig, hH_eig]
    module
  have hσpd' : σ.PosDef := by simpa [σ] using hσpd
  obtain ⟨c, -, hWpsd, hWnotpd⟩ := exists_critical_scalar hX hσpd'
  let W : Mat := σ - (c : ℂ) • X
  have hW_eig : T W = (r : ℂ) • W := by
    simp only [W, map_sub, map_smul, hσ_eig, hX_eig]
    module
  by_cases hWzero : W = 0
  · refine ⟨(c : ℂ) - (b : ℂ), ?_⟩
    have hEq : (b : ℂ) • X + H = (c : ℂ) • X := by
      exact sub_eq_zero.mp (by simpa [W, σ] using hWzero)
    calc
      H = (c : ℂ) • X - (b : ℂ) • X := by rw [← hEq]; module
      _ = ((c : ℂ) - (b : ℂ)) • X := by module
  · have hSW :
        (((LinearMap.id + T : Module.End ℂ Mat) ^ (D - 1)) W).PosDef :=
      growth_posDef_of_irreducible T hT hIrr W (by simpa [W] using hWpsd) hWzero
    have hEq32 := idPlus_pow_apply_of_real_eigenvector T W r hW_eig (D - 1)
    let α : ℝ := (1 + r) ^ (D - 1)
    have hα : 0 < α := pow_pos (by linarith) _
    have hαinv : (0 : ℂ) < ((α : ℂ)⁻¹) := by
      exact_mod_cast inv_pos.mpr hα
    rw [hEq32] at hSW
    have hWpd_scaled := hSW.smul hαinv
    have hαne : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
    have hWpd : W.PosDef := by
      simpa only [α, smul_smul, inv_mul_cancel₀ hαne, one_smul] using hWpd_scaled
    exact (hWnotpd (by simpa [W] using hWpd)).elim

/-- Every complex eigenvector at the nonnegative Perron value is proportional to
the positive-definite Perron eigenvector.

Following Wolf's proof before Equation (6.32), the eigenvector is split into
its Hermitian and skew-Hermitian parts.  Positivity of `T` ensures that both
parts remain eigenvectors at the same real eigenvalue, and the boundary
argument is applied to each part. -/
theorem eigenvector_eq_smul_of_irreducible_positive [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T)
    {X Z : Mat} {r : ℝ} (hr : 0 ≤ r)
    (hX : X.PosDef) (hX_eig : T X = (r : ℂ) • X)
    (hZ_eig : T Z = (r : ℂ) • Z) :
    ∃ c : ℂ, Z = c • X := by
  obtain ⟨H₁, H₂, hH₁def, hH₂def, hH₁, hH₂, hZdecomp⟩ :=
    Matrix.exists_isHermitian_decomposition Z
  have hZstar_eig : T Zᴴ = (r : ℂ) • Zᴴ := by
    calc
      T Zᴴ = (T Z)ᴴ := hT.map_conjTranspose Z
      _ = ((r : ℂ) • Z)ᴴ := by rw [hZ_eig]
      _ = (r : ℂ) • Zᴴ := by simp
  have hH₁_eig : T H₁ = (r : ℂ) • H₁ := by
    simp only [hH₁def, map_add, hZ_eig, hZstar_eig]
    module
  have hH₂_eig : T H₂ = (r : ℂ) • H₂ := by
    simp only [hH₂def, map_smul, map_sub, hZ_eig, hZstar_eig]
    module
  obtain ⟨c₁, hc₁⟩ := isHermitian_eigenvector_eq_smul_of_irreducible_positive
    T hT hIrr hr hX hX_eig hH₁ hH₁_eig
  obtain ⟨c₂, hc₂⟩ := isHermitian_eigenvector_eq_smul_of_irreducible_positive
    T hT hIrr hr hX hX_eig hH₂ hH₂_eig
  refine ⟨(2⁻¹ : ℂ) * c₁ - ((2⁻¹ : ℂ) * Complex.I) * c₂, ?_⟩
  rw [hZdecomp, hc₁, hc₂]
  module

/-- The eigenspace at the nonnegative Perron value is the span of the
positive-definite Perron eigenvector.  This is geometric non-degeneracy in
Wolf Theorem 6.3(2); it does not assert algebraic simplicity. -/
theorem eigenspace_eq_span_of_irreducible_positive [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T)
    {X : Mat} {r : ℝ} (hr : 0 ≤ r)
    (hX : X.PosDef) (hX_eig : T X = (r : ℂ) • X) :
    Module.End.eigenspace T (r : ℂ) = ℂ ∙ X := by
  apply le_antisymm
  · intro Z hZ
    obtain ⟨c, hc⟩ := eigenvector_eq_smul_of_irreducible_positive
      T hT hIrr hr hX hX_eig (Module.End.mem_eigenspace_iff.mp hZ)
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · apply Submodule.span_le.mpr
    intro Z hZ
    rw [Set.mem_singleton_iff] at hZ
    subst Z
    exact Module.End.mem_eigenspace_iff.mpr hX_eig

/-- The ordinary eigenspace at the nonnegative Perron value has complex dimension
one.  No statement about the generalized eigenspace is made. -/
theorem finrank_eigenspace_eq_one_of_irreducible_positive [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T)
    {X : Mat} {r : ℝ} (hr : 0 ≤ r)
    (hX : X.PosDef) (hX_eig : T X = (r : ℂ) • X) :
    Module.finrank ℂ (Module.End.eigenspace T (r : ℂ)) = 1 := by
  rw [eigenspace_eq_span_of_irreducible_positive T hT hIrr hr hX hX_eig]
  apply finrank_span_singleton
  intro hXzero
  have htrace := hX.trace_pos
  simp [hXzero] at htrace

/-! ## Wolf Equation (6.33): comparison with positive eigenvectors -/

/-- The Perron value of an irreducible positive map is also an eigenvalue of
the trace-pairing adjoint, with a positive-definite eigenvector.

The proof uses the positive-map trace-adjoint irreducibility observation on
Wolf lines 604--606, applies the preceding Perron construction to `T*`, and
then identifies the two Perron values by the trace pairing.  This is the first
step of Wolf Equation (6.33). -/
theorem exists_posDef_traceAdjointMap_eigenvector_at_perron [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T)
    {X : Mat} {r : ℝ} (hr : 0 < r)
    (hX : X.PosDef) (hX_eig : T X = (r : ℂ) • X) :
    ∃ X₀ : Mat, X₀.PosDef ∧
      Matrix.traceAdjointMap T X₀ = (r : ℂ) • X₀ := by
  have hr_complex : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hX_ne : X ≠ 0 := by
    intro hXzero
    have htrace := hX.trace_pos
    simp [hXzero] at htrace
  have hT_ne : T ≠ 0 := by
    intro hTzero
    have hsmul : (r : ℂ) • X = 0 := by
      rw [← hX_eig, hTzero, LinearMap.zero_apply]
    exact hX_ne ((smul_eq_zero.mp hsmul).resolve_left hr_complex)
  have hTstar_ne : Matrix.traceAdjointMap T ≠ 0 := by
    intro hTstar_zero
    apply hT_ne
    have hdouble := congrArg Matrix.traceAdjointMap hTstar_zero
    rw [Matrix.traceAdjointMap_traceAdjointMap] at hdouble
    have hzero : Matrix.traceAdjointMap (0 : Mat →ₗ[ℂ] Mat) = 0 := by
      apply LinearMap.ext
      intro ρ
      ext i j
      simp [Matrix.traceAdjointMap]
    rw [hzero] at hdouble
    exact hdouble
  obtain ⟨X₀, s, -, hs, hX₀, hX₀_eig, -⟩ :=
    exists_posDef_eigenvector_of_irreducible_positive_of_ne_zero
      (Matrix.traceAdjointMap T) hT.traceAdjointMap
      (hIrr.traceAdjointMap hT) hTstar_ne
  have htrace_pos : 0 < Matrix.trace (X₀ * X) :=
    trace_mul_pos_of_posDef_posSemidef_ne_zero hX₀ hX.posSemidef hX_ne
  have htrace_ne : Matrix.trace (X₀ * X) ≠ 0 := ne_of_gt htrace_pos
  have hpair := Matrix.trace_traceAdjointMap_mul T X₀ X
  rw [hX₀_eig, hX_eig] at hpair
  have hsr_complex : (s : ℂ) = (r : ℂ) := by
    apply mul_right_cancel₀ htrace_ne
    simpa only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul] using hpair
  have hsr : s = r := by exact_mod_cast hsr_complex
  subst s
  exact ⟨X₀, hX₀, hX₀_eig⟩

/-- **Wolf Equation (6.33).**  Let `r > 0` have a positive-definite
eigenvector for an irreducible positive map.  Any positive eigenvalue `λ > 0`
which has a nonzero positive semidefinite eigenvector equals `r`.

The positive-definite `r`-eigenvector `X₀` of the trace adjoint gives
`r tr(X₀ Y) = tr(T*(X₀)Y) = tr(X₀ T(Y)) = λ tr(X₀ Y)`.
Faithfulness of the positive-definite weighted trace permits cancellation. -/
theorem positive_eigenvalue_eq_perron_of_irreducible_positive [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T)
    {X Y : Mat} {r lam : ℝ} (hr : 0 < r)
    (hX : X.PosDef) (hX_eig : T X = (r : ℂ) • X)
    (_hlam : 0 < lam) (hY : Y.PosSemidef) (hY_ne : Y ≠ 0)
    (hY_eig : T Y = (lam : ℂ) • Y) :
    lam = r := by
  obtain ⟨X₀, hX₀, hX₀_eig⟩ :=
    exists_posDef_traceAdjointMap_eigenvector_at_perron
      T hT hIrr hr hX hX_eig
  have htrace_pos : 0 < Matrix.trace (X₀ * Y) :=
    trace_mul_pos_of_posDef_posSemidef_ne_zero hX₀ hY hY_ne
  have htrace_ne : Matrix.trace (X₀ * Y) ≠ 0 := ne_of_gt htrace_pos
  have hpair := Matrix.trace_traceAdjointMap_mul T X₀ Y
  rw [hX₀_eig, hY_eig] at hpair
  have hrlam_complex : (r : ℂ) = (lam : ℂ) := by
    apply mul_right_cancel₀ htrace_ne
    simpa only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul] using hpair
  exact_mod_cast hrlam_complex.symm

/-- Every upper Collatz--Wielandt feasible value lies above a positive Perron
value.  The proof is the order form of Wolf Equation (6.33): pair the positive
semidefinite upper residual with the positive-definite Perron eigenvector of
the trace adjoint. -/
theorem perron_le_upperCollatzWielandtFeasible [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T)
    {X Y : Mat} {r a : ℝ} (hr : 0 < r)
    (hX : X.PosDef) (hX_eig : T X = (r : ℂ) • X)
    (hYa : UpperCollatzWielandtFeasible T Y a) :
    r ≤ a := by
  obtain ⟨X₀, hX₀, hX₀_eig⟩ :=
    exists_posDef_traceAdjointMap_eigenvector_at_perron
      T hT hIrr hr hX hX_eig
  have hY_ne : Y ≠ 0 := by
    intro hYzero
    have htrace := hYa.1.2
    rw [hYzero, Matrix.trace_zero] at htrace
    norm_num at htrace
  have htrace_pos : 0 < Matrix.trace (X₀ * Y) :=
    trace_mul_pos_of_posDef_posSemidef_ne_zero hX₀ hYa.1.1 hY_ne
  have hpair := Matrix.trace_traceAdjointMap_mul T X₀ Y
  have htrace_map :
      Matrix.trace (X₀ * T Y) = (r : ℂ) * Matrix.trace (X₀ * Y) := by
    rw [← hpair, hX₀_eig, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have hgap_nonneg :
      0 ≤ Matrix.trace (X₀ * ((a : ℂ) • Y - T Y)) :=
    hX₀.posSemidef.trace_mul_nonneg hYa.2
  have hgap_eq :
      Matrix.trace (X₀ * ((a : ℂ) • Y - T Y)) =
        (((a - r : ℝ) : ℂ) * Matrix.trace (X₀ * Y)) := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul, htrace_map]
    push_cast
    ring
  rw [hgap_eq] at hgap_nonneg
  have hgap_re_nonneg := (Complex.nonneg_iff.mp hgap_nonneg).1
  have htrace_re_pos := (Complex.lt_def.mp htrace_pos).1
  rw [Complex.mul_re] at hgap_re_nonneg
  norm_num at hgap_re_nonneg
  norm_num at htrace_re_pos
  nlinarith

/-- **Wolf Theorem 6.3(1), corrected global form.**  For an irreducible
positive map, the maximum of the lower Collatz--Wielandt feasible values and
the minimum of the upper feasible values are attained at the same
positive-definite density-matrix eigenvector.

The upper extremum is a minimum, correcting the second supremum printed on
Wolf line 618.  This theorem makes no false pointwise claim for arbitrary
positive semidefinite matrices. -/
theorem exists_posDef_common_collatzWielandt_value_of_irreducible_positive
    [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T) :
    ∃ X : Mat, ∃ r : ℝ,
      X ∈ densityMatrices D ∧ 0 ≤ r ∧ X.PosDef ∧
        T X = (r : ℂ) • X ∧
        LowerCollatzWielandtFeasible T X r ∧
        UpperCollatzWielandtFeasible T X r ∧
        (∀ Y : Mat, ∀ a : ℝ, LowerCollatzWielandtFeasible T Y a → a ≤ r) ∧
        (∀ Y : Mat, ∀ a : ℝ, UpperCollatzWielandtFeasible T Y a → r ≤ a) := by
  obtain ⟨X, r, hXdensity, hr, hX, hX_eig, hLowerMax⟩ :=
    exists_posDef_eigenvector_of_irreducible_positive T hT hIrr
  obtain ⟨hLowerAtX, hUpperAtX⟩ :=
    lower_and_upperCollatzWielandtFeasible_of_eigenvector
      T hXdensity hX_eig
  have hUpperMin :
      ∀ Y : Mat, ∀ a : ℝ, UpperCollatzWielandtFeasible T Y a → r ≤ a := by
    intro Y a hYa
    by_cases hrzero : r = 0
    · simpa only [hrzero] using upperCollatzWielandtFeasible_nonneg T hT hYa
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
      exact perron_le_upperCollatzWielandtFeasible
        T hT hIrr hrpos hX hX_eig hYa
  exact ⟨X, r, hXdensity, hr, hX, hX_eig, hLowerAtX, hUpperAtX,
    hLowerMax, hUpperMin⟩
