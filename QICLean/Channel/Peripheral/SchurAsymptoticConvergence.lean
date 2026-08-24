/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.UnitarySchurTriangularization
import QICLean.Analysis.UpperTriangularBound
import QICLean.Channel.Determinant.Bound
import QICLean.Channel.FixedPoint.StationaryStates
import QICLean.Channel.Peripheral.SpectralProjection
import QICLean.Channel.TransferMatrix

/-!
# Schur-form asymptotic convergence

This file develops Wolf's Schur-decomposition route to the explicit
asymptotic convergence estimate in Equation (8.111).  The peripheral spectral
projection `T_φ` and the phase-weighted peripheral map `T_ϕ = T T_φ` remain
distinct throughout.

The first result transports the exact positive-power identity
`T ^ n - T_ϕ ^ n = (T - T_ϕ) ^ n` to transfer matrices.  The restriction
`0 < n` is essential: at `n = 0` the left-hand side vanishes and the
right-hand side is the identity.  Thus the later natural-exponent condition
`d^2 - 1 ≤ n` must not by itself be used to claim the printed all-`n`
statement when `d = 1`.

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8,
Theorem "Asymptotic convergence II", Equation (8.111); local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1295--1316.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

variable {D : ℕ}

/-- The transfer-matrix form of the positive-power identity underlying Wolf
Equation (8.111):
`T̂ ^ n - T̂_ϕ ^ n = (T - T_ϕ)̂ ^ n` for `0 < n`.

This uses the phase-weighted peripheral map `T_ϕ`, not the projection `T_φ`.
No positivity or complete-positivity hypothesis is needed for the algebraic
identity. -/
theorem transferMatrix_pow_sub_peripheralWeightedProjection_pow
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) {n : ℕ} (hn : 0 < n) :
    transferMatrix T ^ n - transferMatrix T.peripheralWeightedProjection ^ n =
      transferMatrix (T - T.peripheralWeightedProjection) ^ n := by
  rw [← transferMatrix_pow, ← transferMatrix_pow, ← transferMatrix_pow]
  calc
    transferMatrix (T ^ n) - transferMatrix (T.peripheralWeightedProjection ^ n) =
        transferMatrix (T ^ n - T.peripheralWeightedProjection ^ n) :=
      ((transferMatrixLM (D := D)).map_sub _ _).symm
    _ = transferMatrix ((T - T.peripheralWeightedProjection) ^ n) :=
      congrArg transferMatrix (T.pow_sub_peripheralWeightedProjection_pow hn)

/-! ### Canonical `d²`-dimensional coordinates -/

/-- Wolf's transfer matrix, with its product index relabelled by the canonical
equivalence `(Fin D × Fin D) ≃ Fin (D * D)`.  This is the coordinate space in
which the exponent `d² - 1` in Equation (8.111) is represented literally. -/
noncomputable def transferMatrixFin
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) :
    Matrix (Fin (D * D)) (Fin (D * D)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (transferMatrix T)

/-- Relabelling the transfer-matrix coordinates does not change the
eigenvalues of the represented endomorphism. -/
theorem transferMatrixFin_hasEigenvalue_iff
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (z : ℂ) :
    Module.End.HasEigenvalue (transferMatrixFin T).toLin' z ↔
      Module.End.HasEigenvalue T z := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin',
    transferMatrixFin, Matrix.charpoly_reindex, ← Matrix.charpoly_toLin',
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  exact (transferMatrix_hasEigenvalue_iff T z).symm

/-! ### Spectrum after removing the phase-weighted peripheral map -/

/-- The eigenvalues of `T - T_ϕ` are precisely zero together with Wolf's
subperipheral spectrum of `T`.

The zero eigenvalue records the removed peripheral summand.  For a nonzero
eigenvalue, applying `T_φ` to an eigenvector of `T - T_ϕ` shows that its
peripheral component vanishes; the same vector is consequently an eigenvector
of `T`.  Positivity and trace preservation place that eigenvalue in the closed
unit disc, and the peripheral case would force the vector back into the range
of `T_φ`, a contradiction.

Source: Wolf, Chapter 8, proof of Equation (8.111), local source lines
1299--1316. -/
theorem IsPositiveMap.hasEigenvalue_sub_peripheralWeightedProjection_iff
    [NeZero D] {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) (z : ℂ) :
    Module.End.HasEigenvalue (T - T.peripheralWeightedProjection) z ↔
      z = 0 ∨ z ∈ T.subperipheralSpectrum := by
  constructor
  · intro hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      obtain ⟨X, hX⟩ := hz.exists_hasEigenvector
      have hcomm_apply (Y : Matrix (Fin D) (Fin D) ℂ) :
          T.peripheralProjection (T Y) = T (T.peripheralProjection Y) := by
        simpa only [LinearMap.comp_apply] using
          LinearMap.congr_fun T.peripheralProjection_comp Y
      have hP_sub : T.peripheralProjection
          ((T - T.peripheralWeightedProjection) X) = 0 := by
        rw [LinearMap.sub_apply, map_sub, Module.End.peripheralWeightedProjection,
          LinearMap.comp_apply, hcomm_apply X,
          hcomm_apply (T.peripheralProjection X),
          T.peripheralProjection_apply_peripheralProjection, sub_self]
      have hP_smul := congrArg T.peripheralProjection hX.apply_eq_smul
      rw [hP_sub, map_smul] at hP_smul
      have hPX : T.peripheralProjection X = 0 := by
        exact (smul_eq_zero.mp hP_smul.symm).resolve_left hz0
      have hWX : T.peripheralWeightedProjection X = 0 := by
        rw [Module.End.peripheralWeightedProjection, LinearMap.comp_apply, hPX, map_zero]
      have hTX : T X = z • X := by
        calc
          T X = (T - T.peripheralWeightedProjection) X +
              T.peripheralWeightedProjection X := by
            rw [LinearMap.sub_apply, sub_add_cancel]
          _ = z • X := by rw [hX.apply_eq_smul, hWX, add_zero]
      have hzT : Module.End.HasEigenvalue T z := by
        apply Module.End.hasEigenvalue_of_hasEigenvector
        rw [Module.End.hasEigenvector_iff]
        exact ⟨Module.End.mem_eigenspace_iff.mpr hTX, hX.2⟩
      refine ⟨hzT, ?_⟩
      apply lt_of_le_of_ne
      · exact hPos.eigenvalue_norm_le_one_of_tracePreserving hTP z hzT
      · intro hzNorm
        have hPfix := T.peripheralProjection_apply_of_mem_eigenspace hzT hzNorm
          (Module.End.mem_eigenspace_iff.mpr hTX)
        apply hX.2
        rw [← hPfix, hPX]
  · rintro (rfl | hz)
    · obtain ⟨ρ, hρ, hρfix⟩ :=
        IsStationaryMap.exists_stationaryState_of_linear T hPos hTP
      have hρ0 : ρ ≠ 0 := by
        intro hzero
        have htrace := hρ.2
        rw [hzero, Matrix.trace_zero] at htrace
        exact zero_ne_one htrace
      have hρEig : ρ ∈ T.eigenspace 1 :=
        Module.End.mem_eigenspace_iff.mpr (by simpa using hρfix)
      have hOne : Module.End.HasEigenvalue T 1 := by
        apply Module.End.hasEigenvalue_of_hasEigenvector
        rw [Module.End.hasEigenvector_iff]
        exact ⟨hρEig, hρ0⟩
      have hWρ : T.peripheralWeightedProjection ρ = ρ := by
        simpa using T.peripheralWeightedProjection_apply_of_mem_eigenspace hOne
          (by simp) hρEig
      apply Module.End.hasEigenvalue_of_hasEigenvector
      rw [Module.End.hasEigenvector_iff]
      refine ⟨?_, hρ0⟩
      rw [Module.End.mem_eigenspace_iff, LinearMap.sub_apply, hρfix, hWρ,
        sub_self, zero_smul]
    · obtain ⟨X, hX⟩ := hz.1.exists_hasEigenvector
      have hzNonperipheral : z ∈ {w : ℂ | T.HasEigenvalue w ∧ ‖w‖ ≠ 1} :=
        ⟨hz.1, ne_of_lt hz.2⟩
      have hXnonperipheral : X ∈ T.nonPeripheralSubspace := by
        rw [Module.End.nonPeripheralSubspace]
        exact le_biSup T.maxGenEigenspace hzNonperipheral
          (Module.End.eigenspace_le_maxGenEigenspace hX.1)
      have hPX : T.peripheralProjection X = 0 :=
        T.peripheralProjection_apply_eq_zero_iff.mpr hXnonperipheral
      apply Module.End.hasEigenvalue_of_hasEigenvector
      rw [Module.End.hasEigenvector_iff]
      refine ⟨?_, hX.2⟩
      rw [Module.End.mem_eigenspace_iff, LinearMap.sub_apply,
        Module.End.peripheralWeightedProjection, LinearMap.comp_apply, hPX, map_zero,
        sub_zero]
      exact hX.apply_eq_smul

/-! ### Source-specific Schur data -/

/-- The Schur data used in Wolf's proof of Equation (8.111).

For a positive trace-preserving map `T`, the canonically relabelled transfer
matrix of `T - T_ϕ` has a unitary Schur representation
`U (Λ + N) U†`.  Here `Λ` is diagonal, `N` is strictly upper triangular, and
the diagonal entries are exactly zero together with the subperipheral
eigenvalues of `T`.  Consequently `‖Λ‖∞` is the shared
`T.subperipheralModulus`, including the case in which that set is empty or
contains only zero.

The phase-weighted map `T_ϕ = T T_φ`, rather than the peripheral projection
`T_φ`, is removed before taking the Schur decomposition.

Source: Wolf, Chapter 8, proof of Equation (8.111), local source lines
1295--1316. -/
theorem IsPositiveMap.exists_wolf_eq_111_schur_data
    [NeZero D] {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ∃ (U : Matrix.unitaryGroup (Fin (D * D)) ℂ)
        (Λ N : Matrix (Fin (D * D)) (Fin (D * D)) ℂ),
      IsDiag Λ ∧ IsStrictlyUpperTriangular N ∧
      transferMatrixFin (T - T.peripheralWeightedProjection) =
        (U : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) * (Λ + N) *
          (U : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)ᴴ ∧
      (∀ z : ℂ, (∃ i : Fin (D * D), Λ i i = z) ↔
        z = 0 ∨ z ∈ T.subperipheralSpectrum) ∧
      ‖Λ‖ = T.subperipheralModulus := by
  let A := transferMatrixFin (T - T.peripheralWeightedProjection)
  obtain ⟨U, R, hR_upper, hA, hR_spectrum⟩ :=
    Matrix.exists_unitary_schur_triangularization A
  let Λ := Matrix.diagonal (Matrix.diag R)
  let N := R - Λ
  have hΛ_spectrum : ∀ z : ℂ, (∃ i : Fin (D * D), Λ i i = z) ↔
      z = 0 ∨ z ∈ T.subperipheralSpectrum := by
    intro z
    calc
      (∃ i : Fin (D * D), Λ i i = z) ↔
          ∃ i : Fin (D * D), R i i = z := by simp [Λ]
      _ ↔ Module.End.HasEigenvalue A.toLin' z := (hR_spectrum z).symm
      _ ↔ Module.End.HasEigenvalue (T - T.peripheralWeightedProjection) z := by
        exact transferMatrixFin_hasEigenvalue_iff
          (T - T.peripheralWeightedProjection) z
      _ ↔ z = 0 ∨ z ∈ T.subperipheralSpectrum :=
        hPos.hasEigenvalue_sub_peripheralWeightedProjection_iff hTP z
  refine ⟨U, Λ, N, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.isDiag_diagonal _
  · intro i j hij
    by_cases hEq : i = j
    · subst j
      simp [N, Λ]
    · have hji : j < i := by omega
      simp [N, Λ, hR_upper hji, hEq]
  · change A = _
    calc
      A = (U : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) * R *
          (U : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)ᴴ := hA
      _ = (U : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) * (Λ + N) *
          (U : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)ᴴ := by
        rw [show Λ + N = R by simp [N]]
  · exact hΛ_spectrum
  · apply le_antisymm
    · change ‖Matrix.diagonal (Matrix.diag R)‖ ≤ T.subperipheralModulus
      rw [Matrix.l2_opNorm_diagonal]
      refine (pi_norm_le_iff_of_nonneg T.subperipheralModulus_nonneg).mpr ?_
      intro i
      change ‖R i i‖ ≤ T.subperipheralModulus
      have hi := (hΛ_spectrum (R i i)).mp ⟨i, by simp [Λ]⟩
      rcases hi with hi | hi
      · rw [hi, norm_zero]
        exact T.subperipheralModulus_nonneg
      · exact T.norm_le_subperipheralModulus hi
    · by_cases hsub : T.subperipheralSpectrum.Nonempty
      · obtain ⟨z, hz, hzNorm⟩ := T.exists_norm_eq_subperipheralModulus hsub
        obtain ⟨i, hi⟩ := (hΛ_spectrum z).mpr (Or.inr hz)
        have hi_le : ‖Λ i i‖ ≤ ‖Λ‖ := by
          have hbase : ‖R i i‖ ≤ ‖Matrix.diagonal (Matrix.diag R)‖ := by
            rw [Matrix.l2_opNorm_diagonal]
            exact norm_le_pi_norm (Matrix.diag R) i
          simpa only [Λ, Matrix.diagonal_apply_eq, Matrix.diag_apply] using hbase
        calc
          T.subperipheralModulus = ‖z‖ := hzNorm.symm
          _ = ‖Λ i i‖ := by rw [hi]
          _ ≤ ‖Λ‖ := hi_le
      · rw [T.subperipheralModulus_eq_zero_of_empty
          (Set.not_nonempty_iff_eq_empty.mp hsub)]
        exact norm_nonneg Λ
