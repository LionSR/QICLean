/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.UnitarySchurTriangularization
import QICLean.Analysis.UpperTriangularBound
import QICLean.Algebra.HermitianHelpers
import QICLean.Analysis.TraceNormContractivity
import QICLean.Analysis.TraceNormFrobenius
import QICLean.Channel.Determinant.Bound
import QICLean.Channel.FixedPoint.StationaryStates
import QICLean.Channel.Peripheral.CesaroRecurrence
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
right-hand side is the identity.  The channel estimates below use this
identity only for positive powers and treat the remaining `D = 1`, `n = 0`
boundary directly.

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8,
Theorem "Asymptotic convergence II", Equation (8.111); local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1295--1316.
-/

noncomputable section

open Matrix

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

/-- Canonical coordinate relabelling commutes with powers of transfer
matrices. -/
theorem transferMatrixFin_pow
    (T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (n : ℕ) :
    transferMatrixFin T ^ n =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (transferMatrix T ^ n) := by
  exact (map_pow (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv)
    (transferMatrix T) n).symm

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

section L2Reindex

open scoped Matrix.Norms.L2Operator

/-- Simultaneously relabelling the rows and columns through an equivalence
does not increase the `L²` operator norm. -/
theorem Matrix.l2_opNorm_reindex_le_equiv
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m ℂ) :
    ‖Matrix.reindex e e A‖ ≤ ‖A‖ := by
  classical
  apply Matrix.l2_opNorm_le_of_forall (norm_nonneg A)
  intro v
  let w : m → ℂ := fun i ↦ v (e i)
  have hmul : Matrix.reindex e e A *ᵥ v =
      fun j ↦ (A *ᵥ w) (e.symm j) := by
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, w]
    rw [← e.sum_comp]
    simp
  have hnorm_reindex (u : m → ℂ) :
      ‖(EuclideanSpace.equiv n ℂ).symm (fun j ↦ u (e.symm j))‖ =
        ‖(EuclideanSpace.equiv m ℂ).symm u‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simpa using (e.sum_comp (fun j ↦ ‖u (e.symm j)‖ ^ 2)).symm
  have hw_norm : ‖(EuclideanSpace.equiv m ℂ).symm w‖ =
      ‖(EuclideanSpace.equiv n ℂ).symm v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simpa [w] using (e.sum_comp (fun j ↦ ‖v j‖ ^ 2))
  rw [hmul, hnorm_reindex, ← hw_norm]
  exact A.l2_opNorm_mulVec ((EuclideanSpace.equiv m ℂ).symm w)

/-- Simultaneously relabelling the rows and columns through an equivalence
preserves the `L²` operator norm. -/
theorem Matrix.l2_opNorm_reindex_equiv
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m ℂ) :
    ‖Matrix.reindex e e A‖ = ‖A‖ := by
  apply le_antisymm (Matrix.l2_opNorm_reindex_le_equiv e A)
  have hback := Matrix.l2_opNorm_reindex_le_equiv e.symm (Matrix.reindex e e A)
  simpa [Matrix.reindex_apply] using hback

end L2Reindex

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

/-! ### Hilbert--Schmidt norm bound for positive channels -/

section FrobeniusNorm

open scoped InnerProductSpace RealInnerProductSpace Matrix.Norms.Frobenius

private theorem real_inner_frobenius_eq_complex_re
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    inner ℝ (frobeniusEquivEuclidean (Fin D) (Fin D) X)
        (frobeniusEquivEuclidean (Fin D) (Fin D) Y) =
      (inner ℂ (frobeniusEquivEuclidean (Fin D) (Fin D) X)
        (frobeniusEquivEuclidean (Fin D) (Fin D) Y)).re := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Complex.inner]

private theorem frobenius_norm_sq_add_smul_I_of_isHermitian
    {H K : Matrix (Fin D) (Fin D) ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    ‖H + Complex.I • K‖ ^ 2 = ‖H‖ ^ 2 + ‖K‖ ^ 2 := by
  have htrace_im : (Matrix.trace (H * K)).im = 0 := by
    apply (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
    rw [isSelfAdjoint_iff, ← Matrix.trace_conjTranspose,
      Matrix.conjTranspose_mul, hH.eq, hK.eq, Matrix.trace_mul_comm]
  have horth : inner ℝ (frobeniusEquivEuclidean (Fin D) (Fin D) H)
      (frobeniusEquivEuclidean (Fin D) (Fin D) (Complex.I • K)) = 0 := by
    rw [real_inner_frobenius_eq_complex_re,
      Matrix.inner_frobeniusEquivEuclidean, hH.eq, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul, Complex.mul_re, htrace_im]
    norm_num
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  calc
    ‖H + Complex.I • K‖ ^ 2 =
        ‖frobeniusEquivEuclidean (Fin D) (Fin D) (H + Complex.I • K)‖ ^ 2 := by
      rw [LinearIsometryEquiv.norm_map]
    _ = ‖frobeniusEquivEuclidean (Fin D) (Fin D) H +
          frobeniusEquivEuclidean (Fin D) (Fin D) (Complex.I • K)‖ ^ 2 := by
      rw [map_add]
    _ = ‖frobeniusEquivEuclidean (Fin D) (Fin D) H‖ ^ 2 +
          ‖frobeniusEquivEuclidean (Fin D) (Fin D) (Complex.I • K)‖ ^ 2 := by
      simpa only [pow_two] using hpyth
    _ = ‖H‖ ^ 2 + ‖K‖ ^ 2 := by
      rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, norm_smul,
        Complex.norm_I, one_mul]

private theorem frobenius_norm_map_le_sqrt_dim_of_isHermitian
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    {H : Matrix (Fin D) (Fin D) ℂ} (hH : H.IsHermitian) :
    ‖T H‖ ≤ Real.sqrt D * ‖H‖ := by
  calc
    ‖T H‖ ≤ Matrix.traceNorm (T H) :=
      Matrix.frobenius_norm_le_traceNorm (T H)
    _ ≤ Matrix.traceNorm H :=
      Matrix.traceNorm_map_le_of_positive_of_tracePreserving hPos hTP hH
    _ ≤ Real.sqrt D * ‖H‖ :=
      Matrix.traceNorm_le_sqrt_dim_mul_frobenius_norm H

/-- A positive trace-preserving map on `D × D` matrices has induced
Hilbert--Schmidt norm at most `√D`.

The proof first establishes the bound on Hermitian matrices from trace-norm
contractivity, and then uses the orthogonal decomposition `X = H + iK`.
This is the singular-value estimate used by Wolf immediately before Equation
(8.111), local source lines 1314--1316. -/
theorem IsPositiveMap.hilbertSchmidtOperatorNorm_le_sqrt_dim
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    Matrix.hilbertSchmidtOperatorNorm T ≤ Real.sqrt D := by
  rw [Matrix.hilbertSchmidtOperatorNorm]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg D)
  intro x
  obtain ⟨X, rfl⟩ :=
    (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).surjective x
  simp only [LinearMap.coe_toContinuousLinearMap',
    Matrix.frobeniusEuclideanMap_apply, LinearIsometryEquiv.norm_map]
  obtain ⟨H, K, hH, hK, rfl⟩ :=
    Matrix.exists_isHermitian_eq_add_smul_I X
  rw [map_add, map_smul]
  have hTH : (T H).IsHermitian := Matrix.isHermitian_map_of_positive hPos hH
  have hTK : (T K).IsHermitian := Matrix.isHermitian_map_of_positive hPos hK
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg D) (norm_nonneg _))).mp
  rw [frobenius_norm_sq_add_smul_I_of_isHermitian hTH hTK,
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg D),
    frobenius_norm_sq_add_smul_I_of_isHermitian hH hK]
  have hH_bound := frobenius_norm_map_le_sqrt_dim_of_isHermitian hPos hTP hH
  have hK_bound := frobenius_norm_map_le_sqrt_dim_of_isHermitian hPos hTP hK
  nlinarith [norm_nonneg (T H), norm_nonneg (T K), norm_nonneg H, norm_nonneg K,
    Real.sqrt_nonneg (D : ℝ), Real.sq_sqrt (Nat.cast_nonneg D)]

end FrobeniusNorm

open scoped Matrix.Norms.L2Operator

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

/-- Wolf's Schur data with the source-order nilpotent-part estimate
`‖N‖ ≤ μ + 2 √D`.

The two `√D` terms bound the Hilbert--Schmidt operator norms of `T` and
`T_ϕ = T T_φ`, respectively.  Positivity and trace preservation of the
phase-weighted map follow from those of `T`; complete positivity is not used.

Source: Wolf, Chapter 8, proof of Equation (8.111), local source lines
1314--1316. -/
theorem IsPositiveMap.exists_wolf_eq_111_schur_data_with_bound
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
      ‖Λ‖ = T.subperipheralModulus ∧
      ‖N‖ ≤ T.subperipheralModulus + 2 * Real.sqrt D := by
  obtain ⟨U, Λ, N, hΛDiag, hNUpper, hform, hΛspectrum, hΛnorm⟩ :=
    hPos.exists_wolf_eq_111_schur_data hTP
  refine ⟨U, Λ, N, hΛDiag, hNUpper, hform, hΛspectrum, hΛnorm, ?_⟩
  have hWPos : IsPositiveMap T.peripheralWeightedProjection :=
    hPos.peripheralWeightedProjection_isPositiveMap hTP
  have hWTP : IsTracePreservingMap T.peripheralWeightedProjection :=
    hPos.peripheralWeightedProjection_isTracePreservingMap hTP
  have hA_bound :
      ‖transferMatrixFin (T - T.peripheralWeightedProjection)‖ ≤
        2 * Real.sqrt D := by
    calc
      ‖transferMatrixFin (T - T.peripheralWeightedProjection)‖ =
          ‖transferMatrix (T - T.peripheralWeightedProjection)‖ := by
        rw [transferMatrixFin, Matrix.l2_opNorm_reindex_equiv]
      _ = ‖transferMatrix T -
          transferMatrix T.peripheralWeightedProjection‖ := by
        rw [show transferMatrix (T - T.peripheralWeightedProjection) =
            transferMatrix T - transferMatrix T.peripheralWeightedProjection from
          (transferMatrixLM (D := D)).map_sub T T.peripheralWeightedProjection]
      _ ≤ ‖transferMatrix T‖ +
          ‖transferMatrix T.peripheralWeightedProjection‖ := norm_sub_le _ _
      _ = Matrix.hilbertSchmidtOperatorNorm T +
          Matrix.hilbertSchmidtOperatorNorm T.peripheralWeightedProjection := by
        rw [l2_opNorm_transferMatrix_eq_hilbertSchmidtOperatorNorm,
          l2_opNorm_transferMatrix_eq_hilbertSchmidtOperatorNorm]
      _ ≤ Real.sqrt D + Real.sqrt D :=
        add_le_add (hPos.hilbertSchmidtOperatorNorm_le_sqrt_dim hTP)
          (hWPos.hilbertSchmidtOperatorNorm_le_sqrt_dim hWTP)
      _ = 2 * Real.sqrt D := by ring
  have hform_norm :
      ‖transferMatrixFin (T - T.peripheralWeightedProjection)‖ = ‖Λ + N‖ := by
    rw [hform, ← Matrix.star_eq_conjTranspose, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  calc
    ‖N‖ = ‖(Λ + N) - Λ‖ := by rw [add_sub_cancel_left]
    _ ≤ ‖Λ + N‖ + ‖Λ‖ := norm_sub_le _ _
    _ = ‖transferMatrixFin (T - T.peripheralWeightedProjection)‖ +
        T.subperipheralModulus := by rw [hform_norm, hΛnorm]
    _ ≤ 2 * Real.sqrt D + T.subperipheralModulus :=
      by simpa [add_comm] using add_le_add_right hA_bound T.subperipheralModulus
    _ = T.subperipheralModulus + 2 * Real.sqrt D := by ring

/-! ### Channel-level Equation (8.111) -/

/-- **Wolf Equation (8.111), channel-level coarse estimate.**

For a positive trace-preserving map, this constructs the Schur data of
`T - T_ϕ`, identifies the diagonal norm with the common subperipheral
modulus `μ`, bounds the strictly upper-triangular part by `μ + 2 √D`,
and proves the coarse power estimate.

The natural exponent is restricted to the range in which Wolf's exponent
`n - D² + 1` is nonnegative.  For `n > 0`, the proof uses
`Tⁿ - T_ϕⁿ = (T - T_ϕ)ⁿ`; the sole permitted zero-power case is
`D = 1`, `n = 0`, where the final inequality is proved directly.  No division
by `μ` is used, so `μ = 0` is included; at the boundary `n = D² - 1`,
Lean's convention `0 ^ 0 = 1` gives the natural-power form of the estimate.

Source: Wolf, Chapter 8, Theorem "Asymptotic convergence II", Equation
(8.111), local source lines 1299--1316. -/
theorem IsPositiveMap.exists_wolf_eq_111
    [NeZero D] {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    {n : ℕ} (hn_ge : D * D - 1 ≤ n) :
    ∃ (U : Matrix.unitaryGroup (Fin (D * D)) ℂ)
        (Λ N : Matrix (Fin (D * D)) (Fin (D * D)) ℂ),
      IsDiag Λ ∧ IsStrictlyUpperTriangular N ∧
      transferMatrixFin (T - T.peripheralWeightedProjection) =
        (U : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) * (Λ + N) *
          (U : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)ᴴ ∧
      (∀ z : ℂ, (∃ i : Fin (D * D), Λ i i = z) ↔
        z = 0 ∨ z ∈ T.subperipheralSpectrum) ∧
      ‖Λ‖ = T.subperipheralModulus ∧
      ‖N‖ ≤ T.subperipheralModulus + 2 * Real.sqrt D ∧
      ‖transferMatrix T ^ n -
          transferMatrix T.peripheralWeightedProjection ^ n‖ ≤
        T.subperipheralModulus ^ n +
          (((D * D - 1 : ℕ) * n ^ (D * D - 1 : ℕ) : ℕ) : ℝ) *
            T.subperipheralModulus ^ (n - (D * D - 1)) *
              max ‖N‖ (‖N‖ ^ (D * D - 1)) := by
  obtain ⟨U, Λ, N, hΛDiag, hNUpper, hform, hΛspectrum, hΛnorm, hNnorm⟩ :=
    hPos.exists_wolf_eq_111_schur_data_with_bound hTP
  refine ⟨U, Λ, N, hΛDiag, hNUpper, hform, hΛspectrum, hΛnorm, hNnorm, ?_⟩
  by_cases hn0 : n = 0
  · subst n
    have hdim : D * D - 1 = 0 := Nat.eq_zero_of_le_zero hn_ge
    simp [hdim]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hD2 : D * D ≠ 0 := mul_ne_zero (NeZero.ne D) (NeZero.ne D)
    let _ : Nonempty (Fin (D * D)) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hD2)
    have hschur := Matrix.wolf_eq_111_schur_form hΛDiag hNUpper hD2 hn_ge
      hΛnorm T.subperipheralModulus_le_one
    rw [transferMatrix_pow_sub_peripheralWeightedProjection_pow T hn]
    calc
      ‖transferMatrix (T - T.peripheralWeightedProjection) ^ n‖ =
          ‖transferMatrixFin (T - T.peripheralWeightedProjection) ^ n‖ := by
        rw [transferMatrixFin_pow, Matrix.l2_opNorm_reindex_equiv]
      _ = ‖(Λ + N) ^ n‖ := by
        have hconj : transferMatrixFin (T - T.peripheralWeightedProjection) =
            Unitary.conjStarAlgAut ℂ
              (Matrix (Fin (D * D)) (Fin (D * D)) ℂ) U (Λ + N) := by
          simpa only [Unitary.conjStarAlgAut_apply,
            Matrix.star_eq_conjTranspose] using hform
        rw [hconj, ← map_pow, Unitary.conjStarAlgAut_apply,
          ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
          CStarRing.norm_coe_unitary_mul]
      _ ≤ _ := hschur

/-- **Wolf Equation (8.111), channel-level refined estimate.**

Under `2 (D² - 1) ≤ n`, the factor `n ^ (D² - 1)` in the coarse
estimate is replaced by `Nat.choose n (D² - 1)`.  The `D = 1`, `n = 0`
boundary is discharged directly; positive powers use the nonperipheral power
identity.  The proof uses only natural powers and therefore also includes
`μ = 0` without division.

Source: Wolf, Chapter 8, Theorem "Asymptotic convergence II", Equation
(8.111), local source lines 1299--1316. -/
theorem IsPositiveMap.exists_wolf_eq_111_refined
    [NeZero D] {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    {n : ℕ} (hn_ge : 2 * (D * D - 1) ≤ n) :
    ∃ (U : Matrix.unitaryGroup (Fin (D * D)) ℂ)
        (Λ N : Matrix (Fin (D * D)) (Fin (D * D)) ℂ),
      IsDiag Λ ∧ IsStrictlyUpperTriangular N ∧
      transferMatrixFin (T - T.peripheralWeightedProjection) =
        (U : Matrix (Fin (D * D)) (Fin (D * D)) ℂ) * (Λ + N) *
          (U : Matrix (Fin (D * D)) (Fin (D * D)) ℂ)ᴴ ∧
      (∀ z : ℂ, (∃ i : Fin (D * D), Λ i i = z) ↔
        z = 0 ∨ z ∈ T.subperipheralSpectrum) ∧
      ‖Λ‖ = T.subperipheralModulus ∧
      ‖N‖ ≤ T.subperipheralModulus + 2 * Real.sqrt D ∧
      ‖transferMatrix T ^ n -
          transferMatrix T.peripheralWeightedProjection ^ n‖ ≤
        T.subperipheralModulus ^ n +
          (((D * D - 1 : ℕ) * Nat.choose n (D * D - 1) : ℕ) : ℝ) *
            T.subperipheralModulus ^ (n - (D * D - 1)) *
              max ‖N‖ (‖N‖ ^ (D * D - 1)) := by
  obtain ⟨U, Λ, N, hΛDiag, hNUpper, hform, hΛspectrum, hΛnorm, hNnorm⟩ :=
    hPos.exists_wolf_eq_111_schur_data_with_bound hTP
  refine ⟨U, Λ, N, hΛDiag, hNUpper, hform, hΛspectrum, hΛnorm, hNnorm, ?_⟩
  by_cases hn0 : n = 0
  · subst n
    have hdim : D * D - 1 = 0 := by omega
    simp [hdim]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hD2 : D * D ≠ 0 := mul_ne_zero (NeZero.ne D) (NeZero.ne D)
    let _ : Nonempty (Fin (D * D)) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hD2)
    have hschur := Matrix.wolf_eq_111_schur_form_refined hΛDiag hNUpper hD2 hn_ge
      hΛnorm T.subperipheralModulus_le_one
    rw [transferMatrix_pow_sub_peripheralWeightedProjection_pow T hn]
    calc
      ‖transferMatrix (T - T.peripheralWeightedProjection) ^ n‖ =
          ‖transferMatrixFin (T - T.peripheralWeightedProjection) ^ n‖ := by
        rw [transferMatrixFin_pow, Matrix.l2_opNorm_reindex_equiv]
      _ = ‖(Λ + N) ^ n‖ := by
        have hconj : transferMatrixFin (T - T.peripheralWeightedProjection) =
            Unitary.conjStarAlgAut ℂ
              (Matrix (Fin (D * D)) (Fin (D * D)) ℂ) U (Λ + N) := by
          simpa only [Unitary.conjStarAlgAut_apply,
            Matrix.star_eq_conjTranspose] using hform
        rw [hconj, ← map_pow, Unitary.conjStarAlgAut_apply,
          ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
          CStarRing.norm_coe_unitary_mul]
      _ ≤ _ := hschur
