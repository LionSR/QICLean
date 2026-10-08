/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Irreducible.FromSpectral

/-!
# Wolf Theorem 6.4: spectral characterization of irreducibility

This module proves that, for a nonzero positive map `T` on a nonzero full
matrix algebra, Wolf Theorem 6.4 characterizes irreducibility by three
spectral facts: the spectral radius is an ordinary nondegenerate eigenvalue,
and it has positive-definite right and left eigenvectors.  The left eigenvector
is stated for
`Matrix.traceAdjointMap T`, the adjoint with respect to Wolf's bilinear trace
pairing.

The reverse implication follows Wolf's proof.  If `Y > 0` is the left Perron
eigenvector and `S = sqrt Y`, then

`T' = r⁻¹ • similarityMap S⁻¹ T`

is positive and trace preserving, and `S * X * S > 0` is fixed by `T'`.  A
proper invariant corner for `T'` contains a stationary density matrix.  Pulling
that matrix back through the similarity gives a second vector in the ordinary
`r`-eigenspace of `T`, contradicting its dimension one.

The hypothesis `T ≠ 0` is a necessary boundary correction to the printed
statement: on `M₁(ℂ)`, the zero map is irreducible, but its spectral radius is
zero and hence it cannot satisfy the printed strict-positive condition
`T(X) = r X > 0`.

## Main declarations

* `HasWolfSpectralProperties`: the exact source-facing spectral condition.
* `hasWolfSpectralProperties_of_irreducible_positive`: the forward implication.
* `isIrreducibleMap_of_hasWolfSpectralProperties`: the reverse implication.
* `wolf_theorem_6_4`: Wolf Theorem 6.4 with the necessary nonzero-map boundary.
* `hasSpectralProperties_iff_hasWolfSpectralProperties_of_cp`: comparison with
  the earlier finite-Kraus package.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.4; local
  source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 698--721.
-/

open scoped Matrix MatrixOrder ComplexOrder NNReal ENNReal TNOperatorSpace
open Matrix

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A witness for the spectral condition in Wolf Theorem 6.4.

The real number `r` represents the spectral radius through
`spectralRadius_eq`.  The field `finrank_eigenspace_eq_one` is ordinary
geometric nondegeneracy over `ℂ`; it is not restricted to positive
semidefinite eigenvectors and makes no assertion about algebraic multiplicity.
The left eigenvector is expressed through the trace-pairing adjoint, without a
Kraus or complete-positivity hypothesis. -/
structure WolfSpectralProperties (T : Mat →ₗ[ℂ] Mat) where
  r : ℝ
  r_pos : 0 < r
  spectralRadius_eq :
    spectralRadius ℂ ((Module.End.toContinuousLinearMap Mat) T) = ENNReal.ofReal r
  X : Mat
  X_posDef : X.PosDef
  right_eigenvector : T X = (r : ℂ) • X
  Y : Mat
  Y_posDef : Y.PosDef
  left_eigenvector : Matrix.traceAdjointMap T Y = (r : ℂ) • Y
  finrank_eigenspace_eq_one :
    Module.finrank ℂ (Module.End.eigenspace T (r : ℂ)) = 1

/-- `HasWolfSpectralProperties T` asserts the existence of the right and left
Perron data in `WolfSpectralProperties T`. -/
def HasWolfSpectralProperties (T : Mat →ₗ[ℂ] Mat) : Prop :=
  Nonempty (WolfSpectralProperties T)

/-- Wolf Theorem 6.4, forward implication, for an arbitrary nonzero positive
map.  Wolf Theorem 6.3 supplies the ordinary simple right Perron eigenspace;
its trace-adjoint consequence supplies a positive-definite left eigenvector at
the same eigenvalue. -/
theorem hasWolfSpectralProperties_of_irreducible_positive [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    (hIrr : IsIrreducibleMap T) (hT_ne : T ≠ 0) :
    HasWolfSpectralProperties T := by
  obtain ⟨X, r, _hXdensity, hr, hX, hX_eig, _hLowerAtX, _hUpperAtX,
      _hLowerMax, _hUpperMin, hfinrank, _hpositive_eigenvalue, hradius⟩ :=
    exists_wolfTheorem63_of_irreducible_positive_of_ne_zero T hT hIrr hT_ne
  obtain ⟨Y, hY, hY_eig⟩ :=
    exists_posDef_traceAdjointMap_eigenvector_at_perron T hT hIrr hr hX hX_eig
  exact ⟨
    { r := r
      r_pos := hr
      spectralRadius_eq := hradius
      X := X
      X_posDef := hX
      right_eigenvector := hX_eig
      Y := Y
      Y_posDef := hY
      left_eigenvector := hY_eig
      finrank_eigenspace_eq_one := hfinrank }⟩

/-- If an eigenspace has dimension one and contains the nonzero vector `X`,
then every eigenvector in it is a scalar multiple of `X`. -/
private theorem eigenvector_eq_smul_of_finrank_eigenspace_eq_one
    {T : Mat →ₗ[ℂ] Mat} {r : ℝ} {X Z : Mat}
    (hX_ne : X ≠ 0) (hX_eig : T X = (r : ℂ) • X)
    (hfinrank : Module.finrank ℂ (Module.End.eigenspace T (r : ℂ)) = 1)
    (hZ_eig : T Z = (r : ℂ) • Z) :
    ∃ c : ℂ, Z = c • X := by
  let x : Module.End.eigenspace T (r : ℂ) :=
    ⟨X, Module.End.mem_eigenspace_iff.mpr hX_eig⟩
  have hx_ne : x ≠ 0 := by
    intro hx
    apply hX_ne
    exact congrArg Subtype.val hx
  let z : Module.End.eigenspace T (r : ℂ) :=
    ⟨Z, Module.End.mem_eigenspace_iff.mpr hZ_eig⟩
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' x hx_ne).mp hfinrank z
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

/-- Wolf Theorem 6.4, reverse implication, for an arbitrary positive map.

The proof is the similarity and invariant-corner proof at source lines
712--720.  No Kraus representation or complete positivity is used. -/
theorem isIrreducibleMap_of_hasWolfSpectralProperties [NeZero D]
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T)
    (hSpec : HasWolfSpectralProperties T) :
    IsIrreducibleMap T := by
  rcases hSpec with ⟨hSpec⟩
  let S : Mat := CFC.sqrt hSpec.Y
  have hS_herm : Sᴴ = S := by
    simpa [S] using Matrix.conjTranspose_cfc_sqrt (ρ := hSpec.Y)
  have hS_det : IsUnit S.det := by
    simpa [S] using hSpec.Y_posDef.isUnit_det_cfc_sqrt
  have hS_inv_mul : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hS_det
  have hS_mul_inv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hS_det
  have hS_unit : IsUnit S := by
    simpa [S] using
      (CFC.isUnit_sqrt_iff hSpec.Y hSpec.Y_posDef.posSemidef.nonneg).2
        (Matrix.PosDef.isUnit hSpec.Y_posDef)
  have hS_inv_inv : S⁻¹⁻¹ = S := by
    let := hS_unit.invertible
    exact Matrix.inv_inv_of_invertible S
  have hS_inv_herm : (S⁻¹)ᴴ = S⁻¹ := by
    simpa [hS_herm] using Matrix.conjTranspose_nonsing_inv S
  have hS_sq : S * S = hSpec.Y := by
    exact CFC.sqrt_mul_sqrt_self hSpec.Y hSpec.Y_posDef.posSemidef.nonneg
  have hr_complex : (hSpec.r : ℂ) ≠ 0 := by
    exact_mod_cast hSpec.r_pos.ne'
  let T' : Mat →ₗ[ℂ] Mat :=
    (hSpec.r : ℂ)⁻¹ • similarityMap (D := D) S⁻¹ T
  have hT'_pos : IsPositiveMap T' := by
    intro A hA
    have hsim := hT.similarityMap S⁻¹ A hA
    have hr_inv_nonneg : (0 : ℂ) ≤ (hSpec.r : ℂ)⁻¹ :=
      inv_nonneg.mpr (by exact_mod_cast hSpec.r_pos.le)
    simpa only [T', LinearMap.smul_apply] using hsim.smul hr_inv_nonneg
  have hT'_tp : IsTracePreservingMap T' := by
    intro A
    let Z : Mat := S⁻¹ * A * S⁻¹
    calc
      Matrix.trace (T' A) =
          (hSpec.r : ℂ)⁻¹ * Matrix.trace (S * T Z * S) := by
        simp [T', similarityMap, Z, hS_inv_inv, hS_inv_herm]
      _ = (hSpec.r : ℂ)⁻¹ * Matrix.trace (hSpec.Y * T Z) := by
        rw [← hS_sq]
        congr 1
        exact Matrix.trace_mul_cycle S (T Z) S
      _ = (hSpec.r : ℂ)⁻¹ *
          Matrix.trace (Matrix.traceAdjointMap T hSpec.Y * Z) := by
        rw [Matrix.trace_traceAdjointMap_mul]
      _ = (hSpec.r : ℂ)⁻¹ *
          Matrix.trace (((hSpec.r : ℂ) • hSpec.Y) * Z) := by
        rw [hSpec.left_eigenvector]
      _ = (hSpec.r : ℂ)⁻¹ *
          ((hSpec.r : ℂ) * Matrix.trace (hSpec.Y * Z)) := by
        rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      _ = Matrix.trace (hSpec.Y * Z) := by
        rw [← mul_assoc, inv_mul_cancel₀ hr_complex, one_mul]
      _ = Matrix.trace A := by
        rw [← hS_sq]
        change Matrix.trace ((S * S) * (S⁻¹ * A * S⁻¹)) = Matrix.trace A
        rw [show (S * S) * (S⁻¹ * A * S⁻¹) = S * A * S⁻¹ by
          calc
            (S * S) * (S⁻¹ * A * S⁻¹) = S * ((S * S⁻¹) * A) * S⁻¹ := by
              simp only [Matrix.mul_assoc]
            _ = S * A * S⁻¹ := by rw [hS_mul_inv, Matrix.one_mul]]
        rw [Matrix.trace_mul_cycle S A S⁻¹, hS_inv_mul, Matrix.one_mul]
  have hS_vecMul_inj : Function.Injective fun v : Fin D → ℂ => Matrix.vecMul v S := by
    intro v w hvw
    have h' := congrArg (fun x => Matrix.vecMul x S⁻¹) hvw
    simpa [Matrix.vecMul_vecMul, hS_mul_inv] using h'
  let X' : Mat := S * hSpec.X * S
  have hX'_pd : X'.PosDef := by
    simpa [X', hS_herm] using
      hSpec.X_posDef.mul_mul_conjTranspose_same hS_vecMul_inj
  have hX'_fix : T' X' = X' := by
    calc
      T' X' = (hSpec.r : ℂ)⁻¹ •
          (S * T (((S⁻¹ * S) * hSpec.X) * (S * S⁻¹)) * S) := by
        simp [T', X', similarityMap, hS_inv_inv, hS_inv_herm, Matrix.mul_assoc]
      _ = (hSpec.r : ℂ)⁻¹ • (S * T hSpec.X * S) := by
        rw [hS_inv_mul, Matrix.one_mul, hS_mul_inv, Matrix.mul_one]
      _ = (hSpec.r : ℂ)⁻¹ •
          (S * ((hSpec.r : ℂ) • hSpec.X) * S) := by
        rw [hSpec.right_eigenvector]
      _ = X' := by
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul,
          inv_mul_cancel₀ hr_complex, one_smul]
  have huniq : ∀ τ : Mat, τ.PosSemidef → T' τ = τ →
      ∃ c : ℂ, τ = c • X' := by
    intro τ _hτ hτ_fix
    let Z : Mat := S⁻¹ * τ * S⁻¹
    have hZ_eig : T Z = (hSpec.r : ℂ) • Z := by
      have hscaled' :
          S⁻¹ * T' τ * S⁻¹ = (hSpec.r : ℂ)⁻¹ • T Z := by
        calc
          S⁻¹ * T' τ * S⁻¹ =
              S⁻¹ * ((hSpec.r : ℂ)⁻¹ • (S * T Z * S)) * S⁻¹ := by
            simp [T', Z, similarityMap, hS_inv_inv, hS_inv_herm,
              Matrix.mul_assoc]
          _ = (hSpec.r : ℂ)⁻¹ •
              ((S⁻¹ * S) * T Z * (S * S⁻¹)) := by
            simp [Matrix.mul_assoc]
          _ = (hSpec.r : ℂ)⁻¹ • T Z := by
            rw [hS_inv_mul, Matrix.one_mul, hS_mul_inv, Matrix.mul_one]
      have hscaled :
          (hSpec.r : ℂ)⁻¹ • T Z = Z := by
        rw [← hscaled', hτ_fix]
      have h := congrArg (fun M => (hSpec.r : ℂ) • M) hscaled
      simpa [smul_smul, hr_complex, Matrix.mul_assoc] using h
    have hX_ne : hSpec.X ≠ 0 := hSpec.X_posDef.isUnit.ne_zero
    obtain ⟨c, hc⟩ :=
      eigenvector_eq_smul_of_finrank_eigenspace_eq_one hX_ne
        hSpec.right_eigenvector hSpec.finrank_eigenspace_eq_one hZ_eig
    refine ⟨c, ?_⟩
    calc
      τ = (S * S⁻¹) * τ * (S⁻¹ * S) := by
        rw [hS_mul_inv, Matrix.one_mul, hS_inv_mul, Matrix.mul_one]
      _ = S * Z * S := by simp [Z, Matrix.mul_assoc]
      _ = S * (c • hSpec.X) * S := by rw [hc]
      _ = c • X' := by simp [X', Matrix.mul_assoc]
  have hT'_irr : IsIrreducibleMap T' :=
    isIrreducibleMap_of_positive_tracePreserving_posDef_fixedPoint_unique
      T' hT'_pos hT'_tp X' hX'_pd hX'_fix huniq
  have hsimilarity_irr : IsIrreducibleMap (similarityMap (D := D) S⁻¹ T) := by
    have hscaled := isIrreducibleMap_smul hr_complex hT'_irr
    simpa [T', smul_smul, hr_complex] using hscaled
  have hS_inv_det : (S⁻¹).det ≠ 0 := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hS_det.ne_zero
  exact (isIrreducibleMap_similarity_iff (D := D) hS_inv_det).mp hsimilarity_irr

/-- **Wolf Theorem 6.4**, with the necessary zero-map boundary correction.

Let `T` be a nonzero positive map on `M_D(ℂ)`, with `D > 0`.  Then `T` is
irreducible if and only if its spectral radius is an ordinary nondegenerate
eigenvalue having positive-definite right and trace-adjoint left eigenvectors.
No Kraus representation or complete positivity is assumed. -/
theorem wolf_theorem_6_4 [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hT_ne : T ≠ 0) :
    IsIrreducibleMap T ↔ HasWolfSpectralProperties T := by
  constructor
  · exact fun hIrr =>
      hasWolfSpectralProperties_of_irreducible_positive T hT hIrr hT_ne
  · exact isIrreducibleMap_of_hasWolfSpectralProperties hT

/-- The source-general spectral package specializes to the earlier finite-Kraus
package: for a nonzero completely positive map, the two packages are
equivalent.  The forward direction uses ordinary eigenspace simplicity to
obtain the older PSD uniqueness clause; the reverse direction recovers
irreducibility from that clause and then applies the source-general theorem. -/
theorem hasSpectralProperties_iff_hasWolfSpectralProperties_of_cp [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hCP : IsCPMap T) (hT_ne : T ≠ 0) :
    HasSpectralProperties (D := D) T ↔ HasWolfSpectralProperties T := by
  constructor
  · intro hRestricted
    have hIrr : IsIrreducibleMap T :=
      isIrreducibleMap_of_hasSpectralProperties hRestricted
    exact hasWolfSpectralProperties_of_irreducible_positive
      T hCP.isPositiveMap hIrr hT_ne
  · intro hWolf
    have hIrr : IsIrreducibleMap T :=
      isIrreducibleMap_of_hasWolfSpectralProperties hCP.isPositiveMap hWolf
    exact hasSpectralProperties_of_irreducible_cp T hCP hIrr hT_ne

end
