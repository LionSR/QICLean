/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixCongruence
import QICLean.Algebra.MatrixOperatorSpace
import QICLean.Analysis.SpectralRadius
import QICLean.Channel.Irreducible.CollatzWielandt
import QICLean.Channel.Irreducible.Similarity
import QICLean.Channel.Peripheral.Conjugation
import QICLean.Channel.Peripheral.SpectralRadius
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Irreducible spectral-radius identity (Wolf Theorem 6.3(4))

This module proves Wolf's Perron–Frobenius theorem for irreducible positive
maps on `M_D(ℂ)`, and retains the earlier completely-positive interface as a
specialization.

## Main results

* `spectralRadius_eq_of_posDef_eigenvector_of_positive`:
  if `E ρ = r • ρ` with `ρ > 0` and `r > 0`, then the spectral radius of `E`
  is `r`.
* `exists_wolfTheorem63_of_irreducible_positive`: the corrected `r ≥ 0`
  form of all four conclusions of Wolf Theorem 6.3.
* `exists_wolfTheorem63_of_irreducible_positive_of_ne_zero`: Wolf's printed
  `r > 0` form under the necessary explicit nonzero-map hypothesis.
* `spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp`: the earlier CP
  interface, now a direct specialization.
* `spectralRadius_toReal_eq_of_posDef_eigenvector_of_irreducible_cp`:
  the same statement as a real-valued identity.
* `peripheralEigenvalues_similarityMap_eq`: peripheral eigenvalues are
  invariant under the positive-congruence similarity used for Perron gauges.
* `IsPrimitive.similarityMap_iff`: primitivity is invariant under the
  positive-congruence similarity used for Perron gauges.

## Approach

Following Wolf lines 671--680, the positive-definite Perron eigenvector is
used to conjugate and rescale the map to a positive unital map.  Wolf
Proposition 6.1 gives spectral radius one there; similarity invariance and the
scalar spectral-radius identity transport the result back.  No Kraus or
complete-positivity hypothesis enters this argument.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2, Theorem 6.3]
  [Wolf2012QChannels]
-/

open scoped Matrix MatrixOrder Pointwise ComplexOrder BigOperators NNReal ENNReal TNOperatorSpace
open Matrix Finset

variable {D : ℕ}

/-! ## Spectral radius identity (Wolf 6.3(4)) -/

section SimilarityCLM

/-- Spectral radius is invariant under the congruence similarity
`X ↦ C⁻¹ * E (C * X * Cᴴ) * (Cᴴ)⁻¹`.

Source context: arXiv:1606.00608, lines 214--235, fixes the transfer-map
spectral radius when passing to normal blocks.  The equality here is the
finite-dimensional similarity identity used to transport that normalization
through a bond-space gauge.  See also M. Wolf, *Quantum Channels & Operations:
Guided Tour*, Section 6.2, the similarity step in the proof of Theorem 6.3
[Wolf2012QChannels]. -/
theorem spectralRadius_similarityMap_eq
    (C : Matrix (Fin D) (Fin D) ℂ) (hC : C.det ≠ 0)
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (similarityMap (D := D) C E)) =
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) E) := by
  let Φ : (Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) ≃ₐ[ℂ]
      TNLean.MatrixCLM (Fin D) :=
    Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)
  have hsim_alg :
      similarityMap (D := D) C E =
        (Matrix.congruenceLinearEquiv C hC).symm.conjAlgEquiv ℂ E := by
    apply LinearMap.ext
    intro X
    ext i j
    simp [similarityMap, LinearEquiv.conjAlgEquiv_apply, Matrix.mul_assoc]
  have hspec_left :
      spectrum ℂ (Φ (similarityMap (D := D) C E)) =
        spectrum ℂ (similarityMap (D := D) C E) :=
    AlgEquiv.spectrum_eq Φ (similarityMap (D := D) C E)
  have hspec_alg :
      spectrum ℂ (similarityMap (D := D) C E) = spectrum ℂ E := by
    rw [hsim_alg]
    exact AlgEquiv.spectrum_eq
      ((Matrix.congruenceLinearEquiv C hC).symm.conjAlgEquiv ℂ) E
  have hspec_right :
      spectrum ℂ (Φ E) = spectrum ℂ E :=
    AlgEquiv.spectrum_eq Φ E
  have hspec :
      spectrum ℂ (Φ (similarityMap (D := D) C E)) = spectrum ℂ (Φ E) := by
    rw [hspec_left, hspec_alg, hspec_right]
  change spectralRadius ℂ (Φ (similarityMap (D := D) C E)) = spectralRadius ℂ (Φ E)
  rw [spectralRadius, spectralRadius, hspec]

/-- Peripheral eigenvalues are invariant under the congruence similarity
`X ↦ C⁻¹ * E (C * X * Cᴴ) * (Cᴴ)⁻¹`.

Source context: the normalization in arXiv:1708.00029, lines 313--332 uses this bond-space
similarity to pass from irreducible blocks to trace-preserving irreducible blocks without
rescaling them. The spectral invariance is the finite-dimensional similarity step in M. Wolf,
*Quantum Channels & Operations: Guided Tour*, Section 6.2, Theorem 6.3 [Wolf2012QChannels]. -/
theorem peripheralEigenvalues_similarityMap_eq
    (C : Matrix (Fin D) (Fin D) ℂ) (hC : C.det ≠ 0)
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    peripheralEigenvalues (similarityMap (D := D) C E) = peripheralEigenvalues E := by
  have hsim :
      similarityMap (D := D) C E =
        (Matrix.congruenceLinearEquiv C hC).symm.conj E := by
    apply LinearMap.ext
    intro X
    ext i j
    simp [similarityMap, LinearEquiv.conj_apply, Matrix.mul_assoc]
  rw [hsim]
  exact peripheralEigenvalues_conj (Matrix.congruenceLinearEquiv C hC).symm E

/-- Peripheral-spectrum primitivity is invariant under the positive-congruence
similarity used to change Kraus gauges. -/
theorem IsPrimitive.similarityMap_iff
    (C : Matrix (Fin D) (Fin D) ℂ) (hC : C.det ≠ 0)
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    _root_.IsPrimitive (similarityMap (D := D) C E) ↔
      _root_.IsPrimitive E := by
  have hsim :
      similarityMap (D := D) C E =
        (Matrix.congruenceLinearEquiv C hC).symm.conj E := by
    apply LinearMap.ext
    intro X
    ext i j
    simp [similarityMap, LinearEquiv.conj_apply, Matrix.mul_assoc]
  rw [hsim]
  exact IsPrimitive.conj_iff (Matrix.congruenceLinearEquiv C hC).symm E

end SimilarityCLM

/-- **Perron eigenvalue equals spectral radius for a positive map**
(Wolf Theorem 6.3(4)).

If `T X = r X` with `X > 0` and `r > 0`, conjugation by `X¹⁄²` and
rescaling by `r⁻¹` give the positive unital map
`A ↦ r⁻¹ X⁻¹⁄² T(X¹⁄² A X¹⁄²) X⁻¹⁄²`.
Wolf Proposition 6.1 gives spectral radius one for that map.  Spectral-radius
invariance under similarity and its scalar rule then give `ρ(T) = r`.

Irreducibility and complete positivity are not needed once the
positive-definite Perron pair has been supplied. -/
theorem spectralRadius_eq_of_posDef_eigenvector_of_positive
    [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsPositiveMap T)
    (X : Matrix (Fin D) (Fin D) ℂ) (r : ℝ)
    (hX : X.PosDef) (hr : 0 < r)
    (hEig : T X = (r : ℂ) • X) :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T) =
      ENNReal.ofReal r := by
  let S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt X
  have hS_herm : Sᴴ = S := by
    simpa [S] using Matrix.conjTranspose_cfc_sqrt (ρ := X)
  have hS_det : S.det ≠ 0 := by
    exact (by simpa [S] using hX.isUnit_det_cfc_sqrt.ne_zero)
  have hS_inv_mul : S⁻¹ * S = 1 :=
    Matrix.nonsing_inv_mul S (Ne.isUnit hS_det)
  have hS_mul_inv : S * S⁻¹ = 1 :=
    Matrix.mul_nonsing_inv S (Ne.isUnit hS_det)
  have hS_sq : S * S = X := by
    change CFC.sqrt X * CFC.sqrt X = X
    exact CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg
  have hr_complex : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let T' : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    (r : ℂ)⁻¹ • similarityMap (D := D) S T
  have hscale_nonneg : (0 : ℂ) ≤ (r : ℂ)⁻¹ := by
    exact inv_nonneg.mpr (by exact_mod_cast hr.le)
  have hT'_pos : IsPositiveMap T' := by
    intro A hA
    have hsim := hT.similarityMap S A hA
    simpa only [T', LinearMap.smul_apply] using hsim.smul hscale_nonneg
  have hT'_one : T' 1 = 1 := by
    change (r : ℂ)⁻¹ •
      (S⁻¹ * T (S * (1 : Matrix (Fin D) (Fin D) ℂ) * Sᴴ) * (Sᴴ)⁻¹) = 1
    rw [Matrix.mul_one, hS_herm, hS_sq, hEig]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hr_complex,
      one_smul]
    calc
      S⁻¹ * X * S⁻¹ = S⁻¹ * (S * S) * S⁻¹ := by rw [hS_sq]
      _ = (S⁻¹ * S) * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hS_inv_mul, hS_mul_inv, Matrix.one_mul]
  have hrad_T' : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T') = 1 :=
    hT'_pos.spectralRadius_eq_one_of_map_one_eq_one hT'_one
  have hsim : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (similarityMap (D := D) S T)) =
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T) :=
    spectralRadius_similarityMap_eq (D := D) S hS_det T
  have hscale : spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T') =
      (‖((r : ℂ)⁻¹)‖₊ : ℝ≥0∞) *
        spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            (similarityMap (D := D) S T)) := by
    have hT'_clm :
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T') =
          (r : ℂ)⁻¹ •
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
              (similarityMap (D := D) S T)) := by
      rfl
    rw [hT'_clm]
    exact spectralRadius_smul
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (similarityMap (D := D) S T))
      (c := (r : ℂ)⁻¹) (inv_ne_zero hr_complex)
  have hnorm_inv : (‖((r : ℂ)⁻¹)‖₊ : ℝ≥0∞) = (ENNReal.ofReal r)⁻¹ := by
    let rInvNN : ℝ≥0 := ⟨r⁻¹, by positivity⟩
    have hnorm_cast : ‖(r : ℂ)‖ = r := by
      simp [abs_of_pos hr]
    have hnorm_nnn : ‖((r : ℂ)⁻¹)‖₊ = rInvNN := by
      apply Subtype.ext
      change ‖((r : ℂ)⁻¹)‖ = (rInvNN : ℝ)
      rw [show (rInvNN : ℝ) = r⁻¹ by rfl, norm_inv]
      simpa using congrArg Inv.inv hnorm_cast
    calc
      (‖((r : ℂ)⁻¹)‖₊ : ℝ≥0∞) = (rInvNN : ℝ≥0∞) :=
        congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hnorm_nnn
      _ = ENNReal.ofReal (r⁻¹) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        rfl
      _ = (ENNReal.ofReal r)⁻¹ := by rw [ENNReal.ofReal_inv_of_pos hr]
  have hscaled_one : (ENNReal.ofReal r)⁻¹ *
      spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T) = 1 := by
    calc
      (ENNReal.ofReal r)⁻¹ *
          spectralRadius ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T)
          = (‖((r : ℂ)⁻¹)‖₊ : ℝ≥0∞) *
              spectralRadius ℂ
                ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
                  (similarityMap (D := D) S T)) := by rw [hnorm_inv, hsim]
      _ = spectralRadius ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T') :=
              hscale.symm
      _ = 1 := hrad_T'
  have hr_enn_ne_zero : ENNReal.ofReal r ≠ 0 := by
    intro hzero
    have hr_nonpos : r ≤ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using hzero
    exact (not_le_of_gt hr) hr_nonpos
  have hr_enn_ne_top : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T)
        = ENNReal.ofReal r * ((ENNReal.ofReal r)⁻¹ *
            spectralRadius ℂ
              ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T)) := by
                symm
                rw [← mul_assoc, ENNReal.mul_inv_cancel hr_enn_ne_zero hr_enn_ne_top,
                  one_mul]
    _ = ENNReal.ofReal r * 1 := by rw [hscaled_one]
    _ = ENNReal.ofReal r := by rw [mul_one]

/-- Nonnegative boundary form of the positive-map Perron spectral-radius
identity.  If `r = 0`, positivity and the positive-definite eigenvector force
`T = 0`; otherwise this is
`spectralRadius_eq_of_posDef_eigenvector_of_positive`. -/
theorem spectralRadius_eq_of_posDef_eigenvector_of_positive_of_nonneg
    [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsPositiveMap T)
    (X : Matrix (Fin D) (Fin D) ℂ) (r : ℝ)
    (hX : X.PosDef) (hr : 0 ≤ r)
    (hEig : T X = (r : ℂ) • X) :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T) =
      ENNReal.ofReal r := by
  rcases hr.eq_or_lt with hrzero | hrpos
  · have hrzero' : r = 0 := hrzero.symm
    have hTzero : T = 0 := by
      apply hT.eq_zero_of_map_posDef_eq_zero hX
      simpa [hrzero'] using hEig
    subst T
    simp [hrzero']
  · exact spectralRadius_eq_of_posDef_eigenvector_of_positive
      T hT X r hX hrpos hEig

/-- **Wolf Theorem 6.3, corrected boundary form.**  An irreducible positive
map on a nonzero full matrix algebra has a common lower/upper
Collatz--Wielandt value `r ≥ 0`, attained at a positive-definite density
matrix `X` with `T X = r X`.  Its ordinary `r`-eigenspace is one-dimensional,
every positive eigenvalue with a nonzero positive semidefinite eigenvector
equals `r`, and `r` is the spectral radius.

The value is allowed to be zero exactly to retain the one-dimensional zero-map
boundary case omitted in Wolf's printed statement. -/
theorem exists_wolfTheorem63_of_irreducible_positive [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, ∃ r : ℝ,
      X ∈ densityMatrices D ∧ 0 ≤ r ∧ X.PosDef ∧
        T X = (r : ℂ) • X ∧
        LowerCollatzWielandtFeasible T X r ∧
        UpperCollatzWielandtFeasible T X r ∧
        (∀ Y, ∀ a : ℝ, LowerCollatzWielandtFeasible T Y a → a ≤ r) ∧
        (∀ Y, ∀ a : ℝ, UpperCollatzWielandtFeasible T Y a → r ≤ a) ∧
        Module.finrank ℂ (Module.End.eigenspace T (r : ℂ)) = 1 ∧
        (∀ (Y : Matrix (Fin D) (Fin D) ℂ) (lam : ℝ),
          0 < lam → Y.PosSemidef → Y ≠ 0 →
            T Y = (lam : ℂ) • Y → lam = r) ∧
        spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T) =
            ENNReal.ofReal r := by
  obtain ⟨X, r, hXdensity, hr, hX, hX_eig, hLowerAtX, hUpperAtX,
      hLowerMax, hUpperMin⟩ :=
    exists_posDef_common_collatzWielandt_value_of_irreducible_positive
      T hT hIrr
  have hfinrank :
      Module.finrank ℂ (Module.End.eigenspace T (r : ℂ)) = 1 :=
    finrank_eigenspace_eq_one_of_irreducible_positive
      T hT hIrr hr hX hX_eig
  have hpositive_eigenvalue :
      ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (lam : ℝ),
        0 < lam → Y.PosSemidef → Y ≠ 0 →
          T Y = (lam : ℂ) • Y → lam = r := by
    intro Y lam hlam hY hY_ne hY_eig
    by_cases hrzero : r = 0
    · have hTzero : T = 0 := by
        apply hT.eq_zero_of_map_posDef_eq_zero hX
        simpa [hrzero] using hX_eig
      have hlam_complex : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
      have hsmul : (lam : ℂ) • Y = 0 := by
        rw [← hY_eig, hTzero, LinearMap.zero_apply]
      exact (hY_ne ((smul_eq_zero.mp hsmul).resolve_left hlam_complex)).elim
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
      exact positive_eigenvalue_eq_perron_of_irreducible_positive
        T hT hIrr hrpos hX hX_eig hlam hY hY_ne hY_eig
  have hradius :=
    spectralRadius_eq_of_posDef_eigenvector_of_positive_of_nonneg
      T hT X r hX hr hX_eig
  exact ⟨X, r, hXdensity, hr, hX, hX_eig, hLowerAtX, hUpperAtX,
    hLowerMax, hUpperMin, hfinrank, hpositive_eigenvalue, hradius⟩

/-- **Wolf Theorem 6.3, source form.**  If the irreducible positive map is
nonzero, the common Collatz--Wielandt value in
`exists_wolfTheorem63_of_irreducible_positive` is strictly positive.  This is
Wolf's printed statement with the necessary one-dimensional zero-map boundary
excluded explicitly. -/
theorem exists_wolfTheorem63_of_irreducible_positive_of_ne_zero [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsPositiveMap T) (hIrr : IsIrreducibleMap T) (hT_ne : T ≠ 0) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ, ∃ r : ℝ,
      X ∈ densityMatrices D ∧ 0 < r ∧ X.PosDef ∧
        T X = (r : ℂ) • X ∧
        LowerCollatzWielandtFeasible T X r ∧
        UpperCollatzWielandtFeasible T X r ∧
        (∀ Y, ∀ a : ℝ, LowerCollatzWielandtFeasible T Y a → a ≤ r) ∧
        (∀ Y, ∀ a : ℝ, UpperCollatzWielandtFeasible T Y a → r ≤ a) ∧
        Module.finrank ℂ (Module.End.eigenspace T (r : ℂ)) = 1 ∧
        (∀ (Y : Matrix (Fin D) (Fin D) ℂ) (lam : ℝ),
          0 < lam → Y.PosSemidef → Y ≠ 0 →
            T Y = (lam : ℂ) • Y → lam = r) ∧
        spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T) =
            ENNReal.ofReal r := by
  obtain ⟨X, r, hXdensity, hr, hX, hX_eig, hLowerAtX, hUpperAtX,
      hLowerMax, hUpperMin, hfinrank, hpositive_eigenvalue, hradius⟩ :=
    exists_wolfTheorem63_of_irreducible_positive T hT hIrr
  have hr_ne : r ≠ 0 := by
    intro hrzero
    apply hT_ne
    apply hT.eq_zero_of_map_posDef_eq_zero hX
    simpa [hrzero] using hX_eig
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr_ne)
  exact ⟨X, r, hXdensity, hrpos, hX, hX_eig, hLowerAtX, hUpperAtX,
    hLowerMax, hUpperMin, hfinrank, hpositive_eigenvalue, hradius⟩

/-- **Perron eigenvalue = spectral radius** (Wolf Theorem 6.3(4)).

Let `E` be an irreducible CP map and assume `ρ > 0` is a positive-definite
right eigenvector with `E ρ = r • ρ`, `r > 0`. Then the spectral radius of `E`
(as a continuous linear map on matrices) is exactly `r`.

This compatibility declaration is now a direct specialization of
`spectralRadius_eq_of_posDef_eigenvector_of_positive`.  Thus it follows Wolf's
printed unital-similarity route and does not introduce a Kraus/TP gauge. -/
theorem spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp
    [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hCP : IsCPMap E) (_hIrr : IsIrreducibleMap E)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (r : ℝ)
    (hρ_pd : ρ.PosDef) (hr : 0 < r)
    (hEig : E ρ = (r : ℂ) • ρ) :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) E) =
      ENNReal.ofReal r := by
  exact spectralRadius_eq_of_posDef_eigenvector_of_positive
    E hCP.isPositiveMap ρ r hρ_pd hr hEig

/-- **Real-valued spectral-radius identity** (Wolf Theorem 6.3(4), real form).

Convenience corollary of `spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp`:
the Perron–Frobenius eigenvalue `r > 0` equals the `ℝ`-valued spectral radius
`(ρ(E)).toReal`. -/
theorem spectralRadius_toReal_eq_of_posDef_eigenvector_of_irreducible_cp
    [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hCP : IsCPMap E) (hIrr : IsIrreducibleMap E)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (r : ℝ)
    (hρ_pd : ρ.PosDef) (hr : 0 < r)
    (hEig : E ρ = (r : ℂ) • ρ) :
    (spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) E)).toReal = r := by
  rw [spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp E hCP hIrr ρ r hρ_pd hr hEig]
  simp [hr.le]
