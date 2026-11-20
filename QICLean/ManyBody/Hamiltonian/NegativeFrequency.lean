/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Tactic.Abel
import QICLean.Analysis.GaussianFilter.CauchyTransform
import QICLean.Analysis.GaussianFilter.CommutatorSeries
import QICLean.Analysis.GaussianFilter.MatrixIntegral
import QICLean.Analysis.SpectralFilter.PositiveReplacement
import QICLean.ManyBody.Dynamics.HeisenbergEvolution
import QICLean.ManyBody.Hamiltonian.GaussianFilter
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# Negative frequencies and connected ground correlations

This file proves the negative-frequency step of the exponential clustering theorem of
Hastings–Koma (arXiv:math-ph/0507008, Section 3, Lemma 3.1), for a Hermitian matrix with a
spectral gap above a one-dimensional ground space.

* `centeredObservable ψ A` subtracts from `A` its expectation in the vector `ψ`, written as the
  inner product `⟪ψ, Aψ⟫` divided by `‖ψ‖²`; the centred observable has zero expectation and
  norm at most `2‖A‖`, is additive in `A`, is Hermitian for Hermitian `A`, and is `A - E` at an
  eigenvector of `A` with eigenvalue `E`. For a unit vector and a Hermitian observable it is
  TNLean's `groundCentered` (`MPS/AreaLaw/Hastings/ThreeWaySplitting`, at commit
  `414a18fb88`).
* `negativeFrequencyPart hH A` keeps the matrix elements of `A` between eigenvectors whose
  energy difference is negative. It annihilates the ground space, and the connected ground
  correlation of `A` and `B` is the ground expectation of its commutator with `B` (Hastings–Koma,
  equations (3.1)–(3.6)).
* `gaussianNegativeFrequencyOperator h ε H A` is the Gaussian average of the regularized Cauchy
  factor `(ε - it)⁻¹` times the Heisenberg evolution of `A` (Hastings–Koma, equation (3.8)).
  Its matrix elements are the Gaussian–Cauchy transform of the energy differences, and a
  Lieb–Robinson commutator bound gives a bound on its commutator with `B`, uniform in `ε`
  (Hastings–Koma, Section 3).
* As `ε → 0⁺` the ground expectations of the regularized operators converge, and the limit is
  within `2e^{-q/2}‖A‖‖B‖‖ψ‖²` of the connected correlation at variance `q/Δ²`. Together with
  the uniform commutator bound this gives `norm_centered_ground_correlation_le_gaussian`.

The Lieb–Robinson bound enters as the hypothesis `hLR` on the commutator of the evolved
observable with `B`, so the results apply to every Hamiltonian satisfying such a bound.

Moved from TNLean (`e113e005`): `TNLean/Lattice/{ObservableCentering,
NegativeFrequencyGroundCorrelation, GaussianNegativeFrequencyOperator,
GaussianNegativeFrequencyLocality, GaussianNegativeFrequencyGroundLimits,
GaussianConnectedCorrelation}.lean`. Changes: namespace `ManyBody`; the vector expectation
`normalizedVectorExpectation` is replaced by the inner-product quotient; the Heisenberg
evolution is spelled `heisenbergEvolution`; the Gaussian tail uses
`GaussianFilter.measure_compl_Icc_le`.
-/

noncomputable section

open GaussianFilter

section ObservableCentering

open Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "L" => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)

/-- Subtract the expectation `⟨ψ, A ψ⟩ / ‖ψ‖²` times the identity.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6). -/
def centeredObservable (ψ : EuclideanSpace ℂ n) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A - (⟪ψ, L A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ)) • 1

/-- Centering is additive. Hastings, arXiv:0705.2024v4, `law16.tex`, lines 779–782. -/
theorem centeredObservable_add (ψ : EuclideanSpace ℂ n) (A B : Matrix n n ℂ) :
    centeredObservable ψ (A + B) = centeredObservable ψ A + centeredObservable ψ B := by
  simp only [centeredObservable, map_add, _root_.add_apply, inner_add_right,
    add_div, add_smul]
  abel

/-- The centering of `0` is `0`. -/
@[simp]
theorem centeredObservable_zero (ψ : EuclideanSpace ℂ n) :
    centeredObservable ψ (0 : Matrix n n ℂ) = 0 := by
  simp [centeredObservable]

/-- Centering commutes with finite sums. -/
theorem centeredObservable_sum (ψ : EuclideanSpace ℂ n) {ι : Type*} (s : Finset ι)
    (A : ι → Matrix n n ℂ) :
    centeredObservable ψ (∑ i ∈ s, A i) = ∑ i ∈ s, centeredObservable ψ (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, centeredObservable_add, ih]

/-- The centering of a Hermitian observable is Hermitian: its expectation is real. -/
theorem isHermitian_centeredObservable (ψ : EuclideanSpace ℂ n) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (centeredObservable ψ A).IsHermitian := by
  have hT := isSymmetric_toEuclideanLin_iff.mpr hA
  have hreal : ((⟪ψ, L A ψ⟫_ℂ).re : ℂ) = ⟪ψ, L A ψ⟫_ℂ := hT.coe_re_inner_self_apply ψ
  rw [centeredObservable, ← hreal, ← Complex.ofReal_div]
  exact hA.sub (isHermitian_one.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]))

/-- **Centering at an eigenvector.** At a nonzero eigenvector `ψ` of `A` with eigenvalue `E`,
the centered observable is `A - E`. Hastings, arXiv:0705.2024v4, `law16.tex`,
lines 766–767. -/
theorem centeredObservable_of_apply_eq_smul {ψ : EuclideanSpace ℂ n} (hψ : ψ ≠ 0)
    {A : Matrix n n ℂ} {E : ℂ} (hE : L A ψ = E • ψ) : centeredObservable ψ A = A - E • 1 := by
  have hd : ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ)
  have hself : ⟪ψ, ψ⟫_ℂ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) :=
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ).trans (Complex.ofReal_pow ‖ψ‖ 2).symm
  rw [centeredObservable, hE, inner_smul_right, hself, mul_div_cancel_right₀ _ hd]

/-- The expectation divided by the squared norm of the vector is bounded by the observable norm,
for every nonzero vector. Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6); this is Cauchy--Schwarz and the operator-norm bound. -/
theorem norm_inner_div_norm_sq_le
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ≠ 0) (A : Matrix n n ℂ) :
    ‖⟪ψ, L A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ)‖ ≤ ‖A‖ := by
  have hpos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hA : ‖L A ψ‖ ≤ ‖A‖ * ‖ψ‖ := Matrix.l2_opNorm_mulVec A ψ
  rw [norm_div, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)]
  apply (div_le_iff₀ (pow_pos hpos 2)).mpr
  calc
    _ ≤ ‖ψ‖ * ‖L A ψ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ψ‖ * (‖A‖ * ‖ψ‖) := mul_le_mul_of_nonneg_left hA (norm_nonneg _)
    _ = _ := by ring

/-- The centered observable has zero expectation in its nonzero reference vector.
Source: Hastings–Koma,
arXiv:math-ph/0507008, Section 3, equations (3.1)–(3.6). -/
theorem inner_centeredObservable_eq_zero
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ≠ 0) (A : Matrix n n ℂ) :
    ⟪ψ, L (centeredObservable ψ A) ψ⟫_ℂ = 0 := by
  have hd : ((‖ψ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 (norm_ne_zero_iff.mpr hψ))
  have hself : ⟪ψ, ψ⟫_ℂ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) :=
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ).trans (Complex.ofReal_pow ‖ψ‖ 2).symm
  rw [centeredObservable, map_sub, map_smul, map_one]
  change ⟪ψ, L A ψ - (⟪ψ, L A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ)) • ψ⟫_ℂ = 0
  rw [inner_sub_right, inner_smul_right, hself, div_mul_cancel₀ _ hd, sub_self]

/-- centering increases the observable norm by at most a factor two.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6), followed by the elementary triangle estimate. -/
theorem norm_centeredObservable_le
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ≠ 0) (A : Matrix n n ℂ) :
    ‖centeredObservable ψ A‖ ≤ 2 * ‖A‖ := by
  calc
    _ ≤ ‖A‖ + ‖(⟪ψ, L A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ)) • (1 : Matrix n n ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ ‖A‖ + ‖(⟪ψ, L A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ))‖ :=
      add_le_add le_rfl
        (SpectralFilter.norm_smul_one_le (n := n) (⟪ψ, L A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ)))
    _ ≤ ‖A‖ + ‖A‖ := add_le_add le_rfl (norm_inner_div_norm_sq_le hψ A)
    _ = _ := by ring

/-- Centering only the first observable gives the covariance.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6). -/
theorem inner_centeredObservable_mul
    (ψ : EuclideanSpace ℂ n) (A B : Matrix n n ℂ) :
    ⟪ψ, L (centeredObservable ψ A * B) ψ⟫_ℂ =
      ⟪ψ, L (A * B) ψ⟫_ℂ - (⟪ψ, L A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ)) * ⟪ψ, L B ψ⟫_ℂ := by
  rw [centeredObservable, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    map_sub, map_smul]
  change ⟪ψ, L (A * B) ψ - (⟪ψ, L A ψ⟫_ℂ / ((‖ψ‖ ^ 2 : ℝ) : ℂ)) • L B ψ⟫_ℂ = _
  rw [inner_sub_right, inner_smul_right]

/-- Centering preserves every complex submodule containing the identity
and the original observable, in particular a supported-operator space.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6), where scalar subtraction preserves local support. -/
theorem centeredObservable_mem
    (ψ : EuclideanSpace ℂ n) {S : Submodule ℂ (Matrix n n ℂ)}
    (h1 : (1 : Matrix n n ℂ) ∈ S) {A : Matrix n n ℂ} (hA : A ∈ S) :
    centeredObservable ψ A ∈ S :=
  S.sub_mem hA (S.smul_mem _ h1)

/-- The scalar subtraction leaves the commutator with every observable
unchanged. Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.6), used before applying the time-commutator bound. -/
theorem centeredObservable_commutator
    (ψ : EuclideanSpace ℂ n) (A B : Matrix n n ℂ) :
    centeredObservable ψ A * B - B * centeredObservable ψ A = A * B - B * A := by
  simp only [centeredObservable, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  abel

end ManyBody

end ObservableCentering

section SharpNegativeFrequency

open Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace


namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The energy-lowering part `∑_{E_i < E_j} ⟨e_i, A e_j⟩ |e_i⟩⟨e_j|` of an observable, in an
orthonormal eigenbasis of the Hermitian Hamiltonian. Source: Hastings–Koma,
arXiv:math-ph/0507008, equations (3.1)–(3.6). -/
def negativeFrequencyPart {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (A : Matrix n n ℂ) : Matrix n n ℂ :=
  let b := hH.eigenvectorBasis
  ∑ i, ∑ j, if hH.eigenvalues i < hH.eigenvalues j then
    ⟪b i, toEuclideanCLM (n := n) (𝕜 := ℂ) A (b j)⟫_ℂ • vecMulVec ⇑(b i) (star ⇑(b j)) else 0

/-- The negative-frequency part as an operator on the Euclidean space: the sum of the rank-one
operators `⟨e_i, A e_j⟩ |e_i⟩⟨e_j|` over `E_i < E_j`. -/
private theorem toEuclideanCLM_negativeFrequencyPart {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (A : Matrix n n ℂ) :
    toEuclideanCLM (n := n) (𝕜 := ℂ) (negativeFrequencyPart hH A) =
      ∑ i, ∑ j, if hH.eigenvalues i < hH.eigenvalues j then
        ⟪hH.eigenvectorBasis i, toEuclideanCLM (n := n) (𝕜 := ℂ) A (hH.eigenvectorBasis j)⟫_ℂ •
          InnerProductSpace.rankOne ℂ (hH.eigenvectorBasis i) (hH.eigenvectorBasis j)
      else 0 := by
  simp only [negativeFrequencyPart, map_sum, apply_ite (toEuclideanCLM (n := n) (𝕜 := ℂ)),
    map_smul, map_zero]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  congr 2
  ext x : 1
  rw [← InnerProductSpace.symm_toEuclideanLin_rankOne (𝕜 := ℂ),
    ← ContinuousLinearMap.coe_coe, coe_toEuclideanCLM_eq_toEuclideanLin,
    LinearEquiv.apply_symm_apply]
  rfl

omit [DecidableEq n] in
private theorem inner_apply_eq_double_sum
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n))
    (T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (ψ x : EuclideanSpace ℂ n) :
    ⟪ψ, T x⟫_ℂ = ∑ i, ∑ j,
      ⟪b j, x⟫_ℂ * ⟪b i, T (b j)⟫_ℂ * ⟪ψ, b i⟫_ℂ := by
  have hexpand (y : EuclideanSpace ℂ n) :
      ⟪ψ, y⟫_ℂ = ∑ i, ⟪b i, y⟫_ℂ * ⟪ψ, b i⟫_ℂ := by
    conv_lhs => rw [← b.sum_repr' y]
    simp only [inner_sum, inner_smul_right]
  calc
    ⟪ψ, T x⟫_ℂ = ∑ j, ⟪b j, x⟫_ℂ * ⟪ψ, T (b j)⟫_ℂ := by
      conv_lhs => rw [← b.sum_repr' x]
      simp only [map_sum, map_smul, inner_sum, inner_smul_right]
    _ = ∑ j, ∑ i, ⟪b j, x⟫_ℂ * ⟪b i, T (b j)⟫_ℂ * ⟪ψ, b i⟫_ℂ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hexpand (T (b j)), Finset.mul_sum]
      simp only [mul_assoc]
    _ = _ := Finset.sum_comm

/-- The negative-frequency part annihilates every eigenvector at the least eigenvalue.
Source: Hastings–Koma,
arXiv:math-ph/0507008, equations (3.2)–(3.5). -/
theorem negativeFrequencyPart_apply_ground_eq_zero {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {E₀ : ℝ} (hmin : ∀ i, E₀ ≤ hH.eigenvalues i)
    (A : Matrix n n ℂ) {ψ : EuclideanSpace ℂ n}
    (hψ : ψ ∈ groundSpace H E₀) :
    toEuclideanCLM (n := n) (𝕜 := ℂ) (negativeFrequencyPart hH A) ψ = 0 := by
  rw [toEuclideanCLM_negativeFrequencyPart]
  simp only [_root_.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : hH.eigenvalues i < hH.eigenvalues j
  · have hj : hH.eigenvalues j ≠ E₀ := by linarith [hmin i]
    have hzero := inner_eq_zero_of_mem_groundSpace hH hj
      (SpectralFilter.mulVec_eigenvectorBasis_complex hH j) hψ
    simp only [ite_eq_left hij, _root_.smul_apply,
      InnerProductSpace.rankOne_apply, hzero, zero_smul, smul_zero]
  · simp only [ite_eq_right hij, _root_.zero_apply]

private theorem inner_ground_negativeFrequencyPart_apply
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hmin : ∀ i, E₀ ≤ hH.eigenvalues i) (A : Matrix n n ℂ)
    {ψ x : EuclideanSpace ℂ n} (hψ : ψ ∈ groundSpace H E₀)
    (hx : x ∈ (groundSpace H E₀)ᗮ) :
    ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) (negativeFrequencyPart hH A) x⟫_ℂ =
      ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A x⟫_ℂ := by
  let b := hH.eigenvectorBasis
  rw [inner_apply_eq_double_sum b (toEuclideanCLM (n := n) (𝕜 := ℂ) A) ψ x,
    toEuclideanCLM_negativeFrequencyPart]
  simp only [_root_.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hij : hH.eigenvalues i < hH.eigenvalues j
  · simp only [ite_eq_left hij, _root_.smul_apply,
      InnerProductSpace.rankOne_apply, inner_smul_right]
    ring
  · have hvanish :
        ⟪b j, x⟫_ℂ * ⟪b i, toEuclideanCLM (n := n) (𝕜 := ℂ) A (b j)⟫_ℂ *
          ⟪ψ, b i⟫_ℂ = 0 := by
      by_cases hi : hH.eigenvalues i = E₀
      · have hj : hH.eigenvalues j = E₀ := by
          have hge := hmin j
          rw [hi] at hij
          linarith
        have hmem : b j ∈ groundSpace H E₀ := eigenvectorBasis_mem_groundSpace hH hj
        have hz := ((groundSpace H E₀).mem_orthogonal x).mp hx (b j) hmem
        simp only [hz, zero_mul]
      · have hz : ⟪ψ, b i⟫_ℂ = 0 := inner_eq_zero_symm.mpr
          (inner_eq_zero_of_mem_groundSpace hH hi
            (SpectralFilter.mulVec_eigenvectorBasis_complex hH i) hψ)
        simp only [hz, mul_zero]
    simpa only [ite_eq_right hij, _root_.zero_apply, inner_zero_right] using hvanish.symm

/-- For a vector `ψ` at the least eigenvalue and the projection `P₀` onto that eigenspace,
`⟨ψ, A (1 - P₀) B ψ⟩ = ⟨ψ, [A⁻, B] ψ⟩`, where `A⁻` is the negative-frequency part. The
eigenspace may be degenerate. Source: Hastings–Koma,
arXiv:math-ph/0507008, equations (3.1)–(3.6). -/
theorem inner_ground_projected_eq_negativeFrequency_commutator
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hmin : ∀ i, E₀ ≤ hH.eigenvalues i) (A B : Matrix n n ℂ)
    {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundSpace H E₀) :
    ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A
      (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ -
        (groundSpace H E₀).starProjection
          (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ))⟫_ℂ =
      ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ)
        (negativeFrequencyPart hH A * B - B * negativeFrequencyPart hH A) ψ⟫_ℂ := by
  let K := groundSpace H E₀
  let y := toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ
  have hsplit := inner_ground_negativeFrequencyPart_apply hH hmin A hψ
    (K.sub_starProjection_mem_orthogonal y)
  have hkill := negativeFrequencyPart_apply_ground_eq_zero hH hmin A hψ
  have hkillProjection := negativeFrequencyPart_apply_ground_eq_zero hH hmin A
    (K.starProjection_apply_mem y)
  rw [map_sub, hkillProjection, sub_zero] at hsplit
  simpa only [map_sub, map_mul, _root_.sub_apply, mul_apply_eq_comp,
    ContinuousLinearMap.comp_apply, hkill, map_zero, sub_zero] using hsplit.symm

/-- If the ground space is spanned by `ψ`, then
`⟨ψ, A B ψ⟩ - ⟨ψ, A ψ⟩ ⟨ψ, B ψ⟩ / ‖ψ‖² = ⟨ψ, [A⁻, B] ψ⟩`.
Source: Hastings–Koma, arXiv:math-ph/0507008, equations (3.1)–(3.6),
specialized to an exactly one-dimensional ground eigenspace. -/
theorem inner_ground_connected_eq_negativeFrequency_commutator
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hmin : ∀ i, E₀ ≤ hH.eigenvalues i) (A B : Matrix n n ℂ)
    {ψ : EuclideanSpace ℂ n} (hline : groundSpace H E₀ = Submodule.span ℂ {ψ}) :
    ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A
        (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ)⟫_ℂ -
        ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A ψ⟫_ℂ *
          ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ⟫_ℂ /
            ((‖ψ‖ ^ 2 : ℝ) : ℂ) =
      ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ)
        (negativeFrequencyPart hH A * B - B * negativeFrequencyPart hH A) ψ⟫_ℂ := by
  have hψ : ψ ∈ groundSpace H E₀ := hline ▸ Submodule.mem_span_singleton_self ψ
  calc
    _ = ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A
        (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ -
          (groundSpace H E₀).starProjection
            (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ))⟫_ℂ := by
      rw [hline, Submodule.starProjection_singleton (𝕜 := ℂ)]
      simp only [map_sub, map_smul, inner_sub_right, inner_smul_right]
      let a : ℂ := ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A ψ⟫_ℂ
      let b : ℂ := ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ⟫_ℂ
      let δ : ℂ := Complex.ofReal (‖ψ‖ ^ 2)
      let e : ℂ := ⟪ψ, toEuclideanCLM (n := n) (𝕜 := ℂ) A
        (toEuclideanCLM (n := n) (𝕜 := ℂ) B ψ)⟫_ℂ
      change e - a * b / δ = e - (b / δ) * a
      apply congrArg (fun z : ℂ ↦ e - z)
      calc
        a * b / δ = b * a / δ := congrArg (fun z : ℂ ↦ z / δ) (mul_comm a b)
        _ = b / δ * a := (div_mul_eq_mul_div₀ b a δ).symm
    _ = _ := inner_ground_projected_eq_negativeFrequency_commutator hH hmin A B hψ

end ManyBody

end SharpNegativeFrequency

section RegularizedOperator

open MeasureTheory ProbabilityTheory Complex Matrix
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace NNReal Topology

namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The regularized Cauchy factor times the Heisenberg evolution.
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.8). -/
def gaussianNegativeFrequencyIntegrand (H A : Matrix n n ℂ) (ε t : ℝ) : Matrix n n ℂ :=
  ((ε : ℂ) - Complex.I * t)⁻¹ •
    heisenbergEvolution H t A

/-- The regularized frequency integral, normalized by the density
at zero of the inverse-variance Gaussian. Source: Hastings–Koma,
arXiv:math-ph/0507008, Lemma 3.1, equations (3.7)–(3.8). -/
def gaussianNegativeFrequencyOperator (h : ℝ≥0) (ε : ℝ) (H A : Matrix n n ℂ) :
    Matrix n n ℂ :=
  (GaussianFilter.kernel h⁻¹ 0 : ℂ) •
    ∫ t : ℝ, gaussianNegativeFrequencyIntegrand H A ε t ∂gaussianReal 0 h

/-- Positive regularization makes the time integrand continuous.
Source: Hastings–Koma, arXiv:math-ph/0507008, equation (3.8). -/
theorem continuous_gaussianNegativeFrequencyIntegrand
    (H A : Matrix n n ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (gaussianNegativeFrequencyIntegrand H A ε) := by
  unfold gaussianNegativeFrequencyIntegrand
  apply Continuous.fun_smul
  · exact (by fun_prop : Continuous fun t : ℝ ↦ (ε : ℂ) - Complex.I * t).inv₀
      (cauchyDenominator_ne_zero hε)
  · exact SpectralFilter.continuous_hermitianUnitaryPath_conj H A

/-- Unitary conjugation bounds the integrand by the inverse positive
regularizer times the observable norm. Source: Hastings–Koma,
arXiv:math-ph/0507008, equation (3.8). -/
theorem norm_gaussianNegativeFrequencyIntegrand_le
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖gaussianNegativeFrequencyIntegrand H A ε t‖ ≤ ε⁻¹ * ‖A‖ := by
  rw [gaussianNegativeFrequencyIntegrand, norm_smul, heisenbergEvolution,
    SpectralFilter.norm_hermitianUnitaryPath_conj hH A t]
  exact mul_le_mul_of_nonneg_right (norm_inv_cauchyDenominator_le hε t) (norm_nonneg A)

/-- The operator-valued integrand is Bochner integrable for every
Gaussian variance and every positive regularizer. In particular its norm
is integrable. Source: Hastings–Koma, arXiv:math-ph/0507008,
Lemma 3.1, equation (3.8). -/
theorem integrable_gaussianNegativeFrequencyIntegrand
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (gaussianNegativeFrequencyIntegrand H A ε) (gaussianReal 0 h) := by
  apply (integrable_const (ε⁻¹ * ‖A‖)).mono'
    (continuous_gaussianNegativeFrequencyIntegrand H A hε).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_gaussianNegativeFrequencyIntegrand_le hH A hε)

/-- The regularized observable has norm at most `c_h ε⁻¹ ‖A‖`. Source: Hastings–Koma,
arXiv:math-ph/0507008, equation (3.8). -/
theorem norm_gaussianNegativeFrequencyOperator_le
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ‖gaussianNegativeFrequencyOperator h ε H A‖ ≤
      GaussianFilter.kernel h⁻¹ 0 * (ε⁻¹ * ‖A‖) := by
  rw [gaussianNegativeFrequencyOperator, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (GaussianFilter.kernel_nonneg _ _)]
  apply mul_le_mul_of_nonneg_left ?_ (GaussianFilter.kernel_nonneg _ _)
  simpa using norm_integral_le_of_norm_le_const (μ := gaussianReal 0 h)
    (Filter.Eventually.of_forall (norm_gaussianNegativeFrequencyIntegrand_le hH A hε))

/-- Between energy eigenvectors at energies `E` and `E'`, the matrix element of the operator
integral is the Gaussian–Cauchy transform at `E - E'` times the matrix element of `A`.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1,
equations (3.7)–(3.13). -/
theorem dotProduct_integral_gaussianNegativeFrequencyIntegrand_mulVec
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) {v w : n → ℂ} {E E' : ℝ}
    (hv : H *ᵥ v = (E : ℂ) • v) (hw : H *ᵥ w = (E' : ℂ) • w) :
    star v ⬝ᵥ ((∫ t : ℝ, gaussianNegativeFrequencyIntegrand H A ε t
        ∂gaussianReal 0 h) *ᵥ w) =
      gaussianCauchyTransform h ε (E - E') * (star v ⬝ᵥ (A *ᵥ w)) := by
  let Lin : Matrix n n ℂ →ₗ[ℂ] ℂ :=
    (dotProductBilin ℂ ℂ (star v)).comp ((Matrix.mulVecBilin ℂ ℂ).flip w)
  let L : Matrix n n ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap Lin
  have hL : ∀ M, L M = star v ⬝ᵥ (M *ᵥ w) := fun M ↦ rfl
  rw [← hL, ← L.integral_comp_comm
    (integrable_gaussianNegativeFrequencyIntegrand h hH A hε)]
  simp_rw [gaussianNegativeFrequencyIntegrand, heisenbergEvolution, map_smul, hL,
    SpectralFilter.dotProduct_conj_mulVec hH A hv hw, smul_eq_mul]
  have hphase (t : ℝ) : (t : ℂ) * ((E : ℂ) - E') * Complex.I =
      ((E - E' : ℝ) : ℂ) * t * Complex.I := by
    push_cast
    ring
  simp_rw [hphase, ← mul_assoc]
  rw [integral_mul_const]
  rfl

/-- Exact eigenvector matrix elements of the normalized regularized
observable. Source: Hastings–Koma, arXiv:math-ph/0507008,
Lemma 3.1, equations (3.7)–(3.13). -/
theorem dotProduct_gaussianNegativeFrequencyOperator_mulVec
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) {v w : n → ℂ} {E E' : ℝ}
    (hv : H *ᵥ v = (E : ℂ) • v) (hw : H *ᵥ w = (E' : ℂ) • w) :
    star v ⬝ᵥ (gaussianNegativeFrequencyOperator h ε H A *ᵥ w) =
      (GaussianFilter.kernel h⁻¹ 0 : ℂ) * gaussianCauchyTransform h ε (E - E') *
        (star v ⬝ᵥ (A *ᵥ w)) := by
  rw [gaussianNegativeFrequencyOperator, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, dotProduct_integral_gaussianNegativeFrequencyIntegrand_mulVec h hH A hε hv hw,
    mul_assoc]

/-- The eigenvector matrix-element formula in the Euclidean Hilbert space.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1. -/
theorem inner_gaussianNegativeFrequencyOperator
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {ε : ℝ} (hε : 0 < ε) {v w : EuclideanSpace ℂ n} {E E' : ℝ}
    (hv : H *ᵥ WithLp.ofLp v = (E : ℂ) • WithLp.ofLp v)
    (hw : H *ᵥ WithLp.ofLp w = (E' : ℂ) • WithLp.ofLp w) :
    ⟪v, Matrix.toEuclideanLin (gaussianNegativeFrequencyOperator h ε H A) w⟫_ℂ =
      (GaussianFilter.kernel h⁻¹ 0 : ℂ) * gaussianCauchyTransform h ε (E - E') *
        ⟪v, Matrix.toEuclideanLin A w⟫_ℂ := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, dotProduct_comm] using
    dotProduct_gaussianNegativeFrequencyOperator_mulVec h hH A hε hv hw

/-- The regularized observable converges entrywise between energy
eigenvectors to the Gaussian negative-frequency multiplier. This follows
from the scalar Cauchy limit, with no supplied multiplier premise.
Source: Hastings–Koma, arXiv:math-ph/0507008, Lemma 3.1, equation (3.7). -/
theorem tendsto_dotProduct_gaussianNegativeFrequencyOperator
    (h : ℝ≥0) (hh : 0 < h) {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (A : Matrix n n ℂ) {v w : n → ℂ} {E E' : ℝ}
    (hv : H *ᵥ v = (E : ℂ) • v) (hw : H *ᵥ w = (E' : ℂ) • w) :
    Filter.Tendsto (fun ε : ℝ ↦
      star v ⬝ᵥ (gaussianNegativeFrequencyOperator h ε H A *ᵥ w))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((gaussianReal 0 h⁻¹).real (Set.Ici (E - E')) : ℂ) *
        (star v ⬝ᵥ (A *ᵥ w)))) := by
  apply ((tendsto_normalized_gaussianCauchyTransform h hh (E - E')).mul_const
    (star v ⬝ᵥ (A *ᵥ w))).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (dotProduct_gaussianNegativeFrequencyOperator_mulVec h hH A hε hv hw).symm

end ManyBody

end RegularizedOperator

section Locality

open MeasureTheory ProbabilityTheory Matrix GaussianFilter
open scoped Matrix.Norms.L2Operator NNReal

namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem norm_inv_cauchyDenominator_le_abs_time (ε : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ‖((ε : ℂ) - Complex.I * t)⁻¹‖ ≤ |t|⁻¹ := by
  have hnorm : |t| ≤ ‖(ε : ℂ) - Complex.I * t‖ := by
    simpa using Complex.abs_im_le_norm ((ε : ℂ) - Complex.I * t)
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le (abs_pos.mpr ht) hnorm

private theorem exp_sub_one_le_mul_exp (x : ℝ) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith

/-- If `‖[A(t), B]‖ ≤ C (e^{v|t|} - 1)` for all `t`, then the commutator of the regularized
negative-frequency operator with `B` is bounded by
`c_h (C v e^{vT} + (2‖A‖‖B‖/T) e^{-T²/(2h)})`, uniformly in the regularizer `ε > 0`. The
short-time zero of the commutator cancels the Cauchy pole; the Gaussian tail bounds the
long-time part. Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3. -/
theorem norm_commutator_gaussianNegativeFrequencyOperator_le
    (h : ℝ≥0) {H : Matrix n n ℂ} (hH : H.IsHermitian) (A B : Matrix n n ℂ)
    {ε T C v : ℝ} (hε : 0 < ε) (hT : 0 < T) (hC : 0 ≤ C) (hv : 0 ≤ v)
    (hLR : ∀ t : ℝ,
      ‖heisenbergEvolution H t A * B - B * heisenbergEvolution H t A‖ ≤
        C * (Real.exp (v * |t|) - 1)) :
    ‖gaussianNegativeFrequencyOperator h ε H A * B -
        B * gaussianNegativeFrequencyOperator h ε H A‖ ≤
      kernel h⁻¹ 0 * (C * v * Real.exp (v * T) +
        (2 * ‖A‖ * ‖B‖ / T) * Real.exp (-T ^ 2 / (2 * (h : ℝ)))) := by
  simp only [heisenbergEvolution] at hLR
  let μ : Measure ℝ := gaussianReal 0 h
  let f := gaussianNegativeFrequencyIntegrand H A ε
  let L := GaussianFilter.commutatorCLM B
  let a : ℝ → Matrix n n ℂ := fun t ↦
    hermitianUnitaryPath H t * A * hermitianUnitaryPath H (-t)
  let M := C * v * Real.exp (v * T)
  let D := 2 * ‖A‖ * ‖B‖
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hC hv) (Real.exp_pos _).le
  have hnorm (t : ℝ) : ‖L (f t)‖ =
      ‖((ε : ℂ) - Complex.I * t)⁻¹‖ * ‖a t * B - B * a t‖ := by
    simp only [L, f, gaussianNegativeFrequencyIntegrand, heisenbergEvolution, map_smul,
      norm_smul, GaussianFilter.commutatorCLM_apply, a]
    rw [norm_sub_rev]
  have hglob (t : ℝ) : ‖a t * B - B * a t‖ ≤ D := by
    calc
      _ ≤ ‖a t * B‖ + ‖B * a t‖ := norm_sub_le _ _
      _ ≤ ‖a t‖ * ‖B‖ + ‖B‖ * ‖a t‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = D := by
        rw [SpectralFilter.norm_hermitianUnitaryPath_conj hH A t]
        dsimp only [D]
        ring
  have hshort (t : ℝ) (ht : t ∈ Set.Icc (-T) T) : ‖L (f t)‖ ≤ M := by
    rw [hnorm]
    by_cases ht0 : t = 0
    · subst t
      have hz : ‖a 0 * B - B * a 0‖ = 0 := le_antisymm
        (by simpa only [abs_zero, mul_zero, Real.exp_zero, sub_self, mul_zero] using hLR 0)
        (norm_nonneg _)
      rw [hz, mul_zero]
      exact hM
    have hs : 0 < |t| := abs_pos.mpr ht0
    have hsT : |t| ≤ T := abs_le.mpr ht
    have hcomm : ‖a t * B - B * a t‖ ≤ |t| * M := by
      calc
        _ ≤ C * (Real.exp (v * |t|) - 1) := hLR t
        _ ≤ C * ((v * |t|) * Real.exp (v * |t|)) :=
          mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp _) hC
        _ ≤ C * ((v * |t|) * Real.exp (v * T)) := by
          gcongr
        _ = _ := by dsimp only [M]; ring
    calc
      _ ≤ |t|⁻¹ * (|t| * M) :=
        mul_le_mul (norm_inv_cauchyDenominator_le_abs_time ε ht0) hcomm
          (norm_nonneg _) (inv_nonneg.mpr hs.le)
      _ = M := by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have hlong (t : ℝ) (ht : t ∈ (Set.Icc (-T) T)ᶜ) : ‖L (f t)‖ ≤ D / T := by
    have hs : T < |t| := by
      by_contra hs
      exact ht (abs_le.mp (le_of_not_gt hs))
    have ht0 : t ≠ 0 := abs_pos.mp (hT.trans hs)
    have hi : ‖((ε : ℂ) - Complex.I * t)⁻¹‖ ≤ T⁻¹ :=
      (norm_inv_cauchyDenominator_le_abs_time ε ht0).trans (by
        simpa only [one_div] using one_div_le_one_div_of_le hT hs.le)
    rw [hnorm]
    calc
      _ ≤ T⁻¹ * D := mul_le_mul hi (hglob t) (norm_nonneg _) (inv_nonneg.mpr hT.le)
      _ = D / T := by rw [div_eq_mul_inv, mul_comm]
  have hint := integrable_gaussianNegativeFrequencyIntegrand h hH A hε
  have hmap : Integrable (fun t ↦ L (f t)) μ := L.integrable_comp hint
  have hmass : ‖∫ t, L (f t) ∂μ‖ ≤ M + (D / T) * μ.real (Set.Icc (-T) T)ᶜ := by
    calc
      _ ≤ ‖∫ t in Set.Icc (-T) T, L (f t) ∂μ‖ +
          ‖∫ t in (Set.Icc (-T) T)ᶜ, L (f t) ∂μ‖ := by
        rw [← integral_add_compl measurableSet_Icc hmap]
        exact norm_add_le _ _
      _ ≤ M * μ.real (Set.Icc (-T) T) + (D / T) * μ.real (Set.Icc (-T) T)ᶜ :=
        add_le_add (norm_setIntegral_le_of_norm_le_const (by finiteness) hshort)
          (norm_setIntegral_le_of_norm_le_const (by finiteness) hlong)
      _ ≤ _ := add_le_add (mul_le_of_le_one_right hM measureReal_le_one) le_rfl
  rw [norm_sub_rev]
  change ‖L (gaussianNegativeFrequencyOperator h ε H A)‖ ≤ _
  rw [gaussianNegativeFrequencyOperator, map_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (kernel_nonneg _ _), ← L.integral_comp_comm hint]
  apply mul_le_mul_of_nonneg_left ?_ (kernel_nonneg _ _)
  apply hmass.trans
  dsimp only [M, D, μ]
  gcongr
  exact measure_compl_Icc_le h hT.le

end ManyBody

end Locality

section GroundLimits

open MeasureTheory ProbabilityTheory Complex Matrix Filter
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal Topology


namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "L" => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)

private theorem inner_adjoint_matrix (A : Matrix n n ℂ)
    (x y : EuclideanSpace ℂ n) :
    ⟪x, L Aᴴ y⟫_ℂ = star ⟪y, L A x⟫_ℂ := by
  rw [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (L A x) y).symm

private theorem star_inner_matrix (A : Matrix n n ℂ)
    (x y : EuclideanSpace ℂ n) :
    star ⟪x, L A y⟫_ℂ = ⟪y, L Aᴴ x⟫_ℂ :=
  (inner_adjoint_matrix A y x).symm

private theorem inner_cutoff_limit
    {q Δ : ℝ} (hq : 0 < q) (hΔ : 0 < Δ)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (A : Matrix n n ℂ)
    {v w : EuclideanSpace ℂ n} {E E' : ℝ}
    (hv : H *ᵥ WithLp.ofLp v = (E : ℂ) • WithLp.ofLp v)
    (hw : H *ᵥ WithLp.ofLp w = (E' : ℂ) • WithLp.ofLp w) :
    Tendsto (fun ε : ℝ ↦
      ⟪v, L (gaussianNegativeFrequencyOperator (q / Δ ^ 2).toNNReal ε H A) w⟫_ℂ)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((gaussianNegativeFrequencyCutoff q Δ (E - E') : ℂ) * ⟪v, L A w⟫_ℂ)) := by
  apply ((tendsto_normalized_gaussianCauchyTransform_cutoff hq hΔ (E - E')).mul_const
    ⟪v, L A w⟫_ℂ).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (inner_gaussianNegativeFrequencyOperator _ hH A hε hv hw).symm

omit [DecidableEq n] in
private theorem exists_vector_limit_of_inner_limits
    {α : Type*} {l : Filter α} [l.NeBot]
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n))
    (f : α → EuclideanSpace ℂ n) (c : n → ℂ)
    (hc : ∀ i, Tendsto (fun t ↦ ⟪b i, f t⟫_ℂ) l (𝓝 (c i))) :
    ∃ ξ : EuclideanSpace ℂ n, Tendsto f l (𝓝 ξ) ∧ ∀ i, ⟪b i, ξ⟫_ℂ = c i := by
  let ξ := ∑ i, c i • b i
  have hsum := tendsto_finsetSum Finset.univ fun i _ ↦ (hc i).smul_const (b i)
  have hf : Tendsto f l (𝓝 ξ) := by
    apply hsum.congr'
    exact Eventually.of_forall fun t ↦ b.sum_repr' (f t)
  refine ⟨ξ, hf, fun i ↦ ?_⟩
  exact tendsto_nhds_unique (tendsto_const_nhds.inner hf) (hc i)

private theorem centered_ground_line_inner_eq_zero
    {H : Matrix n n ℂ} {E₀ : ℝ} {ψ : EuclideanSpace ℂ n}
    (hline : groundSpace H E₀ = Submodule.span ℂ {ψ})
    (A : Matrix n n ℂ) (hcenter : ⟪ψ, L A ψ⟫_ℂ = 0)
    {φ : EuclideanSpace ℂ n} (hφ : φ ∈ groundSpace H E₀) :
    ⟪φ, L A ψ⟫_ℂ = 0 := by
  rw [hline, Submodule.mem_span_singleton] at hφ
  obtain ⟨c, rfl⟩ := hφ
  rw [inner_smul_left, hcenter, mul_zero]

/-- regularized operators and their adjoints have ground-vector
limits with the two Gaussian separation bounds. Neither the limits nor
their spectral coefficients are hypotheses. Source: Hastings–Koma,
arXiv:math-ph/0507008, Section 3, equations (3.1)–(3.14), Lemma 3.1. -/
theorem exists_gaussianNegativeFrequency_ground_limits
    {q Δ : ℝ} (hq : 0 < q) (hΔ : 0 < Δ)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : IsGapped H E₀ Δ)
    {ψ : EuclideanSpace ℂ n} (hline : groundSpace H E₀ = Submodule.span ℂ {ψ})
    (A : Matrix n n ℂ) (hcenter : ⟪ψ, L A ψ⟫_ℂ = 0) :
    ∃ ξ η : EuclideanSpace ℂ n,
      Tendsto (fun ε : ℝ ↦
        L (gaussianNegativeFrequencyOperator (q / Δ ^ 2).toNNReal ε H A) ψ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ξ) ∧
      Tendsto (fun ε : ℝ ↦
        L (gaussianNegativeFrequencyOperator (q / Δ ^ 2).toNNReal ε H A)ᴴ ψ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 η) ∧
      ‖ξ‖ ≤ Real.exp (-q / 2) * ‖L A ψ‖ ∧
      ‖L Aᴴ ψ - η‖ ≤ Real.exp (-q / 2) * ‖L Aᴴ ψ‖ := by
  have hψ : ψ ∈ groundSpace H E₀ := hline ▸ Submodule.mem_span_singleton_self ψ
  replace hgap := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  let b := hH.eigenvectorBasis
  let F := fun ε : ℝ ↦ gaussianNegativeFrequencyOperator (q / Δ ^ 2).toNNReal ε H A
  have hb (i : n) :
      H *ᵥ WithLp.ofLp (b i) = (hH.eigenvalues i : ℂ) • WithLp.ofLp (b i) :=
    SpectralFilter.mulVec_eigenvectorBasis_complex hH i
  have hψ' := mem_groundSpace_iff_mulVec.mp hψ
  have hplus (i : n) := inner_cutoff_limit hq hΔ hH A (hb i) hψ'
  have hminus (i : n) :
      Tendsto (fun ε : ℝ ↦ ⟪b i, L (F ε)ᴴ ψ⟫_ℂ)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ((gaussianNegativeFrequencyCutoff q Δ (E₀ - hH.eigenvalues i) : ℂ) *
          ⟪b i, L Aᴴ ψ⟫_ℂ)) := by
    have h := (inner_cutoff_limit hq hΔ hH A hψ' (hb i)).star
    simpa only [star_mul', star_inner_matrix, Complex.star_def, Complex.conj_ofReal,
      mul_comm] using h
  obtain ⟨ξ, hξ, hξcoef⟩ := exists_vector_limit_of_inner_limits b
    (fun ε ↦ L (F ε) ψ) _ hplus
  obtain ⟨η, hη, hηcoef⟩ := exists_vector_limit_of_inner_limits b
    (fun ε ↦ L (F ε)ᴴ ψ) _ hminus
  have hcenterAdj : ⟪ψ, L Aᴴ ψ⟫_ℂ = 0 := by
    rw [inner_adjoint_matrix, hcenter, star_zero]
  have hground (i : n) (hi : hH.eigenvalues i = E₀) : b i ∈ groundSpace H E₀ :=
    eigenvectorBasis_mem_groundSpace hH hi
  refine ⟨ξ, η, hξ, hη, ?_, ?_⟩
  · apply norm_le_of_inner_coefficients_le b ξ (L A ψ) (Real.exp_pos _).le
    intro i
    by_cases hi : hH.eigenvalues i = E₀
    · have hz := centered_ground_line_inner_eq_zero hline A hcenter (hground i hi)
      rw [hξcoef, hz, mul_zero, norm_zero]
      positivity
    · have hω : Δ ≤ hH.eigenvalues i - E₀ := by
        have := (hgap i).resolve_left hi
        linarith
      rw [hξcoef, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (gaussianNegativeFrequencyCutoff_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_right
        (gaussianNegativeFrequencyCutoff_le_exp_of_gap hq hΔ hω) (norm_nonneg _)
  · apply norm_le_of_inner_coefficients_le b (L Aᴴ ψ - η) (L Aᴴ ψ) (Real.exp_pos _).le
    intro i
    by_cases hi : hH.eigenvalues i = E₀
    · have hz := centered_ground_line_inner_eq_zero hline Aᴴ hcenterAdj (hground i hi)
      have hzero : ⟪b i, L Aᴴ ψ - η⟫_ℂ = 0 := by
        simp only [inner_sub_right, hηcoef, hz, mul_zero, sub_zero]
      rw [hzero, norm_zero]
      positivity
    · have hω : E₀ - hH.eigenvalues i ≤ -Δ := by
        have := (hgap i).resolve_left hi
        linarith
      have hcoef : ⟪b i, L Aᴴ ψ - η⟫_ℂ =
          ((1 - gaussianNegativeFrequencyCutoff q Δ (E₀ - hH.eigenvalues i) : ℝ) : ℂ) *
            ⟪b i, L Aᴴ ψ⟫_ℂ := by
        rw [inner_sub_right, hηcoef]
        push_cast
        ring
      rw [hcoef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (abs_one_sub_gaussianNegativeFrequencyCutoff_le_exp_of_gap hq hΔ hω) (norm_nonneg _)

/-- For a centered first observable, the ground expectation of the commutator of the
regularized operator with `B` converges as `ε → 0⁺` to a number within
`2 e^{-q/2} ‖A‖ ‖B‖ ‖ψ‖²` of `⟨ψ, A B ψ⟩`. Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3,
equations (3.1)–(3.14), before using the Lieb–Robinson bound. -/
theorem exists_gaussianNegativeFrequency_ground_commutator_limit
    {q Δ : ℝ} (hq : 0 < q) (hΔ : 0 < Δ)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : IsGapped H E₀ Δ)
    {ψ : EuclideanSpace ℂ n} (hline : groundSpace H E₀ = Submodule.span ℂ {ψ})
    (A B : Matrix n n ℂ) (hcenter : ⟪ψ, L A ψ⟫_ℂ = 0) :
    ∃ z : ℂ,
      Tendsto (fun ε : ℝ ↦
        let F := gaussianNegativeFrequencyOperator (q / Δ ^ 2).toNNReal ε H A
        ⟪ψ, L (F * B - B * F) ψ⟫_ℂ)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 z) ∧
      ‖⟪ψ, L (A * B) ψ⟫_ℂ - z‖ ≤
        2 * Real.exp (-q / 2) * ‖A‖ * ‖B‖ * ‖ψ‖ ^ 2 := by
  have hψ : ψ ∈ groundSpace H E₀ := hline ▸ Submodule.mem_span_singleton_self ψ
  obtain ⟨ξ, η, hξ, hη, hsmall, herror⟩ :=
    exists_gaussianNegativeFrequency_ground_limits hq hΔ hH hgap hline A hcenter
  let z := ⟪η, L B ψ⟫_ℂ - ⟪L Bᴴ ψ, ξ⟫_ℂ
  have hmove (M : Matrix n n ℂ) (x y : EuclideanSpace ℂ n) :
      ⟪L Mᴴ x, y⟫_ℂ = ⟪x, L M y⟫_ℂ := by
    rw [← Matrix.star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  refine ⟨z, ?_, ?_⟩
  · have h := (hη.inner (𝕜 := ℂ) (tendsto_const_nhds (x := L B ψ))).sub
      ((tendsto_const_nhds (x := L Bᴴ ψ)).inner (𝕜 := ℂ) hξ)
    apply h.congr'
    exact Eventually.of_forall fun ε ↦ by
      dsimp only
      simp only [map_sub, map_mul, _root_.sub_apply, inner_sub_right,
        mul_apply_eq_comp, hmove]
  · have hnorm (M : Matrix n n ℂ) : ‖L M ψ‖ ≤ ‖M‖ * ‖ψ‖ :=
      Matrix.l2_opNorm_mulVec M ψ
    have hnormAdj (M : Matrix n n ℂ) : ‖L Mᴴ ψ‖ ≤ ‖M‖ * ‖ψ‖ := by
      simpa only [Matrix.l2_opNorm_conjTranspose] using hnorm Mᴴ
    have hid : ⟪ψ, L (A * B) ψ⟫_ℂ - z =
        ⟪L Aᴴ ψ - η, L B ψ⟫_ℂ + ⟪L Bᴴ ψ, ξ⟫_ℂ := by
      rw [map_mul, mul_apply_eq_comp,
        ← hmove A ψ (L B ψ), inner_sub_left]
      dsimp only [z]
      ring
    rw [hid]
    calc
      _ ≤ ‖⟪L Aᴴ ψ - η, L B ψ⟫_ℂ‖ + ‖⟪L Bᴴ ψ, ξ⟫_ℂ‖ := norm_add_le _ _
      _ ≤ ‖L Aᴴ ψ - η‖ * ‖L B ψ‖ + ‖L Bᴴ ψ‖ * ‖ξ‖ :=
        add_le_add (norm_inner_le_norm (𝕜 := ℂ) _ _) (norm_inner_le_norm (𝕜 := ℂ) _ _)
      _ ≤ (Real.exp (-q / 2) * ‖L Aᴴ ψ‖) * ‖L B ψ‖ +
          ‖L Bᴴ ψ‖ * (Real.exp (-q / 2) * ‖L A ψ‖) :=
        add_le_add (mul_le_mul_of_nonneg_right herror (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hsmall (norm_nonneg _))
      _ ≤ (Real.exp (-q / 2) * (‖A‖ * ‖ψ‖)) * (‖B‖ * ‖ψ‖) +
          (‖B‖ * ‖ψ‖) * (Real.exp (-q / 2) * (‖A‖ * ‖ψ‖)) := by
        have hexp := (Real.exp_pos (-q / 2)).le
        exact add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left (hnormAdj A) hexp) (hnorm B)
            (norm_nonneg _) (mul_nonneg hexp (mul_nonneg (norm_nonneg _) (norm_nonneg _))))
          (mul_le_mul (hnormAdj B) (mul_le_mul_of_nonneg_left (hnorm A) hexp)
            (mul_nonneg hexp (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ = _ := by ring

end ManyBody

end GroundLimits

section ConnectedCorrelation

open MeasureTheory ProbabilityTheory Matrix GaussianFilter Filter
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal Topology


namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "L" => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)

/-- For a centered first observable and a Lieb–Robinson commutator bound, the ground
correlation `⟨ψ, A B ψ⟩` is bounded by the Gaussian gap error `2 e^{-q/2} ‖A‖ ‖B‖` plus the
locality bound of the regularized operator, times `‖ψ‖²`.
Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3. -/
theorem norm_centered_ground_correlation_le_gaussian
    {q Δ T C v : ℝ} (hq : 0 < q) (hΔ : 0 < Δ) (hT : 0 < T)
    (hC : 0 ≤ C) (hv : 0 ≤ v)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : IsGapped H E₀ Δ)
    {ψ : EuclideanSpace ℂ n} (hline : groundSpace H E₀ = Submodule.span ℂ {ψ})
    (A B : Matrix n n ℂ) (hcenter : ⟪ψ, L A ψ⟫_ℂ = 0)
    (hLR : ∀ t : ℝ,
      ‖heisenbergEvolution H t A * B - B * heisenbergEvolution H t A‖ ≤
        C * (Real.exp (v * |t|) - 1)) :
    let h := (q / Δ ^ 2).toNNReal
    ‖⟪ψ, L (A * B) ψ⟫_ℂ‖ ≤
      (2 * Real.exp (-q / 2) * ‖A‖ * ‖B‖ +
        kernel h⁻¹ 0 * (C * v * Real.exp (v * T) +
          (2 * ‖A‖ * ‖B‖ / T) * Real.exp (-T ^ 2 / (2 * (h : ℝ))))) * ‖ψ‖ ^ 2 := by
  have hψ : ψ ∈ groundSpace H E₀ := hline ▸ Submodule.mem_span_singleton_self ψ
  let h := (q / Δ ^ 2).toNNReal
  let K := kernel h⁻¹ 0 * (C * v * Real.exp (v * T) +
    (2 * ‖A‖ * ‖B‖ / T) * Real.exp (-T ^ 2 / (2 * (h : ℝ))))
  obtain ⟨z, hlim, herror⟩ := exists_gaussianNegativeFrequency_ground_commutator_limit
    hq hΔ hH hgap hline A B hcenter
  have hpoint (ε : ℝ) (hε : 0 < ε) :
      let F := gaussianNegativeFrequencyOperator h ε H A
      ‖⟪ψ, L (F * B - B * F) ψ⟫_ℂ‖ ≤ K * ‖ψ‖ ^ 2 := by
    let F := gaussianNegativeFrequencyOperator h ε H A
    have hcomm : ‖F * B - B * F‖ ≤ K :=
      norm_commutator_gaussianNegativeFrequencyOperator_le h hH A B hε hT hC hv hLR
    have hnorm (M : Matrix n n ℂ) : ‖L M ψ‖ ≤ ‖M‖ * ‖ψ‖ :=
      Matrix.l2_opNorm_mulVec M ψ
    calc
      _ ≤ ‖ψ‖ * ‖L (F * B - B * F) ψ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ‖ * (‖F * B - B * F‖ * ‖ψ‖) :=
        mul_le_mul_of_nonneg_left (hnorm _) (norm_nonneg ψ)
      _ ≤ ‖ψ‖ * (K * ‖ψ‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcomm (norm_nonneg ψ)) (norm_nonneg ψ)
      _ = K * ‖ψ‖ ^ 2 := by ring
  have hz : ‖z‖ ≤ K * ‖ψ‖ ^ 2 := by
    apply le_of_tendsto hlim.norm
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hpoint ε hε
  calc
    _ = ‖(⟪ψ, L (A * B) ψ⟫_ℂ - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖⟪ψ, L (A * B) ψ⟫_ℂ - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ 2 * Real.exp (-q / 2) * ‖A‖ * ‖B‖ * ‖ψ‖ ^ 2 + K * ‖ψ‖ ^ 2 :=
      add_le_add herror hz
    _ = _ := by dsimp only [K]; ring

end ManyBody

end ConnectedCorrelation
