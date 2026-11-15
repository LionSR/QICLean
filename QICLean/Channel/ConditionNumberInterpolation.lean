/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceNormContractionCoefficient
import QICLean.Channel.SupportCompletion
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Completely positive interpolation and the condition number

For a square matrix $X$, Wolf writes $\kappa(X) = \|X\|_\infty \|X^{-1}\|_\infty$ for
its condition number. For positive definite $P \in M_d(\mathbb C)$ and
$P' \in M_{d'}(\mathbb C)$ there is a completely positive unital map
$T : M_d(\mathbb C) \to M_{d'}(\mathbb C)$ with $T(P) = \lambda P'$ for some
$\lambda > 0$ if and only if $\kappa(P) \ge \kappa(P')$. This is Wolf's Lemma
(8.93).

## Operator-norm facts

For positive definite $A$ in positive dimension, `‖A‖` is the largest
eigenvalue and `‖A⁻¹‖⁻¹` the smallest, with unit eigenvectors attaining both,
and $\|A^{-1}\|^{-1}\mathbf 1 \le A \le \|A\|\mathbf 1$. Both follow from the
C⋆-algebra facts that the norm of a positive element lies in its spectrum and
dominates it.

## Construction

When $\kappa(P) \ge \kappa(P')$ and $P$ is not a multiple of the identity, write
$M = \|P\|$, $m = \|P^{-1}\|^{-1}$, $\lambda = \|P\| / \|P'\|$, and let $\psi_1$,
$\psi_2$ be unit eigenvectors of $P$ for $m$ and $M$. Wolf's map (8.95) is
$$T(X) = \langle \psi_1 | X | \psi_1\rangle \frac{M\mathbf 1 - \lambda P'}{M - m}
       + \langle \psi_2 | X | \psi_2\rangle \frac{\lambda P' - m\mathbf 1}{M - m},$$
which is Wolf's
$E_i(\lambda P') / \langle\psi_i|E_i(P)|\psi_i\rangle$ written out, since
$E_1(X) = \mathbf 1 - X/M$ gives $\langle\psi_1|E_1(P)|\psi_1\rangle = (M - m)/M$
and $E_2(X) = X - m\mathbf 1$ gives $\langle\psi_2|E_2(P)|\psi_2\rangle = M - m$.
Each summand is a rank-one compression followed by preparation of a positive
semidefinite matrix, so $T$ is completely positive. When $P = M\mathbf 1$ the
hypothesis forces $P' = \|P'\|\mathbf 1$ and $X \mapsto \langle\psi|X|\psi\rangle\mathbf 1$
works.

## Main results

* `Matrix.conditionNumber` — Wolf's $\kappa(X) = \|X\|_\infty\|X^{-1}\|_\infty$.
* `Matrix.exists_isKrausCP_unital_map_smul_iff_conditionNumber_le` — Wolf's
  Lemma (8.93).

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour* (July 5, 2012),
Chapter 8, Lemma before Eq. (8.93) and its proof, Eqs. (8.93)–(8.95);
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1045–1072.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

/-- **Condition number** $\kappa(X) = \|X\|_\infty \|X^{-1}\|_\infty$, with the
operator norm and the matrix inverse.

`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, line 1046. -/
def conditionNumber {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) : ℝ :=
  ‖X‖ * ‖X⁻¹‖

variable {d d' : ℕ}

/-! ### Quadratic forms -/

/-- The Loewner order is monotone in every quadratic form. -/
lemma dotProduct_mulVec_le_of_le {X Y : Matrix (Fin d) (Fin d) ℂ} (h : X ≤ Y)
    (ψ : Fin d → ℂ) : star ψ ⬝ᵥ (X *ᵥ ψ) ≤ star ψ ⬝ᵥ (Y *ᵥ ψ) := by
  have := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg ψ
  rwa [sub_mulVec, dotProduct_sub, sub_nonneg] at this

/-- The quadratic form of a unit eigenvector is its eigenvalue. -/
lemma dotProduct_mulVec_of_mulVec_eq {X : Matrix (Fin d) (Fin d) ℂ} {ψ : Fin d → ℂ}
    (hψ : IsUnitVector ψ) {c : ℂ} (hX : X *ᵥ ψ = c • ψ) :
    star ψ ⬝ᵥ (X *ᵥ ψ) = c := by
  rw [hX, dotProduct_smul, smul_eq_mul]
  have : star ψ ⬝ᵥ ψ = 1 := hψ
  rw [this, mul_one]

/-- The quadratic form of a unit vector at a real multiple of the identity. -/
lemma dotProduct_mulVec_smul_one {ψ : Fin d → ℂ} (hψ : IsUnitVector ψ) (r : ℝ) :
    star ψ ⬝ᵥ ((r • (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ ψ) = r := by
  apply dotProduct_mulVec_of_mulVec_eq hψ
  rw [smul_mulVec, one_mulVec, ← Complex.coe_smul]

/-! ### Extremal eigenvalues through operator norms -/

/-- A Hermitian matrix is dominated by its operator norm times the identity. -/
lemma IsHermitian.le_norm_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : A ≤ ‖A‖ • (1 : Matrix n n ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact IsSelfAdjoint.le_algebraMap_norm_self A hA.isSelfAdjoint

/-- A Hermitian matrix dominates `c 𝟙` whenever `c` is at most every eigenvalue. -/
lemma IsHermitian.smul_one_le_of_le_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {c : ℝ} (hc : ∀ i, c ≤ hA.eigenvalues i) :
    c • (1 : Matrix n n ℂ) ≤ A := by
  rw [← Algebra.algebraMap_eq_smul_one, algebraMap_le_iff_le_spectrum (a := A) hA.isSelfAdjoint]
  intro x hx
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hc i

/-- The eigenvectors of a Hermitian matrix are unit vectors. -/
lemma IsHermitian.isUnitVector_eigenvectorBasis {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (i : Fin d) : IsUnitVector ⇑(hA.eigenvectorBasis i) :=
  eigenvectorUnitary_isUnitVector hA i

/-- A positive semidefinite matrix in positive dimension has a unit eigenvector
with eigenvalue its operator norm. -/
lemma PosSemidef.exists_isUnitVector_mulVec_eq_norm_smul [NeZero d]
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) :
    ∃ ψ : Fin d → ℂ, IsUnitVector ψ ∧ A *ᵥ ψ = (‖A‖ : ℂ) • ψ := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hmem := CStarAlgebra.norm_mem_spectrum_of_nonneg A hA.nonneg
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨i, hi⟩ := hmem
  refine ⟨_, hA.isHermitian.isUnitVector_eigenvectorBasis i, ?_⟩
  rw [hA.isHermitian.mulVec_eigenvectorBasis, hi, Complex.coe_smul]

/-- For a positive definite matrix in positive dimension, `‖A⁻¹‖⁻¹` is a positive
eigenvalue with a unit eigenvector, and `‖A⁻¹‖⁻¹ 𝟙 ≤ A`. -/
lemma PosDef.inv_norm_inv_spec [NeZero d] {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosDef) :
    0 < ‖A⁻¹‖⁻¹ ∧ ‖A⁻¹‖⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) ≤ A ∧
      ∃ ψ : Fin d → ℂ, IsUnitVector ψ ∧ A *ᵥ ψ = ((‖A⁻¹‖⁻¹ : ℝ) : ℂ) • ψ := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  obtain ⟨w, hw, hAw⟩ := hA.inv.posSemidef.exists_isUnitVector_mulVec_eq_norm_smul
  set N : ℝ := ‖A⁻¹‖ with hN
  -- `N` is positive: it is the quadratic form of the positive definite `A⁻¹` at `w`.
  have hNpos : 0 < N := by
    have hw0 : w ≠ 0 := by
      rintro rfl
      have : star (0 : Fin d → ℂ) ⬝ᵥ (0 : Fin d → ℂ) = 1 := hw
      simp at this
    have hpos := hA.inv.dotProduct_mulVec_pos hw0
    rw [dotProduct_mulVec_of_mulVec_eq hw hAw] at hpos
    exact_mod_cast hpos
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  refine ⟨inv_pos.mpr hNpos, ?_, w, hw, ?_⟩
  · apply hA.isHermitian.smul_one_le_of_le_eigenvalues
    intro k
    set v : Fin d → ℂ := ⇑(hA.isHermitian.eigenvectorBasis k)
    set μ : ℝ := hA.isHermitian.eigenvalues k
    have hμ : 0 < μ := hA.eigenvalues_pos k
    have hAv : A *ᵥ v = (μ : ℂ) • v := by
      rw [hA.isHermitian.mulVec_eigenvectorBasis, Complex.coe_smul]
    have hAinvv : A⁻¹ *ᵥ v = ((μ⁻¹ : ℝ) : ℂ) • v := by
      have h1 : A⁻¹ *ᵥ (A *ᵥ v) = v := by rw [mulVec_mulVec, hAinvA, one_mulVec]
      rw [hAv, mulVec_smul] at h1
      have hμne : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
      calc A⁻¹ *ᵥ v = ((μ : ℂ)⁻¹ * μ) • (A⁻¹ *ᵥ v) := by
            rw [inv_mul_cancel₀ hμne, one_smul]
        _ = (μ : ℂ)⁻¹ • ((μ : ℂ) • (A⁻¹ *ᵥ v)) := by rw [smul_smul]
        _ = ((μ⁻¹ : ℝ) : ℂ) • v := by rw [h1]; push_cast; rfl
    have hle := dotProduct_mulVec_le_of_le hA.inv.isHermitian.le_norm_smul_one v
    rw [dotProduct_mulVec_of_mulVec_eq (hA.isHermitian.isUnitVector_eigenvectorBasis k) hAinvv,
      dotProduct_mulVec_smul_one (hA.isHermitian.isUnitVector_eigenvectorBasis k),
      Complex.real_le_real] at hle
    exact (inv_le_comm₀ hμ hNpos).mp hle
  · have h1 : A *ᵥ (A⁻¹ *ᵥ w) = w := by rw [mulVec_mulVec, hAAinv, one_mulVec]
    rw [hAw, mulVec_smul] at h1
    have h2 : A *ᵥ w = (N : ℂ)⁻¹ • w := by
      rw [← h1, smul_smul, inv_mul_cancel₀ hNne, one_smul, h1]
    rw [h2]
    push_cast
    rfl

/-! ### Rank-one measure-and-prepare maps -/

/-- The trace of the compression by `|ψ⟩⟨ψ|` is the quadratic form of `ψ`. -/
lemma trace_singleKrausMap_pureStateProj {ψ : Fin d → ℂ} (hψ : IsUnitVector ψ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    (singleKrausMap (pureStateProj ψ) X).trace = star ψ ⬝ᵥ (X *ᵥ ψ) := by
  have hunit : star ψ ⬝ᵥ ψ = 1 := hψ
  have hherm : (pureStateProj ψ)ᴴ = pureStateProj ψ := by
    rw [pureStateProj, conjTranspose_vecMulVec]
    congr 1
    ext p
    simp
  have hidem : pureStateProj ψ * pureStateProj ψ = pureStateProj ψ := by
    rw [pureStateProj, vecMulVec_mul_vecMulVec,
      show (fun p => star (ψ p)) ⬝ᵥ ψ = 1 from hunit, one_smul]
  rw [singleKrausMap_apply, hherm, Matrix.trace_mul_cycle, hidem, pureStateProj,
    vecMulVec_mul, trace_vecMulVec, dotProduct_comm, ← dotProduct_mulVec]
  rfl

/-- The measure-and-prepare map `X ↦ ⟨ψ|X|ψ⟩ Q`. -/
def measurePrepareMap (ψ : Fin d → ℂ) (Q : Matrix (Fin d') (Fin d') ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ :=
  (tracePrepareMap Q).comp (singleKrausMap (pureStateProj ψ))

lemma measurePrepareMap_apply {ψ : Fin d → ℂ} (hψ : IsUnitVector ψ)
    (Q : Matrix (Fin d') (Fin d') ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    measurePrepareMap ψ Q X = (star ψ ⬝ᵥ (X *ᵥ ψ)) • Q := by
  rw [measurePrepareMap, LinearMap.comp_apply, tracePrepareMap_apply,
    trace_singleKrausMap_pureStateProj hψ]

lemma measurePrepareMap_isKrausCP (ψ : Fin d → ℂ) {Q : Matrix (Fin d') (Fin d') ℂ}
    (hQ : Q.PosSemidef) : IsKrausCP (measurePrepareMap ψ Q) :=
  isKrausCP_comp (singleKrausMap_isKrausCP _) (tracePrepareMap_isKrausCP Q hQ)

/-! ### Wolf's Lemma (8.93) -/

/-- A real multiple of a matrix with eigenvector `ψ` has the scaled eigenvalue. -/
private lemma real_smul_mulVec_eq {X : Matrix (Fin d) (Fin d) ℂ} {ψ : Fin d → ℂ} {c : ℝ}
    (hX : X *ᵥ ψ = (c : ℂ) • ψ) (r : ℝ) : (r • X) *ᵥ ψ = ((r * c : ℝ) : ℂ) • ψ := by
  rw [smul_mulVec, hX, ← Complex.coe_smul, smul_smul]
  push_cast
  rfl

/-- Real form of a quadratic-form inequality between real values. -/
private lemma real_le_of_dotProduct {X Y : Matrix (Fin d) (Fin d) ℂ} (h : X ≤ Y)
    {ψ : Fin d → ℂ} {x y : ℝ} (hx : star ψ ⬝ᵥ (X *ᵥ ψ) = x)
    (hy : star ψ ⬝ᵥ (Y *ᵥ ψ) = y) : x ≤ y := by
  have := dotProduct_mulVec_le_of_le h ψ
  rw [hx, hy] at this
  exact_mod_cast this

/-- **Only-if direction of Wolf's Lemma (8.93)**, for positive unital maps.

`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1069–1071. -/
theorem conditionNumber_le_of_positive_unital_map_smul
    {P : Matrix (Fin d) (Fin d) ℂ} {P' : Matrix (Fin d') (Fin d') ℂ}
    (hP : P.PosDef) (hP' : P'.PosDef)
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hpos : ∀ X, X.PosSemidef → (T X).PosSemidef) (hunital : T 1 = 1)
    {lam : ℝ} (hlam : 0 < lam) (hTP : T P = lam • P') :
    conditionNumber P' ≤ conditionNumber P := by
  rcases Nat.eq_zero_or_pos d' with hd' | hd'
  · subst hd'
    have h0 : (P' : Matrix (Fin 0) (Fin 0) ℂ) = 0 := Subsingleton.elim _ _
    have h0' : (P'⁻¹ : Matrix (Fin 0) (Fin 0) ℂ) = 0 := Subsingleton.elim _ _
    simp only [conditionNumber, h0, norm_zero, zero_mul]
    positivity
  have : NeZero d' := ⟨hd'.ne'⟩
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exfalso
    have h1 : (1 : Matrix (Fin 0) (Fin 0) ℂ) = 0 := Subsingleton.elim _ _
    rw [h1, map_zero] at hunital
    have : (1 : Matrix (Fin d') (Fin d') ℂ) ≠ 0 := by
      have : Nonempty (Fin d') := ⟨⟨0, hd'⟩⟩
      exact one_ne_zero
    exact this hunital.symm
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨hm, hmP, -⟩ := hP.inv_norm_inv_spec
  obtain ⟨hm', -, w', hw', hP'w'⟩ := hP'.inv_norm_inv_spec
  obtain ⟨w, hw, hP'w⟩ := hP'.posSemidef.exists_isUnitVector_mulVec_eq_norm_smul
  set M : ℝ := ‖P‖
  set m : ℝ := ‖P⁻¹‖⁻¹
  set M' : ℝ := ‖P'‖
  set m' : ℝ := ‖P'⁻¹‖⁻¹
  have hMm : m ≤ M := by
    obtain ⟨ψ, hψ, hPψ⟩ := hP.posSemidef.exists_isUnitVector_mulVec_eq_norm_smul
    exact real_le_of_dotProduct hmP (dotProduct_mulVec_smul_one hψ m)
      (dotProduct_mulVec_of_mulVec_eq hψ hPψ)
  have hM : 0 < M := hm.trans_le hMm
  -- `T (𝟙 - P / M) ≥ 0` gives `λ M' ≤ M`.
  have hE1 : lam / M * M' ≤ 1 := by
    have hE : M⁻¹ • P ≤ (1 : Matrix (Fin d) (Fin d) ℂ) :=
      calc M⁻¹ • P ≤ M⁻¹ • (M • (1 : Matrix (Fin d) (Fin d) ℂ)) :=
            smul_le_smul_of_nonneg_left hP.isHermitian.le_norm_smul_one (inv_nonneg.mpr hM.le)
        _ = 1 := by rw [smul_smul, inv_mul_cancel₀ hM.ne', one_smul]
    have hTE := hpos _ (Matrix.le_iff.mp hE)
    rw [map_sub, hunital, LinearMap.map_smul_of_tower, hTP, smul_smul,
      ← Matrix.le_iff, ← div_eq_inv_mul] at hTE
    exact real_le_of_dotProduct hTE
      (dotProduct_mulVec_of_mulVec_eq hw (real_smul_mulVec_eq hP'w _))
      (dotProduct_mulVec_of_mulVec_eq hw (by rw [one_mulVec]; simp))
  -- `T (P - m 𝟙) ≥ 0` gives `m ≤ λ m'`.
  have hE2 : m ≤ lam * m' := by
    have hTE := hpos _ (Matrix.le_iff.mp hmP)
    rw [map_sub, LinearMap.map_smul_of_tower, hunital, hTP, ← Matrix.le_iff] at hTE
    exact real_le_of_dotProduct hTE (dotProduct_mulVec_smul_one hw' m)
      (dotProduct_mulVec_of_mulVec_eq hw' (real_smul_mulVec_eq hP'w' _))
  have hM'le : M' ≤ M / lam := by
    rw [le_div_iff₀ hlam]
    have := hE1
    rw [div_mul_eq_mul_div, div_le_one hM] at this
    linarith
  have hmle : m / lam ≤ m' := by rw [div_le_iff₀ hlam]; linarith
  -- Assemble `κ(P') = M' / m' ≤ (M / λ) / (m / λ) = κ(P)`.
  have hκP : conditionNumber P = M / m := by
    simp only [conditionNumber, M, m, div_inv_eq_mul]
  have hκP' : conditionNumber P' = M' / m' := by
    simp only [conditionNumber, M', m', div_inv_eq_mul]
  rw [hκP, hκP']
  calc M' / m' ≤ (M / lam) / (m / lam) :=
        div_le_div₀ (div_nonneg hM.le hlam.le) hM'le (div_pos hm hlam) hmle
    _ = M / m := by field_simp

/-- **Wolf's Lemma (8.93)**: completely positive unital interpolation.

Let $P \in M_d(\mathbb C)$ and $P' \in M_{d'}(\mathbb C)$ be positive definite. There is
a completely positive unital linear map $T : M_d(\mathbb C) \to M_{d'}(\mathbb C)$ with
$T(P) = \lambda P'$ for some $\lambda > 0$ if and only if
$\kappa(P) \ge \kappa(P')$, where $\kappa(X) = \|X\|_\infty \|X^{-1}\|_\infty$.

`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1045–1072. -/
theorem exists_isKrausCP_unital_map_smul_iff_conditionNumber_le
    {P : Matrix (Fin d) (Fin d) ℂ} {P' : Matrix (Fin d') (Fin d') ℂ}
    (hP : P.PosDef) (hP' : P'.PosDef) :
    (∃ T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ,
        IsKrausCP T ∧ T 1 = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ T P = lam • P') ↔
      conditionNumber P' ≤ conditionNumber P := by
  constructor
  · rintro ⟨T, hT, hunital, lam, hlam, hTP⟩
    exact conditionNumber_le_of_positive_unital_map_smul hP hP'
      (fun X hX => hT.map_posSemidef hX) hunital hlam hTP
  intro hκ
  rcases Nat.eq_zero_or_pos d' with hd' | hd'
  · subst hd'
    exact ⟨0, ⟨0, Fin.elim0, fun X => Subsingleton.elim _ _⟩, Subsingleton.elim _ _,
      1, one_pos, Subsingleton.elim _ _⟩
  have : NeZero d' := ⟨hd'.ne'⟩
  obtain ⟨hm', hm'P', -⟩ := hP'.inv_norm_inv_spec
  have hP'M' : P' ≤ ‖P'‖ • (1 : Matrix (Fin d') (Fin d') ℂ) := hP'.isHermitian.le_norm_smul_one
  set M' : ℝ := ‖P'‖
  set m' : ℝ := ‖P'⁻¹‖⁻¹
  have hm'M' : m' ≤ M' := by
    obtain ⟨ψ, hψ, hPψ⟩ := hP'.posSemidef.exists_isUnitVector_mulVec_eq_norm_smul
    exact real_le_of_dotProduct hm'P' (dotProduct_mulVec_smul_one hψ m')
      (dotProduct_mulVec_of_mulVec_eq hψ hPψ)
  have hM' : 0 < M' := hm'.trans_le hm'M'
  have hκP' : conditionNumber P' = M' / m' := by
    simp only [conditionNumber, M', m', div_inv_eq_mul]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · exfalso
    subst hd
    have h0 : conditionNumber P = 0 := by
      have : (P : Matrix (Fin 0) (Fin 0) ℂ) = 0 := Subsingleton.elim _ _
      simp [conditionNumber, this]
    rw [h0, hκP'] at hκ
    exact absurd hκ (not_le.mpr (div_pos hM' hm'))
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨hm, hmP, ψ₁, hψ₁, hPψ₁⟩ := hP.inv_norm_inv_spec
  obtain ⟨ψ₂, hψ₂, hPψ₂⟩ := hP.posSemidef.exists_isUnitVector_mulVec_eq_norm_smul
  have hPM : P ≤ ‖P‖ • (1 : Matrix (Fin d) (Fin d) ℂ) := hP.isHermitian.le_norm_smul_one
  set M : ℝ := ‖P‖
  set m : ℝ := ‖P⁻¹‖⁻¹
  have hmM : m ≤ M := real_le_of_dotProduct hmP (dotProduct_mulVec_smul_one hψ₂ m)
    (dotProduct_mulVec_of_mulVec_eq hψ₂ hPψ₂)
  have hM : 0 < M := hm.trans_le hmM
  have hκP : conditionNumber P = M / m := by
    simp only [conditionNumber, M, m, div_inv_eq_mul]
  rw [hκP, hκP', div_le_div_iff₀ hm' hm] at hκ
  set lam : ℝ := M / M' with hlam_def
  have hlam : 0 < lam := div_pos hM hM'
  rcases hmM.lt_or_eq with hlt | heq
  · -- Wolf's construction (8.95).
    set c : ℝ := (M - m)⁻¹
    have hc : 0 < c := inv_pos.mpr (sub_pos.mpr hlt)
    set Q₁ : Matrix (Fin d') (Fin d') ℂ := c • (M • 1 - lam • P')
    set Q₂ : Matrix (Fin d') (Fin d') ℂ := c • (lam • P' - m • 1)
    have hQ₁ : Q₁.PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]
      refine smul_nonneg hc.le (sub_nonneg.mpr ?_)
      calc lam • P' ≤ lam • (M' • (1 : Matrix (Fin d') (Fin d') ℂ)) :=
            smul_le_smul_of_nonneg_left hP'M' hlam.le
        _ = M • 1 := by rw [smul_smul, hlam_def, div_mul_cancel₀ _ hM'.ne']
    have hQ₂ : Q₂.PosSemidef := by
      rw [← Matrix.nonneg_iff_posSemidef]
      refine smul_nonneg hc.le (sub_nonneg.mpr ?_)
      have hmlm : m ≤ lam * m' := by
        rw [hlam_def, div_mul_eq_mul_div, le_div_iff₀ hM']
        linarith
      calc m • (1 : Matrix (Fin d') (Fin d') ℂ) ≤ (lam * m') • 1 :=
            smul_le_smul_of_nonneg_right hmlm zero_le_one
        _ = lam • (m' • 1) := by rw [smul_smul]
        _ ≤ lam • P' := smul_le_smul_of_nonneg_left hm'P' hlam.le
    refine ⟨measurePrepareMap ψ₁ Q₁ + measurePrepareMap ψ₂ Q₂,
      (measurePrepareMap_isKrausCP ψ₁ hQ₁).add (measurePrepareMap_isKrausCP ψ₂ hQ₂),
      ?_, lam, hlam, ?_⟩
    · rw [LinearMap.add_apply, measurePrepareMap_apply hψ₁, measurePrepareMap_apply hψ₂,
        one_mulVec, one_mulVec, show star ψ₁ ⬝ᵥ ψ₁ = 1 from hψ₁,
        show star ψ₂ ⬝ᵥ ψ₂ = 1 from hψ₂, one_smul, one_smul, ← smul_add,
        sub_add_sub_cancel, ← sub_smul]
      rw [smul_smul, inv_mul_cancel₀ (sub_pos.mpr hlt).ne', one_smul]
    · rw [LinearMap.add_apply, measurePrepareMap_apply hψ₁, measurePrepareMap_apply hψ₂,
        dotProduct_mulVec_of_mulVec_eq hψ₁ hPψ₁, dotProduct_mulVec_of_mulVec_eq hψ₂ hPψ₂]
      ext i j
      simp only [Q₁, Q₂, c, add_apply, smul_apply, sub_apply, one_apply, smul_eq_mul,
        Complex.real_smul]
      have hne : ((M - m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hlt).ne'
      push_cast at hne ⊢
      field_simp
      ring
  · -- `P = M 𝟙`, hence `P' = M' 𝟙`.
    have hPeq : P = M • (1 : Matrix (Fin d) (Fin d) ℂ) :=
      le_antisymm hPM (heq ▸ hmP)
    have hM'm' : M' ≤ m' := by
      rw [heq] at hκ
      have := hκ
      nlinarith
    have hP'eq : P' = M' • (1 : Matrix (Fin d') (Fin d') ℂ) :=
      le_antisymm hP'M' ((le_antisymm hm'M' hM'm') ▸ hm'P')
    refine ⟨measurePrepareMap ψ₂ 1,
      measurePrepareMap_isKrausCP ψ₂ Matrix.PosSemidef.one, ?_, lam, hlam, ?_⟩
    · rw [measurePrepareMap_apply hψ₂, one_mulVec, show star ψ₂ ⬝ᵥ ψ₂ = 1 from hψ₂,
        one_smul]
    · rw [measurePrepareMap_apply hψ₂, dotProduct_mulVec_of_mulVec_eq hψ₂ hPψ₂, hP'eq,
        smul_smul, hlam_def, div_mul_cancel₀ _ hM'.ne', Complex.coe_smul]

end Matrix
