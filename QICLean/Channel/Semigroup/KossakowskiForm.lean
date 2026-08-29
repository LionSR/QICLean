/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixOperatorSpace
import QICLean.Channel.Semigroup.LindbladForm

/-!
# Kossakowski Matrix Form — Wolf Theorem 7.1, Equation (7.23)

This file defines the Kossakowski matrix form of a quantum dynamical semigroup
generator (Wolf Equation 7.23) and proves its equivalence with the Lindblad form.

## Main definitions

* `TracelessBasisKossakowskiForm` — Wolf's Kossakowski data in a fixed basis
  of the traceless matrices, with a positive semidefinite Kossakowski matrix.
* `KossakowskiForm` — the algebraic variant for an arbitrary finite family:
  `L(ρ) = i[ρ,H] + ½ Σ_{k,l} C_{lk} ([F_k, ρ F_l†] + [F_k ρ, F_l†])`.

## Main results

* `gksl_iff_tracelessBasisKossakowskiForm` — Wolf's Theorem 7.1,
  Equation (7.23), at the source-facing basis-level boundary.
* `kossakowski_iff_lindblad` — algebraic Kossakowski ↔ Lindblad conversion.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 7.1.2, Theorem 7.1, Equation 7.23]
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder TNOperatorSpace
open Matrix TNLean

noncomputable section

variable {D : ℕ}

section KossakowskiForms

/-! ## Wolf Theorem 7.1: Kossakowski matrix form (Equation 7.23) -/

/-- The complex linear subspace of traceless matrices in `M_D(ℂ)`.

This is the space spanned by `F₁, …, F_{D²-1}` in Wolf, Theorem 7.1,
Equation (7.23). -/
def tracelessMatrixSubspace (D : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin D) ℂ ℂ)

/-- The space of traceless `D × D` matrices has dimension `D² - 1`, as used
in Wolf, Theorem 7.1, Equation (7.23). -/
theorem finrank_tracelessMatrixSubspace :
    Module.finrank ℂ (tracelessMatrixSubspace D) = D ^ 2 - 1 := by
  by_cases hD : D = 0
  · subst D
    simpa using
      (Module.finrank_eq_zero_of_subsingleton ℂ (tracelessMatrixSubspace 0))
  · let _ : NeZero D := ⟨hD⟩
    let τ := Matrix.traceLinearMap (Fin D) ℂ ℂ
    have hfin_mat : Module.finrank ℂ (Matrix (Fin D) (Fin D) ℂ) = D * D := by
      simp [Module.finrank_matrix, Fintype.card_fin]
    have hD_ne : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD
    have htrI : τ (1 : Matrix (Fin D) (Fin D) ℂ) = (D : ℂ) := by
      change Matrix.trace (1 : Matrix (Fin D) (Fin D) ℂ) = _
      simp [Matrix.trace_one, Fintype.card_fin]
    have h_rn := τ.finrank_range_add_finrank_ker
    rw [hfin_mat] at h_rn
    have h_range : Module.finrank ℂ (LinearMap.range τ) = 1 := by
      have hrange_top : LinearMap.range τ = ⊤ := by
        rw [LinearMap.range_eq_top]
        intro c
        refine ⟨(c / (D : ℂ)) • (1 : Matrix (Fin D) (Fin D) ℂ), ?_⟩
        rw [map_smul, htrI, smul_eq_mul, div_mul_cancel₀ c hD_ne]
      rw [hrange_top, finrank_top]
      exact Module.finrank_self ℂ
    rw [h_range] at h_rn
    change Module.finrank ℂ (LinearMap.ker τ) = D ^ 2 - 1
    simp only [Nat.pow_two]
    omega

/-- The **Kossakowski form** of a generator (Wolf Equation 7.23):
`L(ρ) = i[ρ,H] + ½ Σ_{k,l} C_{lk} ([F_k, ρ F_l†] + [F_k ρ, F_l†])`
where `C ≥ 0` is the Kossakowski matrix and `F` is the chosen family of
matrices. In the paper this family is a basis of traceless matrices; the
current structure states only the data used in the algebraic conversion to
Lindblad form. -/
structure KossakowskiForm (D : ℕ) where
  /-- The number of matrices in the chosen family `F`. -/
  n : ℕ
  /-- The Hamiltonian (must be Hermitian). -/
  H : Matrix (Fin D) (Fin D) ℂ
  /-- The family of matrices appearing in the Kossakowski sum. -/
  F : Fin n → Matrix (Fin D) (Fin D) ℂ
  /-- The Kossakowski matrix (must be PSD). -/
  C : Matrix (Fin n) (Fin n) ℂ
  /-- Hermiticity of H. -/
  H_hermitian : H.IsHermitian
  /-- PSD of C. -/
  C_posSemidef : C.PosSemidef

/-- The source-facing Kossakowski data of Wolf, Theorem 7.1, Equation (7.23).
The family `F₁, …, F_{D²-1}` is a basis of the traceless matrices, and
`C` is the positive semidefinite Kossakowski matrix in that fixed basis. -/
structure TracelessBasisKossakowskiForm (D : ℕ) where
  /-- The Hamiltonian `H`. -/
  H : Matrix (Fin D) (Fin D) ℂ
  /-- The fixed basis `F₁, …, F_{D²-1}` of the traceless matrices. -/
  F : Module.Basis (Fin (D ^ 2 - 1)) ℂ (tracelessMatrixSubspace D)
  /-- The Kossakowski matrix `C` in the basis `F`. -/
  C : Matrix (Fin (D ^ 2 - 1)) (Fin (D ^ 2 - 1)) ℂ
  /-- The Hamiltonian is Hermitian. -/
  H_hermitian : H.IsHermitian
  /-- The Kossakowski matrix is positive semidefinite. -/
  C_posSemidef : C.PosSemidef

/-- Forgetting that `F` is a basis of traceless matrices gives the algebraic
Kossakowski form with the same `H`, `F`, and `C`. -/
def TracelessBasisKossakowskiForm.toKossakowskiForm
    (K : TracelessBasisKossakowskiForm D) : KossakowskiForm D where
  n := D ^ 2 - 1
  H := K.H
  F := fun k ↦ K.F k
  C := K.C
  H_hermitian := K.H_hermitian
  C_posSemidef := K.C_posSemidef

/-- A single summand in the dissipative part of a Kossakowski form. -/
private def kossakowskiTerm (K : KossakowskiForm D) (k l : Fin K.n)
    (ρ : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  K.C l k • (
    (K.F k * ρ * (K.F l)ᴴ - (K.F l)ᴴ * K.F k * ρ) +
    (K.F k * ρ * (K.F l)ᴴ - ρ * (K.F l)ᴴ * K.F k))

private lemma kossakowskiTerm_add (K : KossakowskiForm D)
    (k l : Fin K.n) (ρ σ : Matrix (Fin D) (Fin D) ℂ) :
    kossakowskiTerm K k l (ρ + σ) =
      kossakowskiTerm K k l ρ + kossakowskiTerm K k l σ := by
  simp only [kossakowskiTerm, mul_add, add_mul, smul_add, smul_sub]
  abel

private lemma kossakowskiTerm_smul (K : KossakowskiForm D)
    (k l : Fin K.n) (c : ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    kossakowskiTerm K k l (c • ρ) = c • kossakowskiTerm K k l ρ := by
  simp only [kossakowskiTerm, mul_smul_comm, smul_mul_assoc, smul_add,
    smul_sub, smul_smul]
  rw [mul_comm]

/-- The dissipative part of a Kossakowski form. -/
private def kossakowskiDissipator (K : KossakowskiForm D)
    (ρ : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  (1 / 2 : ℂ) • ∑ k : Fin K.n, ∑ l : Fin K.n, kossakowskiTerm K k l ρ

private lemma kossakowskiDissipator_add (K : KossakowskiForm D)
    (ρ σ : Matrix (Fin D) (Fin D) ℂ) :
    kossakowskiDissipator K (ρ + σ) =
      kossakowskiDissipator K ρ + kossakowskiDissipator K σ := by
  simp_rw [kossakowskiDissipator, kossakowskiTerm_add, Finset.sum_add_distrib]
  rw [smul_add]

private lemma kossakowskiDissipator_smul (K : KossakowskiForm D)
    (c : ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ) :
    kossakowskiDissipator K (c • ρ) = c • kossakowskiDissipator K ρ := by
  simp_rw [kossakowskiDissipator, kossakowskiTerm_smul, ← Finset.smul_sum]
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- The linear map defined by a Kossakowski form. -/
def KossakowskiForm.toLinearMap (K : KossakowskiForm D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun ρ :=
    Complex.I • (ρ * K.H - K.H * ρ) +
      kossakowskiDissipator K ρ
  map_add' ρ σ := by
    simp only [kossakowskiDissipator_add, mul_add, add_mul, smul_add, smul_sub]
    abel
  map_smul' c ρ := by
    simp only [RingHom.id_apply, kossakowskiDissipator_smul, mul_smul_comm,
      smul_mul_assoc, smul_sub]
    rw [smul_add, smul_sub]
    simp only [smul_smul]
    congr 1
    congr 1 <;> ring_nf

/-- The linear map in Wolf's basis-level Kossakowski form (Equation (7.23)). -/
def TracelessBasisKossakowskiForm.toLinearMap
    (K : TracelessBasisKossakowskiForm D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  K.toKossakowskiForm.toLinearMap

/-- The Lindblad form obtained from Wolf's factorization
`C = (sqrt C)ᴴ * sqrt C` in the chosen traceless basis.

Its Lindblad operators are
`Lⱼ = ∑ₖ (sqrt C)ⱼₖ Fₖ`, as in the proof of Wolf, Theorem 7.1,
`Notes/WolfNoteTexSource/ch07_semigroup_structure.tex`, lines 258--263. -/
def TracelessBasisKossakowskiForm.sqrtLindbladForm
    (K : TracelessBasisKossakowskiForm D) : LindbladForm D where
  r := D ^ 2 - 1
  H := K.toKossakowskiForm.H
  L := fun j ↦ ∑ k, (CFC.sqrt K.C) j k • K.toKossakowskiForm.F k
  H_hermitian := K.toKossakowskiForm.H_hermitian

/-- The square-root Lindblad operators of a basis-level Kossakowski form are
traceless. -/
theorem TracelessBasisKossakowskiForm.sqrtLindbladForm_hasTracelessKraus
    (K : TracelessBasisKossakowskiForm D) :
    K.sqrtLindbladForm.HasTracelessKraus := by
  intro j
  simp only [TracelessBasisKossakowskiForm.sqrtLindbladForm,
    Matrix.trace_sum, Matrix.trace_smul]
  apply Finset.sum_eq_zero
  intro k _
  have hk : trace (K.F k : Matrix (Fin D) (Fin D) ℂ) = 0 := by
    exact (K.F k).property
  change (CFC.sqrt K.C) j k • trace (K.F k : Matrix (Fin D) (Fin D) ℂ) = 0
  rw [hk, smul_zero]

/-- Wolf's positive-semidefinite factorization of the Kossakowski matrix:
`C = (sqrt C)† * sqrt C`. -/
theorem TracelessBasisKossakowskiForm.C_eq_conjTranspose_sqrt_mul_sqrt
    (K : TracelessBasisKossakowskiForm D) :
    K.C = (CFC.sqrt K.C)ᴴ * CFC.sqrt K.C := by
  have hC_nonneg : 0 ≤ K.C :=
    Matrix.nonneg_iff_posSemidef.mpr K.C_posSemidef
  have hsqrt_psd : (CFC.sqrt K.C).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K.C)
  rw [hsqrt_psd.isHermitian.eq]
  simpa using (CFC.sqrt_mul_sqrt_self K.C hC_nonneg).symm

/-! ### Auxiliary lemmas for Kossakowski ↔ Lindblad conversion -/

/-- The dissipator equals ½ of the Kossakowski commutator sum
(for a single operator). This connects the two forms. -/
private lemma dissipator_eq_half_kossakowski
    (Lop ρ : Matrix (Fin D) (Fin D) ℂ) :
    dissipator Lop ρ = (1/2 : ℂ) • (
      (Lop * ρ * Lopᴴ - Lopᴴ * Lop * ρ) +
      (Lop * ρ * Lopᴴ - ρ * Lopᴴ * Lop)) := by
  simp only [dissipator]
  -- Align parenthesization: ρ*(L†*L) = ρ*L†*L
  rw [show ρ * (Lopᴴ * Lop) = ρ * Lopᴴ * Lop from
    (mul_assoc ρ Lopᴴ Lop).symm]
  -- Both sides now use left-associative products.
  -- This is a ℂ-module identity: a-(1/2)b-(1/2)c = (1/2)((a-b)+(a-c))
  module

/-- Bilinear sum identity: `Σⱼ (Σₖ B_{jk}•Fₖ) * M * (Σₖ B_{jk}•Fₖ)†`
equals `Σₖₗ (B†B)_{lk} • (Fₖ * M * Fₗ†)`. Used in Kossakowski ↔ Lindblad. -/
theorem kraus_sum_eq_double_sum {r n : ℕ}
    (B : Matrix (Fin r) (Fin n) ℂ)
    (F : Fin n → Matrix (Fin D) (Fin D) ℂ)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    ∑ j : Fin r, (∑ k, B j k • F k) * M * (∑ k, B j k • F k)ᴴ =
    ∑ k : Fin n, ∑ l : Fin n, (Bᴴ * B) l k • (F k * M * (F l)ᴴ) := by
  simp_rw [conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [← Finset.sum_smul]; congr 1
  simp [conjTranspose_apply, mul_apply, mul_comm]

/-- Adjoint variant: `Σⱼ Lⱼ†Lⱼ = Σₗ Σₖ (B†B)_{lk} • (Fₗ†Fₖ)`. -/
theorem adj_kraus_sum_eq_double_sum {r n : ℕ}
    (B : Matrix (Fin r) (Fin n) ℂ)
    (F : Fin n → Matrix (Fin D) (Fin D) ℂ) :
    ∑ j : Fin r, (∑ k, B j k • F k)ᴴ * (∑ k, B j k • F k) =
    ∑ l : Fin n, ∑ k : Fin n, (Bᴴ * B) l k • ((F l)ᴴ * F k) := by
  simp_rw [conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [← Finset.sum_smul]; congr 1

/-- A factorization `C = BᴴB` converts a Kossakowski form into the
corresponding Lindblad family `Lⱼ = ∑ₖ Bⱼₖ Fₖ`. -/
theorem KossakowskiForm.toLinearMap_eq_lindblad_of_factor
    {r : ℕ} (K : KossakowskiForm D)
    (B : Matrix (Fin r) (Fin K.n) ℂ)
    (hB : K.C = Bᴴ * B) :
    K.toLinearMap =
      (LindbladForm.mk r K.H (fun j ↦ ∑ k, B j k • K.F k) K.H_hermitian).toLinearMap := by
  ext1 ρ
  simp only [KossakowskiForm.toLinearMap, LindbladForm.toLinearMap,
    kossakowskiDissipator, kossakowskiTerm, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  simp_rw [dissipator_eq_half_kossakowski]
  rw [← Finset.smul_sum]
  congr 1
  have hLML : ∀ N : Matrix (Fin D) (Fin D) ℂ,
      ∑ j : Fin r, (∑ k, B j k • K.F k) * N * (∑ k, B j k • K.F k)ᴴ =
      ∑ k, ∑ l, K.C l k • (K.F k * N * (K.F l)ᴴ) :=
    fun N ↦ by
      rw [kraus_sum_eq_double_sum]
      simp_rw [hB]
  have hLtL : ∑ j : Fin r, (∑ k, B j k • K.F k)ᴴ * (∑ k, B j k • K.F k) =
      ∑ k, ∑ l, K.C l k • ((K.F l)ᴴ * K.F k) := by
    rw [adj_kraus_sum_eq_double_sum, Finset.sum_comm]
    simp_rw [hB]
  symm
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [hLML]
  rw [← Finset.sum_mul]
  simp_rw [mul_assoc ρ]
  rw [← Finset.mul_sum]
  rw [hLtL]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← smul_sub, ← smul_add]

/-- The basis-level Kossakowski form and its square-root Lindblad form define
the same generator. -/
theorem TracelessBasisKossakowskiForm.toLinearMap_eq_sqrtLindbladForm
    (K : TracelessBasisKossakowskiForm D) :
    K.toLinearMap = K.sqrtLindbladForm.toLinearMap := by
  let B : Matrix (Fin (D ^ 2 - 1)) (Fin (D ^ 2 - 1)) ℂ := CFC.sqrt K.C
  have hB : K.C = Bᴴ * B := by
    exact K.C_eq_conjTranspose_sqrt_mul_sqrt
  change K.toKossakowskiForm.toLinearMap =
    (LindbladForm.mk (D ^ 2 - 1) K.toKossakowskiForm.H
      (fun j ↦ ∑ k, B j k • K.toKossakowskiForm.F k)
      K.toKossakowskiForm.H_hermitian).toLinearMap
  exact K.toKossakowskiForm.toLinearMap_eq_lindblad_of_factor B hB

/-- The Kossakowski form is equivalent to the Lindblad form:
diagonalizing `C = M†M` converts between the two.
(Wolf proof of Theorem 7.1, last paragraph) -/
theorem kossakowski_iff_lindblad
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    (∃ K : KossakowskiForm D, L = K.toLinearMap) ↔
    (∃ F : LindbladForm D, L = F.toLinearMap) := by
  constructor
  · -- Forward: Kossakowski → Lindblad via `C = Bᴴ * B`
    rintro ⟨KF, hKF⟩
    let B : Matrix (Fin KF.n) (Fin KF.n) ℂ := CFC.sqrt KF.C
    have hB : KF.C = Bᴴ * B := by
      have hC_nonneg : 0 ≤ KF.C :=
        Matrix.nonneg_iff_posSemidef.mpr KF.C_posSemidef
      have hsqrt_psd : (CFC.sqrt KF.C).PosSemidef :=
        Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg KF.C)
      change KF.C = (CFC.sqrt KF.C)ᴴ * CFC.sqrt KF.C
      rw [hsqrt_psd.isHermitian.eq]
      simpa using (CFC.sqrt_mul_sqrt_self KF.C hC_nonneg).symm
    -- Define Lindblad operators: `Lⱼ = Σₖ B_{jk} • Fₖ`
    refine ⟨⟨KF.n, KF.H, fun j => ∑ k, B j k • KF.F k, KF.H_hermitian⟩, ?_⟩
    rw [hKF]
    exact KF.toLinearMap_eq_lindblad_of_factor B hB
  · -- Backward: Lindblad → Kossakowski (set C = 𝟙, F_k = L_k)
    rintro ⟨F, hF⟩
    refine ⟨⟨F.r, F.H, F.L, 1, F.H_hermitian,
      Matrix.PosSemidef.one⟩, ?_⟩
    rw [hF]
    -- Show LindbladForm.toLinearMap = KossakowskiForm.toLinearMap
    ext1 ρ
    simp only [LindbladForm.toLinearMap, KossakowskiForm.toLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk]
    -- Hamiltonian parts are identical
    congr 1
    -- Dissipative: convert dissipator to Kossakowski comm form
    simp_rw [dissipator_eq_half_kossakowski]
    -- LHS: Σ_j (1/2)•(comm terms for j,j)
    -- RHS: (1/2)•Σ_k Σ_l (𝟙 l k)•(comm terms for k,l)
    rw [← Finset.smul_sum]
    congr 1
    -- Collapse inner sum with identity matrix
    apply Finset.sum_congr rfl
    intro k _
    symm
    simp [kossakowskiTerm, Matrix.one_apply, Finset.sum_add_distrib]

/-- A linear map has Wolf's basis-level Kossakowski form (Theorem 7.1,
Equation (7.23)) if and only if it has Lindblad form (Equations (7.21)--(7.22)).

The reverse implication follows Wolf's proof: choose traceless Lindblad
operators, expand `Lⱼ = ∑ₖ Mⱼₖ Fₖ` in a basis of the traceless matrices,
and take the Kossakowski matrix `C = MᴴM`. -/
theorem tracelessBasisKossakowski_iff_lindbladForm
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    (∃ K : TracelessBasisKossakowskiForm D, L = K.toLinearMap) ↔
    (∃ F : LindbladForm D, L = F.toLinearMap) := by
  constructor
  · rintro ⟨K, hK⟩
    exact (kossakowski_iff_lindblad L).mp ⟨K.toKossakowskiForm, hK⟩
  · rintro ⟨G, hG⟩
    obtain ⟨G', hG', htr⟩ := G.exists_traceless
    let b : Module.Basis (Fin (D ^ 2 - 1)) ℂ (tracelessMatrixSubspace D) :=
      Module.finBasisOfFinrankEq ℂ (tracelessMatrixSubspace D)
        finrank_tracelessMatrixSubspace
    let v : Fin G'.r → tracelessMatrixSubspace D := fun j ↦
      ⟨G'.L j, by
        change trace (G'.L j) = 0
        exact htr j⟩
    let M : Matrix (Fin G'.r) (Fin (D ^ 2 - 1)) ℂ :=
      fun j k ↦ b.repr (v j) k
    have h_expand : ∀ j : Fin G'.r,
        G'.L j = ∑ k, M j k • (b k : Matrix (Fin D) (Fin D) ℂ) := by
      intro j
      have h := congrArg (tracelessMatrixSubspace D).subtype
        (b.sum_repr (v j)).symm
      simpa only [M, v, map_sum, map_smul, Submodule.subtype_apply] using h
    let K : TracelessBasisKossakowskiForm D :=
      ⟨G'.H, b, Mᴴ * M, G'.H_hermitian,
        Matrix.posSemidef_conjTranspose_mul_self M⟩
    refine ⟨K, ?_⟩
    let F : LindbladForm D :=
      ⟨G'.r, G'.H, fun j ↦ ∑ k, M j k • (b k : Matrix (Fin D) (Fin D) ℂ),
        G'.H_hermitian⟩
    have hF : F.toLinearMap = G'.toLinearMap := by
      ext1 ρ
      simp only [F, LindbladForm.toLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← h_expand j]
    have hfactor : K.toLinearMap = F.toLinearMap := by
      exact K.toKossakowskiForm.toLinearMap_eq_lindblad_of_factor M rfl
    calc
      L = G.toLinearMap := hG
      _ = G'.toLinearMap := hG'.symm
      _ = F.toLinearMap := hF.symm
      _ = K.toLinearMap := hfactor.symm

/-- **Wolf Theorem 7.1, Equation (7.23).** A linear map generates a semigroup
of quantum channels if and only if it has a
Kossakowski representation in a fixed basis of the traceless matrices with a
positive semidefinite Kossakowski matrix. -/
theorem gksl_iff_tracelessBasisKossakowskiForm
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    IsGKSLGenerator L ↔
      ∃ K : TracelessBasisKossakowskiForm D, L = K.toLinearMap := by
  rw [gksl_iff_lindbladForm, tracelessBasisKossakowski_iff_lindbladForm]

end KossakowskiForms

end -- noncomputable section
