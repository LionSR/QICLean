/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.BipartiteCopies
import QICLean.Algebra.Kronecker.PartialTranspose
import QICLean.Algebra.Kronecker.Vectors
import QICLean.Channel.Schmidt.Rank

/-!
Adapted from QICLean/Channel/Entanglement/FiniteCopyDistillability.lean in the
nptent-operations worktree of QICLean (base commit
8b4c2e43f7df3a62977134e648834b39208b6117, uncommitted completed module;
source SHA-256: f7e2ab1390ba1aeb3f589bebd8f14db44403481f353958f91c2e2d3704b9ba92).
The original copyright and authorship are retained. Curation updates documentation
and imports for the foundations branch; no recurrence purification or operational
rate equivalence is added.

# Finite-copy N-distillability and N-undistillability (Dür–Cirac–Lewenstein–Bruß)

This module formalizes the finite-copy algebraic distillability hierarchy of
Dür, Cirac, Lewenstein, and Bruß, *Distillability and partial transposition in bipartite
systems*, Phys. Rev. A 61, 062313 (2000), arXiv:quant-ph/9910022v1, Section II.1–II.3,
Equations (2)–(4).

## Conventions and separation from asymptotic rate `E_D`

* `N` copies of a bipartite operator `ρ : Matrix (A × B) (A × B) ℂ` are regrouped into
  party-major form `QuantumInfo.bipartiteCopies N ρ` on `(Fin N → A) × (Fin N → B)`.
* The partial transpose over Alice's subsystem is `Matrix.partialTransposeFst`
  in `QICLean.Algebra.Kronecker.PartialTranspose`.
* `IsNDistillable N ρ` requires `0 < N` and a bipartite vector `ψ` of Schmidt rank at most `2`
  (reusing `Matrix.HasSchmidtRankLE 2 ψ`) with `Re ⟨ψ | (ρ^{⊗ N})^{T_A} | ψ⟩ < 0`.
* `IsNUndistillable N ρ` is the negation: no Schmidt-rank-`≤ 2` vector gives a negative
  expectation on `(ρ^{⊗ N})^{T_A}`.
* `IsFiniteCopyDistillable ρ` is `∃ N, IsNDistillable N ρ`, and `IsFiniteCopyUndistillable ρ`
  is `∀ N, IsNUndistillable N ρ`.
* These finite-copy predicates are intentionally kept separate from the asymptotic operational
  rate `QuantumCircuit.distillableEntanglement` (`E_D^P(ρ)`) in
  `QICLean.Circuit.Model.Distillation`. Dür–Cirac–Lewenstein–Bruß cite Horodecki–Horodecki (1999)
  for the reduction from operational LOCC distillability to finite-copy `N`-distillability; that
  operational equivalence (which requires two-qubit recurrence purification and asymptotic rate
  accounting) is not assumed or claimed here.

## Main definitions

* `QuantumInfo.IsOrthonormalPair` — pair of orthonormal vectors in `X → ℂ`.
* `QuantumInfo.HasDCLBTwoTermForm` — DCLB Eq. (3) representation
  `a |e₀⟩|f₀⟩ + b |e₁⟩|f₁⟩` with orthonormal local pairs `e, f`.
* `QuantumInfo.IsNDistillable`, `QuantumInfo.IsNUndistillable`.
* `QuantumInfo.IsFiniteCopyDistillable`, `QuantumInfo.IsFiniteCopyUndistillable`.

## Main results

* `QuantumInfo.partialTransposeFst_bipartiteCopies` — partial transpose commutes with
  party-major `bipartiteCopies`.
* `QuantumInfo.partialTransposeFst_product_sandwich` — generic rectangular local sandwich rule.
* `QuantumInfo.hasDCLBTwoTermForm_of_schmidtRank_eq_two` — every Schmidt-rank-2 vector admits
  the DCLB Eq. (3) orthonormal two-term representation (with positive real coefficients).
* `QuantumInfo.isNDistillable_iff_unit_witness` — normalization independence of witnesses.
* `QuantumInfo.isNDistillable_iff_dclbTwoTermForm` — equivalence with DCLB Eq. (3) for PSD `ρ`.
* `QuantumInfo.isNDistillable_iff_exists_coisometry_twoQubit_nppt` — equivalence with a local
  2D-subspace (co-isometric) `2 × 2` NPPT projection for PSD `ρ`, handling dimensions `< 2`.
* `QuantumInfo.isNDistillable_iff_exists_filter_twoQubit_nppt` — equivalence with an arbitrary
  local `2 × 2` NPPT filter for Hermitian `ρ`.
* `QuantumInfo.isFiniteCopyUndistillable_of_partialTransposeFst_posSemidef` — PPT implies
  `N`-undistillable for all `N`.
* `QuantumInfo.isNDistillable_mono` — monotonicity of `N`-distillability in `N` for nonzero
  PSD `ρ`.
* `QuantumInfo.isFiniteCopyDistillable_iff_not_partialTransposeFst_posSemidef_of_card_le_two` —
  DCLB Section II.3: for `|A| ≤ 2` or `|B| ≤ 2`, NPPT is equivalent to `1`-distillability and
  to finite-copy distillability.
-/

open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace QuantumInfo

/-! ## Section 1: Generic `partialTransposeFst` identities and rank-one positivity -/

section PartialTransposeFstAux

variable {X Y X' Y' : Type*}

/-- Quadratic form pullback along a conjugate transpose:
`⟨Kᴴ φ | M | Kᴴ φ⟩ = ⟨φ | K M Kᴴ | φ⟩`. -/
theorem quadForm_conjTranspose_mulVec [Fintype X] [Fintype Y]
    (K : Matrix X Y ℂ) (M : Matrix Y Y ℂ) (φ : X → ℂ) :
    star (Kᴴ *ᵥ φ) ⬝ᵥ M *ᵥ (Kᴴ *ᵥ φ) = star φ ⬝ᵥ (K * M * Kᴴ) *ᵥ φ := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- The quadratic form of a Hermitian matrix has zero imaginary part. -/
theorem quadForm_im_eq_zero_of_isHermitian [Fintype X]
    {M : Matrix X X ℂ} (hM : M.IsHermitian) (ψ : X → ℂ) :
    (star ψ ⬝ᵥ M *ᵥ ψ).im = 0 := by
  have hconj : star (star ψ ⬝ᵥ M *ᵥ ψ) = star ψ ⬝ᵥ M *ᵥ ψ := by
    simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : star (M j i) = M i j := by simpa [Matrix.conjTranspose_apply] using hM.apply i j
    rw [hij]
    simp only [Pi.star_apply, star_star]
    ring
  exact Complex.conj_eq_iff_im.mp hconj

/-- The first-factor partial transpose of a Hermitian matrix is Hermitian. -/
theorem partialTransposeFst_isHermitian {σ : Matrix (X × Y) (X × Y) ℂ}
    (hσ : σ.IsHermitian) : (Matrix.partialTransposeFst σ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  rw [Matrix.partialTransposeFst_apply, Matrix.partialTransposeFst_apply]
  exact hσ.apply (q.1, p.2) (p.1, q.2)

/-- Generic rectangular local-sandwich intertwining for `Matrix.partialTransposeFst`:
`((A ⊗ B) σ (A ⊗ B)ᴴ)^{T_A} = (Ā ⊗ B) σ^{T_A} (Ā ⊗ B)ᴴ`. -/
theorem partialTransposeFst_product_sandwich
    [Fintype X] [Fintype Y]
    (A : Matrix X' X ℂ) (B : Matrix Y' Y ℂ)
    (σ : Matrix (X × Y) (X × Y) ℂ) :
    Matrix.partialTransposeFst ((A ⊗ₖ B) * σ * (A ⊗ₖ B)ᴴ) =
      (A.map star ⊗ₖ B) * Matrix.partialTransposeFst σ * (A.map star ⊗ₖ B)ᴴ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.partialTransposeFst_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.map_apply, star_mul, star_star,
    Fintype.sum_prod_type, Finset.sum_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- On a product vector `u ⊗ v`, the quadratic form of `σ^{T_A}` equals the quadratic form of
`σ` on `ū ⊗ v`. -/
theorem quadForm_partialTransposeFst_vecKronecker
    [Fintype X] [Fintype Y]
    (σ : Matrix (X × Y) (X × Y) ℂ) (u : X → ℂ) (v : Y → ℂ) :
    star (Matrix.vecKronecker u v) ⬝ᵥ
        Matrix.partialTransposeFst σ *ᵥ Matrix.vecKronecker u v =
      star (Matrix.vecKronecker (star u) v) ⬝ᵥ
        σ *ᵥ Matrix.vecKronecker (star u) v := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.partialTransposeFst_apply,
    Matrix.vecKronecker_apply, Pi.star_apply, star_mul', star_star, Finset.mul_sum]
  -- Swap the two X-indices (outer 1st and inner 1st) while keeping Y-indices in place.
  conv_lhs =>
    arg 2; ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext c
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- Partial transpose commutes with party-major `bipartiteCopies`. -/
@[simp]
theorem partialTransposeFst_bipartiteCopies {A B : Type} (N : ℕ)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix.partialTransposeFst (bipartiteCopies N ρ) =
      bipartiteCopies N (Matrix.partialTransposeFst ρ) := by
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  simp [Matrix.partialTransposeFst_apply, bipartiteCopies_apply]

/-- Party-major copies of a PPT matrix remain PPT. -/
theorem partialTransposeFst_bipartiteCopies_posSemidef {A B : Type} [Finite A] [Finite B]
    (N : ℕ) {ρ : Matrix (A × B) (A × B) ℂ}
    (hρ : (Matrix.partialTransposeFst ρ).PosSemidef) :
    (Matrix.partialTransposeFst (bipartiteCopies N ρ)).PosSemidef := by
  rw [partialTransposeFst_bipartiteCopies]
  exact bipartiteCopies_posSemidef N hρ

/-- For a Hermitian matrix `M`, `Re ⟨ψ | M | ψ⟩ < 0` is equivalent to `⟨ψ | M | ψ⟩ < 0` in the
complex partial order. -/
theorem quadForm_re_neg_iff_complexOrder_neg [Fintype X]
    {M : Matrix X X ℂ} (hM : M.IsHermitian) (ψ : X → ℂ) :
    (star ψ ⬝ᵥ M *ᵥ ψ).re < 0 ↔ star ψ ⬝ᵥ M *ᵥ ψ < 0 := by
  rw [Complex.lt_def]
  simp [quadForm_im_eq_zero_of_isHermitian hM ψ]

/-- For a Hermitian matrix `M`, `¬ M.PosSemidef` is equivalent to the existence of a vector
`ψ` with `Re ⟨ψ | M | ψ⟩ < 0`. -/
theorem not_posSemidef_iff_exists_quadForm_re_neg [Fintype X]
    {M : Matrix X X ℂ} (hM : M.IsHermitian) :
    ¬ M.PosSemidef ↔ ∃ ψ : X → ℂ, (star ψ ⬝ᵥ M *ᵥ ψ).re < 0 := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro hnot
    by_contra hno
    push Not at hno
    apply hnot
    refine ⟨hM, fun ψ => ?_⟩
    rw [Complex.le_def]
    exact ⟨hno ψ, (quadForm_im_eq_zero_of_isHermitian hM ψ).symm⟩
  · rintro ⟨ψ, hψ⟩ ⟨_, hge⟩
    have h0 : (0 : ℝ) ≤ (star ψ ⬝ᵥ M *ᵥ ψ).re := (Complex.le_def.mp (hge ψ)).1
    linarith

/-- For a positive semidefinite matrix `σ`, every vector of Schmidt rank at most `1` has
nonnegative expectation on `σ^{T_A}`. -/
theorem quadForm_partialTransposeFst_nonneg_of_hasSchmidtRankLE_one
    [Fintype X] [Fintype Y]
    {σ : Matrix (X × Y) (X × Y) ℂ} (hσ : σ.PosSemidef)
    {ψ : X × Y → ℂ} (hψ : Matrix.HasSchmidtRankLE 1 ψ) :
    0 ≤ (star ψ ⬝ᵥ Matrix.partialTransposeFst σ *ᵥ ψ).re := by
  obtain ⟨P, Q, hPQ⟩ := Matrix.exists_mul_eq_of_rank_le (Matrix.schmidtCoeffMatrix ψ) hψ
  have hprod : ψ = Matrix.vecKronecker (fun x => P x 0) (fun y => Q 0 y) := by
    ext ⟨x, y⟩
    have hxy := congrFun (congrFun hPQ x) y
    simpa [Matrix.schmidtCoeffMatrix_apply, Matrix.mul_apply, Matrix.vecKronecker_apply]
      using hxy.symm
  rw [hprod, quadForm_partialTransposeFst_vecKronecker]
  have hge := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hσ).2
    (Matrix.vecKronecker (star (fun x => P x 0)) (fun y => Q 0 y))
  exact (Complex.le_def.mp hge).1

/-- For a positive semidefinite matrix `σ`, any Schmidt-rank-`≤ 2` negative witness for `σ^{T_A}`
necessarily has exact Schmidt rank `2`. -/
theorem schmidtRank_eq_two_of_neg_partialTransposeFst
    [Fintype X] [Fintype Y]
    {σ : Matrix (X × Y) (X × Y) ℂ} (hσ : σ.PosSemidef)
    {ψ : X × Y → ℂ} (hψ : Matrix.HasSchmidtRankLE 2 ψ)
    (hneg : (star ψ ⬝ᵥ Matrix.partialTransposeFst σ *ᵥ ψ).re < 0) :
    Matrix.schmidtRank ψ = 2 := by
  have hle : Matrix.schmidtRank ψ ≤ 2 := hψ
  have hnot1 : ¬ Matrix.schmidtRank ψ ≤ 1 := by
    intro h1
    have hge := quadForm_partialTransposeFst_nonneg_of_hasSchmidtRankLE_one hσ h1
    linarith
  omega

end PartialTransposeFstAux

/-! ## Section 2: DCLB Eq. (3) orthonormal two-term Schmidt form -/

section DCLBTwoTermForm

variable {X Y : Type*}

/-- A pair of orthonormal vectors `e 0, e 1 : X → ℂ`. -/
def IsOrthonormalPair [Fintype X] (e : Fin 2 → X → ℂ) : Prop :=
  ∀ i j : Fin 2, star (e i) ⬝ᵥ e j = if i = j then 1 else 0

/-- DCLB Eq. (3) two-term orthonormal representation:
`ψ = a (e₀ ⊗ f₀) + b (e₁ ⊗ f₁)` with orthonormal local pairs `e, f`. -/
def HasDCLBTwoTermForm [Fintype X] [Fintype Y] (ψ : X × Y → ℂ) : Prop :=
  ∃ (e : Fin 2 → X → ℂ) (f : Fin 2 → Y → ℂ) (a b : ℂ),
    IsOrthonormalPair e ∧ IsOrthonormalPair f ∧
      ψ = a • Matrix.vecKronecker (e 0) (f 0) + b • Matrix.vecKronecker (e 1) (f 1)

/-- Any vector in DCLB Eq. (3) form has Schmidt rank at most `2`. -/
theorem hasSchmidtRankLE_two_of_hasDCLBTwoTermForm [Fintype X] [Fintype Y]
    {ψ : X × Y → ℂ} (hψ : HasDCLBTwoTermForm ψ) :
    Matrix.HasSchmidtRankLE 2 ψ := by
  obtain ⟨e, f, a, b, _, _, rfl⟩ := hψ
  let P : Matrix X (Fin 2) ℂ := Matrix.of fun x k => if k = 0 then a * e 0 x else b * e 1 x
  let Q : Matrix (Fin 2) Y ℂ := Matrix.of fun k y => if k = 0 then f 0 y else f 1 y
  have hfac : Matrix.schmidtCoeffMatrix
      (a • Matrix.vecKronecker (e 0) (f 0) + b • Matrix.vecKronecker (e 1) (f 1)) = P * Q := by
    ext x y
    simp only [Matrix.schmidtCoeffMatrix_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.vecKronecker_apply, Matrix.mul_apply, Fin.sum_univ_two, P, Q, Matrix.of_apply,
      ↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff]
    ring
  rw [Matrix.HasSchmidtRankLE, Matrix.schmidtRank, hfac]
  exact (Matrix.rank_mul_le_left P Q).trans (by simpa using Matrix.rank_le_card_width P)

/-- Scaling a vector by a scalar does not increase its Schmidt rank. -/
theorem hasSchmidtRankLE_smul [Fintype Y] {k : ℕ} {ψ : X × Y → ℂ}
    (hψ : Matrix.HasSchmidtRankLE k ψ) (c : ℂ) :
    Matrix.HasSchmidtRankLE k (c • ψ) := by
  rw [Matrix.hasSchmidtRankLE_iff, Matrix.schmidtRank]
  have hcoeff : Matrix.schmidtCoeffMatrix (c • ψ) = c • Matrix.schmidtCoeffMatrix ψ := by
    ext x y; rfl
  rw [hcoeff]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (Matrix.rank_smul_of_mem_nonZeroDivisors (Matrix.schmidtCoeffMatrix ψ)
      (mem_nonZeroDivisors_of_ne_zero hc)).le.trans hψ

/-- Every bipartite vector of exact Schmidt rank `2` admits a DCLB Eq. (3) orthonormal two-term
decomposition (with positive real Schmidt coefficients). -/
theorem hasDCLBTwoTermForm_of_schmidtRank_eq_two
    [Fintype X] [Fintype Y]
    {ψ : X × Y → ℂ} (hψ : Matrix.schmidtRank ψ = 2) :
    HasDCLBTwoTermForm ψ := by
  classical
  let M : Matrix X Y ℂ := Matrix.schmidtCoeffMatrix ψ
  have hMrank : M.rank = 2 := hψ
  let H : Matrix X X ℂ := M * Mᴴ
  have hHpsd : H.PosSemidef := by
    simpa [H] using Matrix.posSemidef_conjTranspose_mul_self Mᴴ
  have hH : H.IsHermitian := hHpsd.1
  let b := hH.eigenvectorBasis
  let μ : X → ℝ := hH.eigenvalues
  have hμ_nonneg : ∀ i, 0 ≤ μ i := hHpsd.eigenvalues_nonneg
  have hmul : ∀ i : X, H *ᵥ (b i : X → ℂ) = (μ i : ℂ) • (b i : X → ℂ) := by
    intro i
    simpa only [b, μ, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hH.mulVec_eigenvectorBasis i
  have horth : ∀ i j : X, star (b i : X → ℂ) ⬝ᵥ (b j : X → ℂ) = if i = j then 1 else 0 := by
    intro i j
    have h := orthonormal_iff_ite.mp b.orthonormal i j
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h
  let S : Finset X := Finset.univ.filter fun i => μ i ≠ 0
  have hker : ∀ i : X, i ∉ S → Mᴴ *ᵥ (b i : X → ℂ) = 0 := by
    intro i hi
    have hμ0 : μ i = 0 := by simpa [S] using hi
    have hnorm0 : star (Mᴴ *ᵥ (b i : X → ℂ)) ⬝ᵥ (Mᴴ *ᵥ (b i : X → ℂ)) = 0 := by
      have h1 : star (Mᴴ *ᵥ (b i : X → ℂ)) ⬝ᵥ (Mᴴ *ᵥ (b i : X → ℂ)) =
          star (b i : X → ℂ) ⬝ᵥ (H *ᵥ (b i : X → ℂ)) := by
        simpa [H] using quadForm_conjTranspose_mulVec M (1 : Matrix Y Y ℂ) (b i : X → ℂ)
      rw [h1, hmul i, hμ0]
      simp
    ext y
    have hre : ∑ y' : Y, Complex.normSq ((Mᴴ *ᵥ (b i : X → ℂ)) y') = 0 := by
      have hre0 := congrArg Complex.re hnorm0
      simpa [dotProduct, Complex.mul_re, Complex.normSq_apply, mul_comm] using hre0
    have hterm : Complex.normSq ((Mᴴ *ᵥ (b i : X → ℂ)) y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun y' _ => Complex.normSq_nonneg _)).mp hre y
        (Finset.mem_univ y)
    exact Complex.normSq_eq_zero.mp hterm
  have hM_expand : ∀ x y, M x y = ∑ i ∈ S, (b i : X → ℂ) x * (Mᵀ *ᵥ star (b i : X → ℂ)) y := by
    intro x y
    have hcol : (WithLp.toLp 2 (M.col y) : EuclideanSpace ℂ X) =
        ∑ i : X, inner ℂ (b i) (WithLp.toLp 2 (M.col y)) • b i := by
      simpa using (b.sum_repr' (WithLp.toLp 2 (M.col y))).symm
    have hx := congrFun (congrArg WithLp.ofLp hcol) x
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct] at hx
    have hinner : ∀ i : X, M.col y ⬝ᵥ star (b i : X → ℂ) = (Mᵀ *ᵥ star (b i : X → ℂ)) y := by
      intro i
      simp [dotProduct, Matrix.mulVec, Matrix.col_apply, Matrix.transpose_apply]
    calc
      M x y = (WithLp.ofLp (WithLp.toLp 2 (M.col y))) x := rfl
      _ = ∑ i : X, (Mᵀ *ᵥ star (b i : X → ℂ)) y * (b i : X → ℂ) x := by
        simpa [hinner] using hx
      _ = ∑ i : X, (b i : X → ℂ) x * (Mᵀ *ᵥ star (b i : X → ℂ)) y :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = ∑ i ∈ S, (b i : X → ℂ) x * (Mᵀ *ᵥ star (b i : X → ℂ)) y := by
        symm
        refine Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_
        have h0 := congrFun (hker i hi) y
        have hstar0 : (Mᵀ *ᵥ star (b i : X → ℂ)) y = star ((Mᴴ *ᵥ (b i : X → ℂ)) y) := by
          simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.transpose_apply,
            mul_comm]
        simp [hstar0, h0]
  have hMleS : M.rank ≤ S.card := by
    let P : Matrix X S ℂ := Matrix.of fun x i => (b i.1 : X → ℂ) x
    let Q : Matrix S Y ℂ := Matrix.of fun i y => (Mᵀ *ᵥ star (b i.1 : X → ℂ)) y
    have hPQ : M = P * Q := by
      ext x y
      rw [hM_expand x y, Matrix.mul_apply]
      simpa [P, Q, Matrix.of_apply] using (Finset.sum_coe_sort S
        (fun i => (b i : X → ℂ) x * (Mᵀ *ᵥ star (b i : X → ℂ)) y)).symm
    rw [hPQ]
    exact (Matrix.rank_mul_le_left P Q).trans (by simpa using Matrix.rank_le_card_width P)
  have hSleM : S.card ≤ M.rank := by
    have hsub : Submodule.span ℂ ((fun i : X => (b i : X → ℂ)) '' (S : Set X)) ≤
        LinearMap.range M.mulVecLin := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      have hμne : (μ i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa [S] using hi)
      refine ⟨(μ i : ℂ)⁻¹ • (Mᴴ *ᵥ (b i : X → ℂ)), ?_⟩
      change M *ᵥ ((μ i : ℂ)⁻¹ • (Mᴴ *ᵥ (b i : X → ℂ))) = (b i : X → ℂ)
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      change (μ i : ℂ)⁻¹ • (H *ᵥ (b i : X → ℂ)) = (b i : X → ℂ)
      rw [hmul i, smul_smul, inv_mul_cancel₀ hμne, one_smul]
    have hli : LinearIndependent ℂ (fun i : S => (b i.1 : X → ℂ)) := by
      have hli_all : LinearIndependent ℂ (fun i : X => (b i : X → ℂ)) :=
        b.orthonormal.linearIndependent.map' (WithLp.linearEquiv 2 ℂ (X → ℂ)).toLinearMap
          (LinearEquiv.ker _)
      exact hli_all.comp (fun i : S => i.1) Subtype.val_injective
    have hcard_eq : Module.finrank ℂ
        (Submodule.span ℂ ((fun i : X => (b i : X → ℂ)) '' (S : Set X))) = S.card := by
      rw [Set.image_eq_range]
      simpa [Fintype.card_coe] using finrank_span_eq_card hli
    rw [← hcard_eq]
    exact Submodule.finrank_mono hsub
  have hScard : S.card = 2 := by omega
  obtain ⟨i₀, i₁, hne, hS_eq⟩ := Finset.card_eq_two.mp hScard
  have hi₀ : i₀ ∈ S := by rw [hS_eq]; simp
  have hi₁ : i₁ ∈ S := by rw [hS_eq]; simp
  have hμ₀_pos : 0 < μ i₀ := lt_of_le_of_ne (hμ_nonneg i₀) (Ne.symm (by simpa [S] using hi₀))
  have hμ₁_pos : 0 < μ i₁ := lt_of_le_of_ne (hμ_nonneg i₁) (Ne.symm (by simpa [S] using hi₁))
  let idx : Fin 2 → X := fun k => if k = 0 then i₀ else i₁
  let e : Fin 2 → X → ℂ := fun k => (b (idx k) : X → ℂ)
  let s : Fin 2 → ℝ := fun k => Real.sqrt (μ (idx k))
  have hs_pos : ∀ k : Fin 2, 0 < s k := by
    intro k; fin_cases k
    · exact Real.sqrt_pos.mpr hμ₀_pos
    · exact Real.sqrt_pos.mpr hμ₁_pos
  let f : Fin 2 → Y → ℂ := fun k => ((s k : ℂ)⁻¹) • (Mᵀ *ᵥ star (e k))
  refine ⟨e, f, (s 0 : ℂ), (s 1 : ℂ), ?_, ?_, ?_⟩
  · intro k l
    have hidx : idx k = idx l ↔ k = l := by
      fin_cases k <;> fin_cases l <;> simp [idx, hne, hne.symm]
    simpa [e, hidx] using horth (idx k) (idx l)
  · intro k l
    have hdot_raw : star (Mᵀ *ᵥ star (e k)) ⬝ᵥ (Mᵀ *ᵥ star (e l)) =
        (μ (idx k) : ℂ) * (star (e l) ⬝ᵥ e k) := by
      have h1 : star (Mᵀ *ᵥ star (e k)) = Mᴴ *ᵥ e k := by
        ext y
        simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.transpose_apply,
          mul_comm]
      have h2 : Mᵀ *ᵥ star (e l) = star (Mᴴ *ᵥ e l) := by
        ext y
        simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.transpose_apply,
          mul_comm]
      rw [h1, h2, dotProduct_comm, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
        ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      change star (e l) ⬝ᵥ H *ᵥ e k = _
      rw [hmul (idx k), dotProduct_smul, smul_eq_mul]
    have hsk_ne : (s k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hs_pos k).ne'
    have hstar_sk : star ((s k : ℂ)⁻¹) = (s k : ℂ)⁻¹ := by simp [Complex.conj_ofReal]
    calc
      star (f k) ⬝ᵥ f l
          = ((s k : ℂ)⁻¹ * (s l : ℂ)⁻¹) * (star (Mᵀ *ᵥ star (e k)) ⬝ᵥ (Mᵀ *ᵥ star (e l))) := by
        simp only [f, star_smul, hstar_sk, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        ring
      _ = ((s k : ℂ)⁻¹ * (s l : ℂ)⁻¹) * ((μ (idx k) : ℂ) * (star (e l) ⬝ᵥ e k)) := by
        rw [hdot_raw]
      _ = if k = l then 1 else 0 := by
        have hidx : idx l = idx k ↔ k = l := by
          fin_cases k <;> fin_cases l <;> simp [idx, hne, hne.symm]
        rw [show star (e l) ⬝ᵥ e k = if k = l then 1 else 0 by
          simpa [e, hidx] using horth (idx l) (idx k)]
        by_cases hkl : k = l
        · subst hkl
          simp only [↓reduceIte, mul_one]
          have hsq : (s k : ℂ) * (s k : ℂ) = (μ (idx k) : ℂ) := by
            rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hμ_nonneg (idx k))]
          rw [← hsq]
          field_simp [hsk_ne]
        · simp [hkl]
  · ext ⟨x, y⟩
    have hxy := hM_expand x y
    rw [hS_eq, Finset.sum_pair hne] at hxy
    have hs0_ne : (s 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hs_pos 0).ne'
    have hs1_ne : (s 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hs_pos 1).ne'
    change M x y = _
    rw [hxy]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecKronecker_apply, f, e, idx,
      ↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff]
    field_simp [hs0_ne, hs1_ne]

end DCLBTwoTermForm

/-! ## Section 3: Normalization independence and 4-way equivalence on a single bipartite matrix -/

section SingleMatrixEquivalences

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Normalization independence of Schmidt-rank-`≤ 2` negative witnesses: any negative witness
can be rescaled to unit norm without changing its Schmidt rank bound. -/
theorem exists_unit_schmidtRankLE_two_neg_iff (M : Matrix (X × Y) (X × Y) ℂ) :
    (∃ ψ : X × Y → ℂ, Matrix.HasSchmidtRankLE 2 ψ ∧ (star ψ ⬝ᵥ M *ᵥ ψ).re < 0) ↔
      (∃ ψ : X × Y → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ Matrix.HasSchmidtRankLE 2 ψ ∧
        (star ψ ⬝ᵥ M *ᵥ ψ).re < 0) := by
  constructor
  · rintro ⟨ψ, hsr, hneg⟩
    have hψ_ne : ψ ≠ 0 := by
      intro h0; subst h0; simp at hneg
    have hnorm_pos : 0 < (star ψ ⬝ᵥ ψ).re := by
      have hre : (star ψ ⬝ᵥ ψ).re = ∑ p, Complex.normSq (ψ p) := by
        simp [dotProduct, Complex.mul_re, Complex.normSq_apply, mul_comm]
      rw [hre]
      obtain ⟨p, hp⟩ := Function.ne_iff.mp hψ_ne
      exact Finset.sum_pos' (fun q _ => Complex.normSq_nonneg _)
        ⟨p, Finset.mem_univ p, Complex.normSq_pos.mpr hp⟩
    have hnorm_im : (star ψ ⬝ᵥ ψ).im = 0 := by
      simp [dotProduct, Complex.mul_im, mul_comm]
    let r : ℝ := Real.sqrt (star ψ ⬝ᵥ ψ).re
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hnorm_pos
    let c : ℂ := (r : ℂ)⁻¹
    have hstar_c : star c = c := by simp [c, Complex.conj_ofReal]
    refine ⟨c • ψ, ?_, hasSchmidtRankLE_smul hsr c, ?_⟩
    · rw [star_smul, hstar_c, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have hdot_eq : star ψ ⬝ᵥ ψ = ((star ψ ⬝ᵥ ψ).re : ℂ) :=
        Complex.ext rfl (by simp [hnorm_im])
      have hr2 : (r : ℂ) * (r : ℂ) = ((star ψ ⬝ᵥ ψ).re : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnorm_pos.le]
      rw [hdot_eq, ← hr2]
      have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
      simp only [c]
      field_simp [hr_ne]
    · rw [star_smul, hstar_c, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, smul_eq_mul]
      have hc2 : c * (c * (star ψ ⬝ᵥ M *ᵥ ψ)) =
          (((r⁻¹ * r⁻¹ : ℝ) : ℂ)) * (star ψ ⬝ᵥ M *ᵥ ψ) := by
        simp only [c, Complex.ofReal_mul, Complex.ofReal_inv]; ring
      rw [hc2, Complex.re_ofReal_mul]
      exact mul_neg_of_pos_of_neg (mul_pos (inv_pos.mpr hr_pos) (inv_pos.mpr hr_pos)) hneg
  · rintro ⟨ψ, _, hsr, hneg⟩
    exact ⟨ψ, hsr, hneg⟩

/-- For a positive semidefinite matrix `σ`, existence of a Schmidt-rank-`≤ 2` negative witness
for `σ^{T_A}` is equivalent to existence of a DCLB Eq. (3) orthonormal two-term witness. -/
theorem exists_schmidtRankLE_two_neg_iff_exists_dclbTwoTermForm_neg
    {σ : Matrix (X × Y) (X × Y) ℂ} (hσ : σ.PosSemidef) :
    (∃ ψ : X × Y → ℂ, Matrix.HasSchmidtRankLE 2 ψ ∧
        (star ψ ⬝ᵥ Matrix.partialTransposeFst σ *ᵥ ψ).re < 0) ↔
      (∃ ψ : X × Y → ℂ, HasDCLBTwoTermForm ψ ∧
        (star ψ ⬝ᵥ Matrix.partialTransposeFst σ *ᵥ ψ).re < 0) := by
  constructor
  · rintro ⟨ψ, hsr, hneg⟩
    exact ⟨ψ, hasDCLBTwoTermForm_of_schmidtRank_eq_two
      (schmidtRank_eq_two_of_neg_partialTransposeFst hσ hsr hneg), hneg⟩
  · rintro ⟨ψ, hdclb, hneg⟩
    exact ⟨ψ, hasSchmidtRankLE_two_of_hasDCLBTwoTermForm hdclb, hneg⟩

/-- For any Hermitian matrix `σ`, existence of a Schmidt-rank-`≤ 2` negative witness for
`σ^{T_A}` is equivalent to the existence of a local `2 × 2` filter `A ⊗ B` producing an
NPPT two-qubit matrix `(A ⊗ B) σ (A ⊗ B)ᴴ`. Works for arbitrary finite dimensions, including
`|X| < 2` or `|Y| < 2`. -/
theorem exists_schmidtRankLE_two_neg_iff_exists_filter_twoQubit_nppt
    {σ : Matrix (X × Y) (X × Y) ℂ} (hσ : σ.IsHermitian) :
    (∃ ψ : X × Y → ℂ, Matrix.HasSchmidtRankLE 2 ψ ∧
        (star ψ ⬝ᵥ Matrix.partialTransposeFst σ *ᵥ ψ).re < 0) ↔
      (∃ (A : Matrix (Fin 2) X ℂ) (B : Matrix (Fin 2) Y ℂ),
        ¬ Matrix.IsPPT ((A ⊗ₖ B) * σ * (A ⊗ₖ B)ᴴ)) := by
  constructor
  · rintro ⟨ψ, hsr, hneg⟩
    obtain ⟨P, Q, hPQ⟩ := Matrix.exists_mul_eq_of_rank_le (Matrix.schmidtCoeffMatrix ψ) hsr
    let A : Matrix (Fin 2) X ℂ := Pᵀ
    let B : Matrix (Fin 2) Y ℂ := Q.map star
    refine ⟨A, B, ?_⟩
    rw [Matrix.IsPPT, ← Matrix.partialTransposeFst_eq_partialTransposeLeft,
      partialTransposeFst_product_sandwich]
    intro hpsd
    let φ : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0
    have hpull : (A.map star ⊗ₖ B)ᴴ *ᵥ φ = ψ := by
      ext ⟨x, y⟩
      have hxy : (P * Q) x y = ψ (x, y) := congrFun (congrFun hPQ x) y
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
        Matrix.kroneckerMap_apply, Matrix.map_apply, star_mul', star_star, A, B,
        Matrix.transpose_apply, φ]
      rw [← hxy, Matrix.mul_apply]
      simp
    have hge : 0 ≤ (star φ ⬝ᵥ ((A.map star ⊗ₖ B) * Matrix.partialTransposeFst σ *
        (A.map star ⊗ₖ B)ᴴ) *ᵥ φ).re :=
      (Complex.le_def.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 φ)).1
    rw [← quadForm_conjTranspose_mulVec, hpull] at hge
    linarith
  · rintro ⟨A, B, hnppt⟩
    have hτ_herm : ((A ⊗ₖ B) * σ * (A ⊗ₖ B)ᴴ).IsHermitian := by
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
        congrArg (fun M => (A ⊗ₖ B) * M * (A ⊗ₖ B)ᴴ) hσ.eq
    have hpt_herm : (Matrix.partialTransposeLeft ((A ⊗ₖ B) * σ * (A ⊗ₖ B)ᴴ)).IsHermitian :=
      hτ_herm.partialTransposeLeft
    rw [Matrix.IsPPT, not_posSemidef_iff_exists_quadForm_re_neg hpt_herm] at hnppt
    obtain ⟨φ, hφ⟩ := hnppt
    rw [← Matrix.partialTransposeFst_eq_partialTransposeLeft,
      partialTransposeFst_product_sandwich] at hφ
    let ψ : X × Y → ℂ := (A.map star ⊗ₖ B)ᴴ *ᵥ φ
    refine ⟨ψ, ?_, ?_⟩
    · have hcoeff : Matrix.schmidtCoeffMatrix ψ =
          (A.map star)ᴴ * Matrix.schmidtCoeffMatrix φ * (Bᴴ)ᵀ := by
        ext x y
        simp only [ψ, Matrix.schmidtCoeffMatrix_apply, Matrix.mulVec, dotProduct,
          Fintype.sum_prod_type, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
          Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, star_mul']
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
        ring
      rw [Matrix.HasSchmidtRankLE, Matrix.schmidtRank, hcoeff]
      exact (Matrix.rank_mul_le_left _ _).trans
        ((Matrix.rank_mul_le_right _ _).trans
          (by simpa using Matrix.rank_le_card_height (Matrix.schmidtCoeffMatrix φ)))
    · rw [quadForm_conjTranspose_mulVec]
      exact hφ

/-- For any positive semidefinite matrix `σ`, existence of a Schmidt-rank-`≤ 2` negative witness
for `σ^{T_A}` is equivalent to the existence of local 2D-subspace co-isometries `A, B`
(`A Aᴴ = 1`, `B Bᴴ = 1`) such that the projected two-qubit operator `(A ⊗ B) σ (A ⊗ B)ᴴ` is
NPPT. Handles dimensions `< 2` cleanly: when `|X| < 2` or `|Y| < 2`, both sides are `False`. -/
theorem exists_schmidtRankLE_two_neg_iff_exists_coisometry_twoQubit_nppt
    {σ : Matrix (X × Y) (X × Y) ℂ} (hσ : σ.PosSemidef) :
    (∃ ψ : X × Y → ℂ, Matrix.HasSchmidtRankLE 2 ψ ∧
        (star ψ ⬝ᵥ Matrix.partialTransposeFst σ *ᵥ ψ).re < 0) ↔
      (∃ (A : Matrix (Fin 2) X ℂ) (B : Matrix (Fin 2) Y ℂ),
        A * Aᴴ = 1 ∧ B * Bᴴ = 1 ∧ ¬ Matrix.IsPPT ((A ⊗ₖ B) * σ * (A ⊗ₖ B)ᴴ)) := by
  constructor
  · intro h
    obtain ⟨ψ, hdclb, hneg⟩ :=
      (exists_schmidtRankLE_two_neg_iff_exists_dclbTwoTermForm_neg hσ).mp h
    obtain ⟨e, f, a, b, he, hf, rfl⟩ := hdclb
    let A : Matrix (Fin 2) X ℂ := Matrix.of fun i x => e i x
    let B : Matrix (Fin 2) Y ℂ := Matrix.of fun j y => star (f j y)
    have hA : A * Aᴴ = 1 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, A, Matrix.of_apply,
        Matrix.one_apply]
      have hij := congrArg star (he i j)
      simpa [dotProduct, star_mul', star_star, apply_ite star] using hij
    have hB : B * Bᴴ = 1 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, B, Matrix.of_apply,
        Matrix.one_apply, star_star]
      simpa [dotProduct] using hf i j
    refine ⟨A, B, hA, hB, ?_⟩
    rw [Matrix.IsPPT, ← Matrix.partialTransposeFst_eq_partialTransposeLeft,
      partialTransposeFst_product_sandwich]
    intro hpsd
    let φ : Fin 2 × Fin 2 → ℂ := fun p =>
      if p = (0, 0) then a else if p = (1, 1) then b else 0
    have hpull : (A.map star ⊗ₖ B)ᴴ *ᵥ φ =
        a • Matrix.vecKronecker (e 0) (f 0) + b • Matrix.vecKronecker (e 1) (f 1) := by
      ext ⟨x, y⟩
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.map_apply,
        star_mul', star_star, A, B, Matrix.of_apply, φ, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Matrix.vecKronecker_apply]
      norm_num
      ring
    have hge : 0 ≤ (star φ ⬝ᵥ ((A.map star ⊗ₖ B) * Matrix.partialTransposeFst σ *
        (A.map star ⊗ₖ B)ᴴ) *ᵥ φ).re :=
      (Complex.le_def.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 φ)).1
    rw [← quadForm_conjTranspose_mulVec, hpull] at hge
    linarith
  · rintro ⟨A, B, _, _, hnppt⟩
    exact (exists_schmidtRankLE_two_neg_iff_exists_filter_twoQubit_nppt hσ.1).mpr ⟨A, B, hnppt⟩

end SingleMatrixEquivalences

/-! ## Section 4: DCLB `N`-distillability, `N`-undistillability, and finite-copy distillability -/

section FiniteCopyDistillability

variable {A B : Type} [Fintype A] [Fintype B]

/-- **`N`-distillability** (Dür–Cirac–Lewenstein–Bruß, PRA 61, 062313 (2000), Sec. II.2,
Eqs. (3)–(4)): `N > 0` and there exists a party-major `N`-copy vector `ψ` of Schmidt rank at
most `2` with `Re ⟨ψ | (ρ^{⊗ N})^{T_A} | ψ⟩ < 0`. -/
def IsNDistillable (N : ℕ) (ρ : Matrix (A × B) (A × B) ℂ) : Prop :=
  0 < N ∧
    ∃ ψ : (Fin N → A) × (Fin N → B) → ℂ,
      Matrix.HasSchmidtRankLE 2 ψ ∧
        (star ψ ⬝ᵥ Matrix.partialTransposeFst (bipartiteCopies N ρ) *ᵥ ψ).re < 0

/-- **`N`-undistillability** (DCLB Sec. II.2): every party-major `N`-copy vector of Schmidt
rank at most `2` has nonnegative expectation on `(ρ^{⊗ N})^{T_A}`. -/
def IsNUndistillable (N : ℕ) (ρ : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∀ ψ : (Fin N → A) × (Fin N → B) → ℂ,
    Matrix.HasSchmidtRankLE 2 ψ →
      0 ≤ (star ψ ⬝ᵥ Matrix.partialTransposeFst (bipartiteCopies N ρ) *ᵥ ψ).re

/-- **Finite-copy distillability** (DCLB Sec. II.2): `ρ` is `N`-distillable for some `N > 0`.
Kept strictly separate from asymptotic operational rate `E_D^P(ρ) > 0`. -/
def IsFiniteCopyDistillable (ρ : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∃ N : ℕ, IsNDistillable N ρ

/-- **Finite-copy undistillability** (DCLB Sec. II.2): `ρ` is `N`-undistillable for all `N`. -/
def IsFiniteCopyUndistillable (ρ : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∀ N : ℕ, IsNUndistillable N ρ

/-- For `N = 0`, every matrix is `0`-undistillable (and not `0`-distillable). -/
theorem isNUndistillable_zero (ρ : Matrix (A × B) (A × B) ℂ) :
    IsNUndistillable 0 ρ := by
  intro ψ _
  have h1 : Matrix.partialTransposeFst (bipartiteCopies 0 ρ) = 1 := by
    ext ⟨xA, xB⟩ ⟨yA, yB⟩
    have hx : xA = yA := Subsingleton.elim _ _
    have hy : xB = yB := Subsingleton.elim _ _
    subst hx hy
    simp [Matrix.partialTransposeFst_apply, bipartiteCopies_apply]
  rw [h1, Matrix.one_mulVec]
  have hre : (star ψ ⬝ᵥ ψ).re = ∑ p, Complex.normSq (ψ p) := by
    simp [dotProduct, Complex.mul_re, Complex.normSq_apply, mul_comm]
  rw [hre]
  exact Finset.sum_nonneg fun p _ => Complex.normSq_nonneg _

/-- `N`-undistillability is exact logical negation of `N`-distillability for every `N : ℕ`. -/
theorem isNUndistillable_iff_not_isNDistillable (N : ℕ) (ρ : Matrix (A × B) (A × B) ℂ) :
    IsNUndistillable N ρ ↔ ¬ IsNDistillable N ρ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [isNUndistillable_zero, IsNDistillable]
  · simp only [IsNUndistillable, IsNDistillable, hN, true_and, not_exists, not_and, not_lt]

/-- Finite-copy undistillability is the exact negation of finite-copy distillability. -/
theorem isFiniteCopyUndistillable_iff_not_isFiniteCopyDistillable
    (ρ : Matrix (A × B) (A × B) ℂ) :
    IsFiniteCopyUndistillable ρ ↔ ¬ IsFiniteCopyDistillable ρ := by
  simp [IsFiniteCopyUndistillable, IsFiniteCopyDistillable,
    isNUndistillable_iff_not_isNDistillable]

/-- Quantifying over all `N : ℕ` is equivalent to quantifying over all positive `N > 0`. -/
theorem isFiniteCopyUndistillable_iff_forall_pos (ρ : Matrix (A × B) (A × B) ℂ) :
    IsFiniteCopyUndistillable ρ ↔ ∀ N : ℕ, 0 < N → IsNUndistillable N ρ := by
  constructor
  · intro h N _; exact h N
  · intro h N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact isNUndistillable_zero ρ
    · exact h N hN

/-- Normalization independence for `IsNDistillable`: a witness may always be chosen unit-norm. -/
theorem isNDistillable_iff_unit_witness (N : ℕ) (ρ : Matrix (A × B) (A × B) ℂ) :
    IsNDistillable N ρ ↔
      0 < N ∧ ∃ ψ : (Fin N → A) × (Fin N → B) → ℂ,
        star ψ ⬝ᵥ ψ = 1 ∧ Matrix.HasSchmidtRankLE 2 ψ ∧
          (star ψ ⬝ᵥ Matrix.partialTransposeFst (bipartiteCopies N ρ) *ᵥ ψ).re < 0 := by
  rw [IsNDistillable, exists_unit_schmidtRankLE_two_neg_iff]

/-- Equivalence of `IsNDistillable` with DCLB Eq. (3) orthonormal two-term witnesses for PSD
operators `ρ`. -/
theorem isNDistillable_iff_dclbTwoTermForm
    (N : ℕ) {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef) :
    IsNDistillable N ρ ↔
      0 < N ∧ ∃ ψ : (Fin N → A) × (Fin N → B) → ℂ,
        HasDCLBTwoTermForm ψ ∧
          (star ψ ⬝ᵥ Matrix.partialTransposeFst (bipartiteCopies N ρ) *ᵥ ψ).re < 0 := by
  rw [IsNDistillable,
    exists_schmidtRankLE_two_neg_iff_exists_dclbTwoTermForm_neg (bipartiteCopies_posSemidef N hρ)]

/-- Equivalence of `IsNDistillable` with local `2 × 2` NPPT filters for Hermitian `ρ`. -/
theorem isNDistillable_iff_exists_filter_twoQubit_nppt
    (N : ℕ) {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.IsHermitian) :
    IsNDistillable N ρ ↔
      0 < N ∧ ∃ (K_A : Matrix (Fin 2) (Fin N → A) ℂ) (K_B : Matrix (Fin 2) (Fin N → B) ℂ),
        ¬ Matrix.IsPPT ((K_A ⊗ₖ K_B) * bipartiteCopies N ρ * (K_A ⊗ₖ K_B)ᴴ) := by
  have hρN : (bipartiteCopies N ρ).IsHermitian := by
    rw [Matrix.IsHermitian, conjTranspose_bipartiteCopies, hρ.eq]
  rw [IsNDistillable, exists_schmidtRankLE_two_neg_iff_exists_filter_twoQubit_nppt hρN]

/-- Equivalence of `IsNDistillable` with local 2D-subspace (co-isometric) `2 × 2` NPPT
projections for PSD `ρ`, valid in all finite dimensions (including `|A| < 2` or `|B| < 2`). -/
theorem isNDistillable_iff_exists_coisometry_twoQubit_nppt
    (N : ℕ) {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef) :
    IsNDistillable N ρ ↔
      0 < N ∧ ∃ (K_A : Matrix (Fin 2) (Fin N → A) ℂ) (K_B : Matrix (Fin 2) (Fin N → B) ℂ),
        K_A * K_Aᴴ = 1 ∧ K_B * K_Bᴴ = 1 ∧
          ¬ Matrix.IsPPT ((K_A ⊗ₖ K_B) * bipartiteCopies N ρ * (K_A ⊗ₖ K_B)ᴴ) := by
  rw [IsNDistillable,
    exists_schmidtRankLE_two_neg_iff_exists_coisometry_twoQubit_nppt
      (bipartiteCopies_posSemidef N hρ)]

/-- **PPT implies `N`-undistillable** (DCLB Sec. II.1): if `ρ^{T_A} ≥ 0`, then `ρ` is
`N`-undistillable for every `N`. -/
theorem isNUndistillable_of_partialTransposeFst_posSemidef (N : ℕ)
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : (Matrix.partialTransposeFst ρ).PosSemidef) :
    IsNUndistillable N ρ := by
  intro ψ _
  have hge := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
    (partialTransposeFst_bipartiteCopies_posSemidef N hρ)).2 ψ
  exact (Complex.le_def.mp hge).1

/-- **PPT implies finite-copy undistillable** (DCLB Sec. II.1): every PPT operator is
`N`-undistillable for all `N`. -/
theorem isFiniteCopyUndistillable_of_partialTransposeFst_posSemidef
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : (Matrix.partialTransposeFst ρ).PosSemidef) :
    IsFiniteCopyUndistillable ρ :=
  fun N => isNUndistillable_of_partialTransposeFst_posSemidef N hρ

/-- Specialization of `isFiniteCopyUndistillable_of_partialTransposeFst_posSemidef` to
`Matrix.IsPPT` on `Fin dA × Fin dB`. -/
theorem isFiniteCopyUndistillable_of_isPPT {dA dB : ℕ}
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ} (hρ : Matrix.IsPPT ρ) :
    IsFiniteCopyUndistillable ρ :=
  isFiniteCopyUndistillable_of_partialTransposeFst_posSemidef hρ

/-- **Sub-qubit edge case**: if `|A| ≤ 1` or `|B| ≤ 1`, every PSD operator is PPT and hence
finite-copy undistillable. -/
theorem isFiniteCopyUndistillable_of_card_le_one
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef)
    (hdim : Fintype.card A ≤ 1 ∨ Fintype.card B ≤ 1) :
    IsFiniteCopyUndistillable ρ := by
  apply isFiniteCopyUndistillable_of_partialTransposeFst_posSemidef
  rcases hdim with hA | hB
  · have : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp hA
    have hpt : Matrix.partialTransposeFst ρ = ρ := by
      ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      rw [Matrix.partialTransposeFst_apply, Subsingleton.elim a₂ a₁]
    rwa [hpt]
  · have : Subsingleton B := Fintype.card_le_one_iff_subsingleton.mp hB
    have hpt : Matrix.partialTransposeFst ρ = ρᵀ := by
      ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      rw [Matrix.partialTransposeFst_apply, Matrix.transpose_apply, Subsingleton.elim b₁ b₂]
    rw [hpt]
    exact hρ.transpose

/-- **Monotonicity step**: for a PSD matrix `ρ` with positive trace, `N`-distillability
implies `(N + 1)`-distillability. -/
theorem isNDistillable_succ {N : ℕ}
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef) (htr : 0 < ρ.trace.re)
    (hN : IsNDistillable N ρ) :
    IsNDistillable (N + 1) ρ := by
  classical
  obtain ⟨_, ψ, hsr, hneg⟩ := hN
  have hex_diag : ∃ p : A × B, 0 < (ρ p p).re := by
    by_contra hno
    push Not at hno
    have hle : ρ.trace.re ≤ 0 := by
      simpa [Matrix.trace, Matrix.diag] using
        Finset.sum_nonpos fun p (_ : p ∈ Finset.univ) => hno p
    linarith
  obtain ⟨⟨a₀, b₀⟩, hdiag_pos⟩ := hex_diag
  have hdiag_im : (ρ (a₀, b₀) (a₀, b₀)).im = 0 :=
    Complex.conj_eq_iff_im.mp (hρ.1.apply (a₀, b₀) (a₀, b₀))
  let ψ' : (Fin (N + 1) → A) × (Fin (N + 1) → B) → ℂ := fun p =>
    if p.1 (Fin.last N) = a₀ ∧ p.2 (Fin.last N) = b₀ then
      ψ (fun i => p.1 i.castSucc, fun i => p.2 i.castSucc)
    else 0
  refine ⟨Nat.succ_pos N, ψ', ?_, ?_⟩
  · obtain ⟨P, Q, hPQ⟩ := Matrix.exists_mul_eq_of_rank_le (Matrix.schmidtCoeffMatrix ψ) hsr
    let P' : Matrix (Fin (N + 1) → A) (Fin 2) ℂ :=
      Matrix.of fun x k => if x (Fin.last N) = a₀ then P (fun i => x i.castSucc) k else 0
    let Q' : Matrix (Fin 2) (Fin (N + 1) → B) ℂ :=
      Matrix.of fun k y => if y (Fin.last N) = b₀ then Q k (fun i => y i.castSucc) else 0
    have hfac : Matrix.schmidtCoeffMatrix ψ' = P' * Q' := by
      ext x y
      simp only [Matrix.schmidtCoeffMatrix_apply, ψ', Matrix.mul_apply, P', Q', Matrix.of_apply]
      by_cases hx : x (Fin.last N) = a₀ <;> by_cases hy : y (Fin.last N) = b₀
      · simp only [hx, hy, and_self, ↓reduceIte]
        exact (congrFun (congrFun hPQ (fun i => x i.castSucc)) (fun i => y i.castSucc)).symm
      · simp [hx, hy]
      · simp [hx, hy]
      · simp [hx, hy]
    rw [Matrix.HasSchmidtRankLE, Matrix.schmidtRank, hfac]
    exact (Matrix.rank_mul_le_left P' Q').trans (by simpa using Matrix.rank_le_card_width P')
  · let embA : (Fin N → A) → (Fin (N + 1) → A) := fun f => Fin.snoc f a₀
    let embB : (Fin N → B) → (Fin (N + 1) → B) := fun g => Fin.snoc g b₀
    let emb : (Fin N → A) × (Fin N → B) → (Fin (N + 1) → A) × (Fin (N + 1) → B) :=
      fun p => (embA p.1, embB p.2)
    have hemb_inj : Function.Injective emb := by
      intro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ h
      simp only [emb, embA, embB, Prod.mk.injEq] at h
      ext i
      · simpa using congrFun h.1 i.castSucc
      · simpa using congrFun h.2 i.castSucc
    have hvanish : ∀ p : (Fin (N + 1) → A) × (Fin (N + 1) → B),
        p ∉ Finset.univ.image emb → ψ' p = 0 := by
      intro ⟨x, y⟩ hp
      have hnot : ¬ (x (Fin.last N) = a₀ ∧ y (Fin.last N) = b₀) := by
        intro ⟨hx, hy⟩
        apply hp
        refine Finset.mem_image.mpr ⟨(fun i => x i.castSucc, fun i => y i.castSucc),
          Finset.mem_univ _, Prod.ext ?_ ?_⟩
        · ext j; refine Fin.lastCases (by simp [emb, embA, hx]) (fun i => by simp [emb, embA]) j
        · ext j; refine Fin.lastCases (by simp [emb, embB, hy]) (fun i => by simp [emb, embB]) j
      simp [ψ', hnot]
    have hquad : star ψ' ⬝ᵥ Matrix.partialTransposeFst (bipartiteCopies (N + 1) ρ) *ᵥ ψ' =
        ρ (a₀, b₀) (a₀, b₀) *
          (star ψ ⬝ᵥ Matrix.partialTransposeFst (bipartiteCopies N ρ) *ᵥ ψ) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb))
        (fun p _ hp => by simp [hvanish p hp]),
        Finset.sum_image (fun x _ y _ h => hemb_inj h)]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb))
        (fun q _ hq => by simp [hvanish q hq]),
        Finset.sum_image (fun x _ y _ h => hemb_inj h)]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hψ'p : ψ' (emb p) = ψ p := by simp [ψ', emb, embA, embB]
      have hψ'q : ψ' (emb q) = ψ q := by simp [ψ', emb, embA, embB]
      have hpt : Matrix.partialTransposeFst (bipartiteCopies (N + 1) ρ) (emb p) (emb q) =
          Matrix.partialTransposeFst (bipartiteCopies N ρ) p q * ρ (a₀, b₀) (a₀, b₀) := by
        simp only [Matrix.partialTransposeFst_apply, bipartiteCopies_apply, emb, embA, embB,
          Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      rw [Pi.star_apply, Pi.star_apply, hψ'p, hψ'q, hpt]
      ring
    rw [hquad, Complex.mul_re, hdiag_im, zero_mul, sub_zero]
    exact mul_neg_of_pos_of_neg hdiag_pos hneg

/-- **Monotonicity of `N`-distillability in `N`**: for a PSD matrix `ρ` with positive trace,
if `ρ` is `N`-distillable and `N ≤ M`, then `ρ` is `M`-distillable. -/
theorem isNDistillable_mono {N M : ℕ}
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef) (htr : 0 < ρ.trace.re)
    (hNM : N ≤ M) (hN : IsNDistillable N ρ) :
    IsNDistillable M ρ := by
  induction hNM with
  | refl => exact hN
  | step _ ih => exact isNDistillable_succ hρ htr ih

/-- **Antitonicity of `N`-undistillability in `N`**: for a PSD matrix `ρ` with positive trace,
`M`-undistillability implies `N`-undistillability for all `N ≤ M`. -/
theorem isNUndistillable_anti {N M : ℕ}
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef) (htr : 0 < ρ.trace.re)
    (hNM : N ≤ M) (hM : IsNUndistillable M ρ) :
    IsNUndistillable N ρ := by
  rw [isNUndistillable_iff_not_isNDistillable] at hM ⊢
  exact fun hN => hM (isNDistillable_mono hρ htr hNM hN)

/-- **DCLB Section II.3 (`ℂ² ⊗ ℂᵈ`)**: when `|A| ≤ 2` or `|B| ≤ 2`, a Hermitian operator `ρ`
is `1`-distillable iff it has a non-positive partial transpose. -/
theorem isNDistillable_one_iff_not_partialTransposeFst_posSemidef_of_card_le_two
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.IsHermitian)
    (hdim : Fintype.card A ≤ 2 ∨ Fintype.card B ≤ 2) :
    IsNDistillable 1 ρ ↔ ¬ (Matrix.partialTransposeFst ρ).PosSemidef := by
  constructor
  · intro h1 hpt
    exact (isNUndistillable_iff_not_isNDistillable 1 ρ).mp
      (isNUndistillable_of_partialTransposeFst_posSemidef 1 hpt) h1
  · intro hnppt
    rw [not_posSemidef_iff_exists_quadForm_re_neg (partialTransposeFst_isHermitian hρ)] at hnppt
    obtain ⟨ψ, hψ⟩ := hnppt
    let ψ1 : (Fin 1 → A) × (Fin 1 → B) → ℂ := fun p => ψ (p.1 0, p.2 0)
    refine ⟨Nat.one_pos, ψ1, ?_, ?_⟩
    · rw [Matrix.HasSchmidtRankLE]
      rcases hdim with hA | hB
      · exact (Matrix.schmidtRank_le_left ψ1).trans (by simpa using hA)
      · exact (Matrix.schmidtRank_le_right ψ1).trans (by simpa using hB)
    · let eA : (Fin 1 → A) ≃ A := Equiv.funUnique (Fin 1) A
      let eB : (Fin 1 → B) ≃ B := Equiv.funUnique (Fin 1) B
      let e : (Fin 1 → A) × (Fin 1 → B) ≃ A × B := Equiv.prodCongr eA eB
      have heq : star ψ1 ⬝ᵥ Matrix.partialTransposeFst (bipartiteCopies 1 ρ) *ᵥ ψ1 =
          star ψ ⬝ᵥ Matrix.partialTransposeFst ρ *ᵥ ψ := by
        simp only [dotProduct, Matrix.mulVec]
        refine Fintype.sum_equiv e _ _ fun p => ?_
        congr 1
        refine Fintype.sum_equiv e _ _ fun q => ?_
        simp [e, eA, eB, ψ1, Prod.map, Matrix.partialTransposeFst_apply, bipartiteCopies_apply]
      rw [heq]
      exact hψ

/-- **DCLB Section II.3 (`ℂ² ⊗ ℂᵈ`)**: when `|A| ≤ 2` or `|B| ≤ 2`, a Hermitian operator `ρ`
is finite-copy distillable iff it has a non-positive partial transpose. -/
theorem isFiniteCopyDistillable_iff_not_partialTransposeFst_posSemidef_of_card_le_two
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.IsHermitian)
    (hdim : Fintype.card A ≤ 2 ∨ Fintype.card B ≤ 2) :
    IsFiniteCopyDistillable ρ ↔ ¬ (Matrix.partialTransposeFst ρ).PosSemidef := by
  constructor
  · intro hdist hpt
    exact (isFiniteCopyUndistillable_iff_not_isFiniteCopyDistillable ρ).mp
      (isFiniteCopyUndistillable_of_partialTransposeFst_posSemidef hpt) hdist
  · intro hnppt
    exact ⟨1, (isNDistillable_one_iff_not_partialTransposeFst_posSemidef_of_card_le_two
      hρ hdim).mpr hnppt⟩

end FiniteCopyDistillability

end QuantumInfo
