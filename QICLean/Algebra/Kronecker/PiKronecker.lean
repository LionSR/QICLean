/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import Mathlib.Order.Interval.Finset.Fin

/-!
# The Kronecker product of a finite family of matrices

For a finite type of sites `ν` and a family of rectangular matrices `K k : Matrix (ι k) (κ k) ℂ`,
the Kronecker product `⊗ₖ K k` is the matrix from `(k : ν) → κ k` to `(k : ν) → ι k` with entries
`∏ₖ K k (x k) (y k)`. The row and column labels may vary with the site. A constant family
`fun _ : Fin M ↦ W` gives the tensor power `W^{⊗M}`, and a family of on-site matrices of a
system of sites gives its product operator `⊗_v m_v`.

The product is multiplicative, unital, and compatible with scalars, sums over choice
functions, the transpose, the conjugate transpose and the trace. It maps diagonal matrices to
diagonal matrices, vanishes exactly when one factor does, and preserves isometries,
coisometries, unitaries and basis inclusions.

## Main declarations

* `Matrix.piKronecker` — the Kronecker product `⊗ₖ K k` of a finite family of matrices.
* `Matrix.piKronecker_mul`, `Matrix.piKronecker_one`, `Matrix.piKronecker_smul`,
  `Matrix.sum_piKronecker`, `Matrix.piKronecker_kronecker`.
* `Matrix.conjTranspose_piKronecker`, `Matrix.transpose_piKronecker`,
  `Matrix.trace_piKronecker`, `Matrix.piKronecker_diagonal`.
* `Matrix.piKronecker_eq_zero_iff`, `Matrix.piKronecker_ne_zero`.
* `Matrix.piKronecker_mulVec_prod`, `Matrix.piKronecker_permMatrix_mulVec` — the action on
  product vectors and of on-site permutations.
* `Matrix.IsIsometry.piKronecker`, `Matrix.IsCoisometry.piKronecker`,
  `Matrix.IsUnitaryBetween.piKronecker`, `Matrix.piKronecker_mem_unitaryGroup`,
  `Matrix.piKronecker_basisInclusion`.
* `Matrix.sum_star_piKronecker_mulVec_mul`, `Matrix.sum_norm_sq_piKronecker_mulVec_le` — inner
  products and norms after a Kronecker product of partial isometries
  (arXiv:2307.01696, Supplemental Material, proof of Lemma 1).

Moved from TNLean, `TNLean/MPS/Tensor/TruncationCommutator.lean`,
`TNLean/MPS/MPU/DomainWall/FiniteGroupDetectorEndpoint.lean` at commit `021ba0bd19` (Apache-2.0).
-/

open scoped BigOperators Matrix ComplexOrder Kronecker

namespace Matrix

variable {ν : Type*} [Fintype ν] {ι κ μ : ν → Type*}

/-- The Kronecker product `⊗ₖ K k` of a finite family of rectangular matrices
`K k : Matrix (ι k) (κ k) ℂ` whose row and column labels may vary with the site `k`: the
matrix from `(k : ν) → κ k` to `(k : ν) → ι k` with entries `∏ₖ K k (x k) (y k)`. -/
def piKronecker (K : (k : ν) → Matrix (ι k) (κ k) ℂ) :
    Matrix ((k : ν) → ι k) ((k : ν) → κ k) ℂ :=
  Matrix.of fun x y ↦ ∏ k, K k (x k) (y k)

@[simp] theorem piKronecker_apply (K : (k : ν) → Matrix (ι k) (κ k) ℂ) (x : (k : ν) → ι k)
    (y : (k : ν) → κ k) : piKronecker K x y = ∏ k, K k (x k) (y k) :=
  rfl

/-- Kronecker products of composable families multiply sitewise. -/
theorem piKronecker_mul [∀ k, Fintype (κ k)] [DecidableEq ν]
    (K : (k : ν) → Matrix (ι k) (κ k) ℂ) (L : (k : ν) → Matrix (κ k) (μ k) ℂ) :
    piKronecker K * piKronecker L = piKronecker fun k ↦ K k * L k := by
  ext x y
  simp only [mul_apply, piKronecker_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun z _ ↦ (Finset.prod_mul_distrib).symm

/-- The Kronecker product of identities is the identity. -/
@[simp] theorem piKronecker_one [∀ k, DecidableEq (ι k)] :
    piKronecker (fun k ↦ (1 : Matrix (ι k) (ι k) ℂ)) = 1 := by
  ext x y
  simp only [piKronecker_apply, one_apply, Fintype.prod_boole, ← funext_iff]

/-- The Kronecker product of sitewise Kronecker products is the Kronecker product of the two
Kronecker products, read along the pairing of configurations. -/
theorem piKronecker_kronecker {ι' κ' : ν → Type*} (K : (k : ν) → Matrix (ι k) (κ k) ℂ)
    (L : (k : ν) → Matrix (ι' k) (κ' k) ℂ) :
    piKronecker (fun k ↦ K k ⊗ₖ L k) =
      reindex (Equiv.arrowProdEquivProdArrow ν ι ι').symm
        (Equiv.arrowProdEquivProdArrow ν κ κ').symm (piKronecker K ⊗ₖ piKronecker L) := by
  ext x y
  simp [kroneckerMap_apply, Finset.prod_mul_distrib]

/-- Multiplying every factor by the same scalar `c` multiplies the product by `c ^ |ν|`. -/
theorem piKronecker_smul (c : ℂ) (K : (k : ν) → Matrix (ι k) (κ k) ℂ) :
    piKronecker (fun k ↦ c • K k) = c ^ Fintype.card ν • piKronecker K := by
  ext x y
  simp [Finset.prod_mul_distrib, Finset.prod_const]

/-- Rescaling one factor by a scalar rescales the product by that scalar. -/
theorem piKronecker_update_smul [DecidableEq ν] (K : (k : ν) → Matrix (ι k) (κ k) ℂ) (i : ν)
    (c : ℂ) : piKronecker (Function.update K i (c • K i)) = c • piKronecker K := by
  ext x y
  simp only [piKronecker_apply, Matrix.smul_apply, smul_eq_mul]
  have hpt : ∀ k, (Function.update K i (c • K i)) k (x k) (y k) =
      Function.update (fun k ↦ K k (x k) (y k)) i (c * K i (x i) (y i)) k := by
    intro k
    rcases eq_or_ne k i with rfl | hk
    · simp
    · simp [Function.update_of_ne hk]
  rw [Finset.prod_congr rfl (fun k _ ↦ hpt k), Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun k ↦ K k (x k) (y k))]
  ring

/-- A Kronecker product with the factor `c • 1` at one site and the identity elsewhere is the
scalar `c`. -/
theorem piKronecker_ite_smul_one [DecidableEq ν] [∀ k, DecidableEq (ι k)] (j : ν) (c : ℂ) :
    piKronecker (fun k ↦ if k = j then c • (1 : Matrix (ι k) (ι k) ℂ) else 1) = c • 1 := by
  have h : (fun k ↦ if k = j then c • (1 : Matrix (ι k) (ι k) ℂ) else 1) =
      Function.update (fun k ↦ (1 : Matrix (ι k) (ι k) ℂ)) j (c • 1) := by
    funext k
    rcases eq_or_ne k j with rfl | hk
    · simp
    · simp [hk]
  rw [h, piKronecker_update_smul, piKronecker_one]

/-- Summing Kronecker products over all choice functions gives the Kronecker product of the
sums. -/
theorem sum_piKronecker [DecidableEq ν] {α : ν → Type*} [∀ k, Fintype (α k)]
    (K : (k : ν) → α k → Matrix (ι k) (κ k) ℂ) :
    ∑ J : (k : ν) → α k, piKronecker (fun k ↦ K k (J k)) =
      piKronecker fun k ↦ ∑ j, K k j := by
  ext x y
  simp only [Matrix.sum_apply, piKronecker_apply]
  exact (Fintype.prod_sum fun k j ↦ K k j (x k) (y k)).symm

/-- The conjugate transpose of a Kronecker product is the Kronecker product of the conjugate
transposes. -/
theorem conjTranspose_piKronecker (K : (k : ν) → Matrix (ι k) (κ k) ℂ) :
    (piKronecker K)ᴴ = piKronecker fun k ↦ (K k)ᴴ := by
  ext x y
  simp [conjTranspose_apply]

/-- The transpose of a Kronecker product is the Kronecker product of the transposes. -/
theorem transpose_piKronecker (K : (k : ν) → Matrix (ι k) (κ k) ℂ) :
    (piKronecker K)ᵀ = piKronecker fun k ↦ (K k)ᵀ := by
  ext x y
  simp

/-- The trace of a Kronecker product is the product of the traces. -/
theorem trace_piKronecker [DecidableEq ν] [∀ k, Fintype (ι k)]
    (K : (k : ν) → Matrix (ι k) (ι k) ℂ) : (piKronecker K).trace = ∏ k, (K k).trace := by
  simp only [trace, diag, piKronecker_apply]
  exact (Fintype.prod_sum fun k x ↦ K k x x).symm

/-- The Kronecker product of diagonal matrices is diagonal, with the products of the
entries. -/
theorem piKronecker_diagonal [∀ k, DecidableEq (ι k)] (f : (k : ν) → ι k → ℂ) :
    (piKronecker fun k ↦ diagonal (f k)) = diagonal fun x ↦ ∏ k, f k (x k) := by
  ext x y
  simp only [piKronecker_apply, diagonal_apply, Fintype.prod_ite_zero, ← funext_iff]

/-- A Kronecker product vanishes exactly when one of its factors does. -/
theorem piKronecker_eq_zero_iff (K : (k : ν) → Matrix (ι k) (κ k) ℂ) :
    piKronecker K = 0 ↔ ∃ k, K k = 0 := by
  constructor
  · intro h
    by_contra! hK
    have hentry (k : ν) : ∃ a b, K k a b ≠ 0 := by
      by_contra! h'
      exact hK k (Matrix.ext h')
    choose a b hab using hentry
    have := congrFun (congrFun h a) b
    rw [piKronecker_apply, Matrix.zero_apply] at this
    exact Finset.prod_ne_zero_iff.mpr (fun k _ ↦ hab k) this
  · rintro ⟨k, hk⟩
    ext x y
    rw [piKronecker_apply, Matrix.zero_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, Matrix.zero_apply])

/-- A Kronecker product of nonzero matrices is nonzero. -/
theorem piKronecker_ne_zero {K : (k : ν) → Matrix (ι k) (κ k) ℂ} (hK : ∀ k, K k ≠ 0) :
    piKronecker K ≠ 0 :=
  fun h ↦ let ⟨k, hk⟩ := (piKronecker_eq_zero_iff K).mp h; hK k hk

/-! ### Action on vectors -/

section Vector

variable [DecidableEq ν]

/-- A Kronecker product applied to a product vector `y ↦ ∏ₖ w k (y k)` is the product vector of
the one-site images. -/
theorem piKronecker_mulVec_prod [∀ k, Fintype (κ k)] (K : (k : ν) → Matrix (ι k) (κ k) ℂ)
    (w : (k : ν) → κ k → ℂ) :
    (piKronecker K *ᵥ fun y ↦ ∏ k, w k (y k)) = fun x ↦ ∏ k, (K k *ᵥ w k) (x k) := by
  funext x
  simp only [mulVec, dotProduct, piKronecker_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun k t ↦ K k (x k) t * w k t).symm

/-- **On-site permutations.** The Kronecker product of the permutation matrices of
permutations `e k` of the labels of the sites `k` acts on vectors as `w ↦ w ∘ e`, where `e`
applies `e k` at every site `k`. -/
theorem piKronecker_permMatrix_mulVec [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]
    (e : (k : ν) → Equiv.Perm (ι k)) (w : ((k : ν) → ι k) → ℂ) :
    piKronecker (fun k ↦ (e k).permMatrix ℂ) *ᵥ w = fun x ↦ w fun k ↦ e k (x k) := by
  funext x
  have h : ∀ y : (k : ν) → ι k, piKronecker (fun k ↦ (e k).permMatrix ℂ) x y =
      if y = (fun k ↦ e k (x k)) then 1 else 0 := fun y ↦ by
    simp only [piKronecker_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    rw [Finset.prod_boole]
    simp only [Finset.mem_univ, true_implies, funext_iff, eq_comm]
  simp only [mulVec, dotProduct, h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

end Vector

/-! ### Isometries and unitaries -/

section Isometry

variable [DecidableEq ν]

/-- A Kronecker product of isometries is an isometry. -/
theorem IsIsometry.piKronecker [∀ k, Fintype (ι k)] [∀ k, DecidableEq (κ k)]
    {K : (k : ν) → Matrix (ι k) (κ k) ℂ} (hK : ∀ k, (K k).IsIsometry) :
    (Matrix.piKronecker K).IsIsometry := by
  unfold IsIsometry at hK ⊢
  rw [conjTranspose_piKronecker, piKronecker_mul]
  simp only [hK, piKronecker_one]

/-- A Kronecker product of coisometries is a coisometry. -/
theorem IsCoisometry.piKronecker [∀ k, Fintype (κ k)] [∀ k, DecidableEq (ι k)]
    {K : (k : ν) → Matrix (ι k) (κ k) ℂ} (hK : ∀ k, (K k).IsCoisometry) :
    (Matrix.piKronecker K).IsCoisometry := by
  unfold IsCoisometry at hK ⊢
  rw [conjTranspose_piKronecker, piKronecker_mul]
  simp only [hK, piKronecker_one]

/-- A Kronecker product of matrices that are unitary between their coordinate spaces is unitary
between the configuration spaces. -/
theorem IsUnitaryBetween.piKronecker [∀ k, Fintype (ι k)] [∀ k, Fintype (κ k)]
    [∀ k, DecidableEq (ι k)] [∀ k, DecidableEq (κ k)] {K : (k : ν) → Matrix (ι k) (κ k) ℂ}
    (hK : ∀ k, (K k).IsUnitaryBetween) : (Matrix.piKronecker K).IsUnitaryBetween :=
  ⟨IsIsometry.piKronecker fun k ↦ (hK k).1, IsCoisometry.piKronecker fun k ↦ (hK k).2⟩

/-- A Kronecker product of unitaries is unitary. -/
theorem piKronecker_mem_unitaryGroup [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]
    {K : (k : ν) → Matrix (ι k) (ι k) ℂ} (hK : ∀ k, K k ∈ unitaryGroup (ι k) ℂ) :
    piKronecker K ∈ unitaryGroup ((k : ν) → ι k) ℂ :=
  (isUnitaryBetween_iff_mem_unitaryGroup _).mp
    (IsUnitaryBetween.piKronecker fun k ↦ (isUnitaryBetween_iff_mem_unitaryGroup _).mpr (hK k))

omit [DecidableEq ν] in
/-- The Kronecker product of the basis inclusions along injections `e k` is the basis inclusion
along the product injection. -/
theorem piKronecker_basisInclusion [∀ k, DecidableEq (κ k)] (e : ∀ k, ι k ↪ κ k) :
    piKronecker (fun k ↦ basisInclusion (e k)) =
      basisInclusion (Function.Embedding.piCongrRight e) := by
  ext y x
  simp [basisInclusion, one_apply, funext_iff, Finset.prod_ite_zero]

/-- `⟨(⊗ₖ W k) ψ, (⊗ₖ W' k) φ⟩ = ⟨ψ, (⊗ₖ (W k)ᴴ W' k) φ⟩`. -/
theorem sum_star_piKronecker_mulVec_mul {n : ν → Type*} [∀ k, Fintype (n k)]
    [∀ k, Fintype (κ k)] [∀ k, Fintype (μ k)] (W : (k : ν) → Matrix (n k) (κ k) ℂ)
    (W' : (k : ν) → Matrix (n k) (μ k) ℂ) (ψ : ((k : ν) → κ k) → ℂ)
    (φ : ((k : ν) → μ k) → ℂ) :
    ∑ s, star ((piKronecker W *ᵥ ψ) s) * (piKronecker W' *ᵥ φ) s =
      ∑ τ, star (ψ τ) * ((piKronecker fun k ↦ (W k)ᴴ * W' k) *ᵥ φ) τ := by
  change star (piKronecker W *ᵥ ψ) ⬝ᵥ (piKronecker W' *ᵥ φ) =
    star ψ ⬝ᵥ ((piKronecker fun k ↦ (W k)ᴴ * W' k) *ᵥ φ)
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, conjTranspose_piKronecker,
    piKronecker_mul]

/-- **Partial isometries do not increase norms.** If every `(W k)ᴴ W k` is a projector, then
`‖(⊗ₖ W k) ψ‖ ≤ ‖ψ‖`. For the partial isometry `V` of the polar decomposition, `Vᴴ V = Π` is the
projector onto the range of `P` (arXiv:2307.01696, Supplemental Material, proof of Lemma 1). -/
theorem sum_norm_sq_piKronecker_mulVec_le {n : ν → Type*} [∀ k, Fintype (n k)]
    [∀ k, Fintype (κ k)] {W : (k : ν) → Matrix (n k) (κ k) ℂ}
    (hidem : ∀ k, ((W k)ᴴ * W k) * ((W k)ᴴ * W k) = (W k)ᴴ * W k)
    (ψ : ((k : ν) → κ k) → ℂ) :
    ∑ s, ‖(piKronecker W *ᵥ ψ) s‖ ^ 2 ≤ ∑ τ, ‖ψ τ‖ ^ 2 := by
  classical
  set Pr := piKronecker fun k ↦ (W k)ᴴ * W k
  have hH : Prᴴ = Pr := by
    simp only [Pr, conjTranspose_piKronecker, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hI : Pr * Pr = Pr := by simp only [Pr, piKronecker_mul, hidem]
  have hpsd : (1 - Pr).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (1 - Pr)
    have e : (1 - Pr)ᴴ * (1 - Pr) = 1 - Pr := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hI]
      abel
    rwa [e] at h
  have hnn := hpsd.dotProduct_mulVec_nonneg ψ
  have h1 : ((∑ s, ‖(piKronecker W *ᵥ ψ) s‖ ^ 2 : ℝ) : ℂ) =
      ∑ s, star ((piKronecker W *ᵥ ψ) s) * (piKronecker W *ᵥ ψ) s := by
    push_cast
    exact Finset.sum_congr rfl fun x _ ↦ by rw [Complex.star_def, Complex.conj_mul']
  have h2 : ((∑ τ, ‖ψ τ‖ ^ 2 : ℝ) : ℂ) = ∑ τ, star (ψ τ) * ψ τ := by
    push_cast
    exact Finset.sum_congr rfl fun x _ ↦ by rw [Complex.star_def, Complex.conj_mul']
  rw [sum_star_piKronecker_mulVec_mul] at h1
  have key : ((∑ τ, ‖ψ τ‖ ^ 2 - ∑ s, ‖(piKronecker W *ᵥ ψ) s‖ ^ 2 : ℝ) : ℂ) =
      star ψ ⬝ᵥ ((1 - Pr) *ᵥ ψ) := by
    rw [Complex.ofReal_sub, h1, h2, sub_mulVec, one_mulVec, dotProduct_sub]
    rfl
  rw [← key] at hnn
  have := Complex.zero_le_real.1 hnn
  linarith

end Isometry

end Matrix

section

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The group commutator** `U₂† U₁† U₂ U₁` of two operators, the operator whose expectation
value detects the anomaly in arXiv:2405.00439, `detecZ2`, `Papers/2405.00439/MPU-DW.tex`
lines 2097--2102, with `U₁ = U^{[i₁,j₁]}` and `U₂ = U^{[i₂,j₂]}`. -/
def groupCommutator (U₁ U₂ : Matrix n n ℂ) : Matrix n n ℂ :=
  U₂ᴴ * U₁ᴴ * U₂ * U₁

/-- **The commutator of two unitaries acts by the exchange phase.** If `U₁† U₁ = 1`,
`U₂† U₂ = 1` and `U₂ U₁ ψ = c U₁ U₂ ψ`, then `U₂† U₁† U₂ U₁ ψ = c ψ`.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2097--2102 (the expectation
value of the commutator "precisely measures the commutator between `U^{[i₁,j₁]}` and
`U^{[i₂,j₂]}`"). -/
theorem groupCommutator_mulVec_eq_smul {U₁ U₂ : Matrix n n ℂ} (hU₁ : U₁ᴴ * U₁ = 1)
    (hU₂ : U₂ᴴ * U₂ = 1) {ψ : n → ℂ} {c : ℂ} (h : U₂ *ᵥ (U₁ *ᵥ ψ) = c • (U₁ *ᵥ (U₂ *ᵥ ψ))) :
    groupCommutator U₁ U₂ *ᵥ ψ = c • ψ := by
  have hc : groupCommutator U₁ U₂ *ᵥ ψ = U₂ᴴ *ᵥ (U₁ᴴ *ᵥ (U₂ *ᵥ (U₁ *ᵥ ψ))) := by
    simp only [groupCommutator, mulVec_mulVec, Matrix.mul_assoc]
  rw [hc, h, mulVec_smul, mulVec_smul, mulVec_mulVec _ U₁ᴴ U₁, hU₁, one_mulVec,
    mulVec_mulVec _ U₂ᴴ U₂, hU₂, one_mulVec]

/-- **The expectation value of the commutator** (arXiv:2405.00439, `detecZ2`,
`Papers/2405.00439/MPU-DW.tex` lines 2097--2102): if `U₁`, `U₂` are unitary and
`U₂ U₁ ψ = c U₁ U₂ ψ`, then `⟨ψ| U₂† U₁† U₂ U₁ |ψ⟩ = c ⟨ψ|ψ⟩`. -/
theorem star_dotProduct_groupCommutator_mulVec {U₁ U₂ : Matrix n n ℂ} (hU₁ : U₁ᴴ * U₁ = 1)
    (hU₂ : U₂ᴴ * U₂ = 1) {ψ : n → ℂ} {c : ℂ} (h : U₂ *ᵥ (U₁ *ᵥ ψ) = c • (U₁ *ᵥ (U₂ *ᵥ ψ))) :
    star ψ ⬝ᵥ (groupCommutator U₁ U₂ *ᵥ ψ) = c * (star ψ ⬝ᵥ ψ) := by
  rw [groupCommutator_mulVec_eq_smul hU₁ hU₂ h, dotProduct_smul, smul_eq_mul]

section OnSite

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **The truncation of an on-site symmetry** `⊗_{i ∈ S} u` to a set `S` of sites of a chain of
`N` sites: `u` on the sites of `S` and the identity elsewhere.

Source: arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex` lines 2104--2105 (truncating
`U = ⊗_{i ∈ Λ} u^{[i]}` gives `U^{[a,b]} = ⊗_{i ∈ [a,b]} u^{[i]}`). -/
noncomputable def onSiteTruncation (u : Matrix ι ι ℂ) (S : Finset (Fin N)) :
    Matrix (Fin N → ι) (Fin N → ι) ℂ :=
  Matrix.piKronecker fun k ↦ if k ∈ S then u else 1

omit [Fintype ι] in
/-- The truncation of an on-site symmetry to all sites is the symmetry `u^{⊗N}`. -/
theorem onSiteTruncation_univ (u : Matrix ι ι ℂ) :
    onSiteTruncation u (Finset.univ : Finset (Fin N)) = Matrix.piKronecker fun _ : Fin N ↦ u := by
  simp [onSiteTruncation]

/-- A truncation of an on-site symmetry with `u† u = 1` satisfies the same relation. -/
theorem onSiteTruncation_conjTranspose_mul_self {u : Matrix ι ι ℂ} (hu : uᴴ * u = 1)
    (S : Finset (Fin N)) : (onSiteTruncation u S)ᴴ * onSiteTruncation u S = 1 := by
  rw [onSiteTruncation, Matrix.conjTranspose_piKronecker, Matrix.piKronecker_mul]
  convert Matrix.piKronecker_one (ι := fun _ : Fin N ↦ ι) using 2
  funext k
  split_ifs <;> simp [hu]

/-- **Truncations of an on-site symmetry commute up to the identity** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 2104--2106): for `u† u = 1` and any two sets of sites,
`(U^{S₂})† (U^{S₁})† U^{S₂} U^{S₁} = 1`. On every site the four factors are powers of `u`
and `u†`, and they cancel. -/
theorem groupCommutator_onSiteTruncation {u : Matrix ι ι ℂ} (hu : uᴴ * u = 1)
    (S₁ S₂ : Finset (Fin N)) :
    groupCommutator (onSiteTruncation u S₁) (onSiteTruncation u S₂) = 1 := by
  rw [groupCommutator, onSiteTruncation, onSiteTruncation, Matrix.conjTranspose_piKronecker,
    Matrix.conjTranspose_piKronecker, Matrix.piKronecker_mul, Matrix.piKronecker_mul,
    Matrix.piKronecker_mul]
  convert Matrix.piKronecker_one (ι := fun _ : Fin N ↦ ι) using 2
  funext k
  split_ifs <;> simp [hu, Matrix.mul_assoc]

/-- **The anomaly detector of an on-site symmetry is one** (arXiv:2405.00439,
`Papers/2405.00439/MPU-DW.tex` lines 2104--2106): for `u† u = 1`, any two sets of sites and a
normalized state `ψ`, `⟨ψ| (U^{S₂})† (U^{S₁})† U^{S₂} U^{S₁} |ψ⟩ = 1`, in agreement with the
trivial anomaly `ω = 1` of on-site symmetries. -/
theorem star_dotProduct_groupCommutator_onSiteTruncation_mulVec {u : Matrix ι ι ℂ}
    (hu : uᴴ * u = 1) (S₁ S₂ : Finset (Fin N)) {ψ : (Fin N → ι) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star ψ ⬝ᵥ (groupCommutator (onSiteTruncation u S₁) (onSiteTruncation u S₂) *ᵥ ψ) = 1 := by
  rw [groupCommutator_onSiteTruncation hu, one_mulVec, hψ]

local notation "σX" => !![(0 : ℂ), 1; 1, 0]

local notation "σZ" => !![(1 : ℂ), 0; 0, -1]

/-- A truncation of an on-site symmetry dressed by a unitary `w` at one site is still unitary. -/
theorem dressed_onSiteTruncation_conjTranspose_mul_self {u w : Matrix ι ι ℂ} (hu : uᴴ * u = 1)
    (hw : wᴴ * w = 1) (S : Finset (Fin N)) (j : Fin N) :
    (onSiteTruncation w {j} * onSiteTruncation u S)ᴴ *
        (onSiteTruncation w {j} * onSiteTruncation u S) = 1 := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (onSiteTruncation w {j})ᴴ,
    onSiteTruncation_conjTranspose_mul_self hw, Matrix.one_mul,
    onSiteTruncation_conjTranspose_mul_self hu]

/-- **The anomaly detector depends on the endpoints of the truncations.** For the on-site
symmetry `X^{⊗N}`, whose anomaly is trivial, take the truncations
`U₁ = Z_{j₁} X^{S₁}` and `U₂ = Z_{j₂} X^{S₂}`, each dressed by the Pauli matrix `Z` at one
endpoint. If `j₁ ∈ S₂`, `j₂ ∉ S₁` and `j₁ ≠ j₂`, then `U₂† U₁† U₂ U₁ = -1`.

These are circuit truncations in the sense of arXiv:2405.00439, `Papers/2405.00439/MPU-DW.tex`
lines 2081--2087. The symmetry `X^{⊗N}` is the depth-two circuit whose first layer applies
`X ⊗ ZX` to the pairs of sites `(2k, 2k+1)` and whose second layer applies `Z` to every odd site,
a gate on the pair `(2k+1, 2k+2)`; indeed `Z · ZX = X`. Dropping the gates that are not
contained in an interval `[i, j]` with `i` even and `j` odd keeps both factors on every odd
site of `[i, j]` except `j`, which keeps only `ZX`, so the truncation is `Z_j X^{⊗[i,j]}`; this
identification of the circuit truncation is not formalized.
For `i₂ < i₁ < j₁ < j₂` of these parities the hypotheses hold, and the expectation value of the
commutator on every normalized state is `-1`, not the trivial anomaly `1`
(`star_dotProduct_groupCommutator_dressed_onSiteTruncation_pauliX`).

This is a counterexample to arXiv:2405.00439, `detecZ2`, lines 2097--2102, read for an
arbitrary circuit truncation. -/
theorem groupCommutator_dressed_onSiteTruncation_pauliX {S₁ S₂ : Finset (Fin N)} {j₁ j₂ : Fin N}
    (hj₁ : j₁ ∈ S₂) (hj₂ : j₂ ∉ S₁) (hj : j₁ ≠ j₂) :
    groupCommutator (onSiteTruncation σZ {j₁} * onSiteTruncation σX S₁)
        (onSiteTruncation σZ {j₂} * onSiteTruncation σX S₂) = -1 := by
  simp only [groupCommutator, onSiteTruncation, Matrix.piKronecker_mul,
      Matrix.conjTranspose_piKronecker]
  rw [← neg_one_smul ℂ (1 : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ),
    ← Matrix.piKronecker_ite_smul_one (ι := fun _ ↦ Fin 2) j₁]
  congr 1
  funext k
  simp only [Finset.mem_singleton]
  by_cases hk₁ : k = j₁
  · subst hk₁
    simp only [hj₁, hj, ite_true, ite_false]
    split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · by_cases hk₂ : k = j₂
    · subst hk₂
      simp only [hj₂, hk₁, ite_true, ite_false]
      split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp only [hk₁, hk₂, ite_false]
      split_ifs <;> ext a b <;> fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The detector of the dressed truncations is `-1`** (arXiv:2405.00439, `detecZ2`,
`Papers/2405.00439/MPU-DW.tex` lines 2097--2102): for the truncations of
`groupCommutator_dressed_onSiteTruncation_pauliX` and every normalized state `ψ`,
`⟨ψ| U₂† U₁† U₂ U₁ |ψ⟩ = -1`, although the on-site symmetry `X^{⊗N}` has trivial anomaly. -/
theorem star_dotProduct_groupCommutator_dressed_onSiteTruncation_pauliX {S₁ S₂ : Finset (Fin N)}
    {j₁ j₂ : Fin N} (hj₁ : j₁ ∈ S₂) (hj₂ : j₂ ∉ S₁) (hj : j₁ ≠ j₂)
    {ψ : (Fin N → Fin 2) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star ψ ⬝ᵥ (groupCommutator (onSiteTruncation σZ {j₁} * onSiteTruncation σX S₁)
        (onSiteTruncation σZ {j₂} * onSiteTruncation σX S₂) *ᵥ ψ) = -1 := by
  rw [groupCommutator_dressed_onSiteTruncation_pauliX hj₁ hj₂ hj, neg_mulVec, one_mulVec,
    dotProduct_neg, hψ]

end OnSite

end Matrix

end

section

open scoped Matrix

namespace Matrix

variable {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The interval truncation `wₐ u^[a,b]`, dressed at its left endpoint.
Source context: arXiv:2405.00439, Section V, lines 2081–2087 and `detectG`.
The dressing is an explicit choice, not a hypothesis implicit in that source. -/
noncomputable def leftDressedOnSiteInterval (u w : Matrix ι ι ℂ) (a b : Fin N) :
    Matrix (Fin N → ι) (Fin N → ι) ℂ :=
  onSiteTruncation w {a} * onSiteTruncation u (Finset.Icc a b)

/-- The six-factor detector at group-element order two, with forward action
`T₀₀`, then `T₁₁`, then `T₂₂` on kets. Source: arXiv:2405.00439, `detectG`,
lines 2108–2117. The order of multiplication is specified explicitly. -/
def cyclicTwoTruncationDetector (T : Fin N → Fin N → Matrix ι ι ℂ)
    (a₀ a₁ a₂ b₀ b₁ b₂ : Fin N) : Matrix ι ι ℂ :=
  (T a₀ b₁)ᴴ * (T a₂ b₂)ᴴ * (T a₁ b₀)ᴴ * T a₂ b₂ * T a₁ b₁ * T a₀ b₀

/-- Every interval in a left-dressed on-site family is unitary if both one-site
matrices are unitary. Source context: arXiv:2405.00439, Section V, lines
2081–2087. This is a property of the explicit family, not a circuit comparison. -/
theorem leftDressedOnSiteInterval_conjTranspose_mul_self {u w : Matrix ι ι ℂ}
    (hu : uᴴ * u = 1) (hw : wᴴ * w = 1) (a b : Fin N) :
    (leftDressedOnSiteInterval u w a b)ᴴ * leftDressedOnSiteInterval u w a b = 1 :=
  dressed_onSiteTruncation_conjTranspose_mul_self hu hw (Finset.Icc a b) a

local notation "σX" => !![(0 : ℂ), 1; 1, 0]

local notation "σZ" => !![(1 : ℂ), 0; 0, -1]

/-- The chronological finite-group detector at order two is `-1` for the coherent
left-endpoint dressings `T(a,b) = Zₐ X^[a,b]` and the printed cut order.

Project counterexample to the arbitrary-truncation reading of arXiv:2405.00439,
`detectG`, lines 2108–2117. The six-factor matrix identity is formalized here;
the fixed-circuit identification and the general even-order extension are separate
claims in `docs/audits/2026-11-15_finite_group_detector_endpoints.md`. -/
theorem cyclicTwoTruncationDetector_leftDressedOnSiteInterval_pauliX
    {a₀ a₁ a₂ b₀ b₁ b₂ : Fin N}
    (h₀ : a₀ < a₂) (h₁ : a₂ < a₁) (h₂ : a₁ < b₀)
    (h₃ : b₀ < b₂) (h₄ : b₂ < b₁) :
    cyclicTwoTruncationDetector (leftDressedOnSiteInterval σX σZ)
      a₀ a₁ a₂ b₀ b₁ b₂ = -1 := by
  simp only [cyclicTwoTruncationDetector, leftDressedOnSiteInterval,
    onSiteTruncation, Matrix.piKronecker_mul, Matrix.conjTranspose_piKronecker]
  rw [← neg_one_smul ℂ (1 : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ),
    ← Matrix.piKronecker_ite_smul_one (ι := fun _ ↦ Fin 2) a₁]
  congr 1
  funext k
  simp only [Finset.mem_singleton, Finset.mem_Icc, Fin.le_def, Fin.ext_iff]
  simp only [Fin.lt_def] at h₀ h₁ h₂ h₃ h₄
  split_ifs <;> first
    | omega
    | (ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two])

/-- The six-factor finite-group detector of the explicit dressed interval family
has expectation `-1` on every normalized state. Source context:
arXiv:2405.00439, `detectG`, lines 2108–2117; this is the matrix counterexample
above, not the claimed anomaly detection theorem. -/
theorem star_dotProduct_cyclicTwoTruncationDetector_leftDressedOnSiteInterval_pauliX
    {a₀ a₁ a₂ b₀ b₁ b₂ : Fin N}
    (h₀ : a₀ < a₂) (h₁ : a₂ < a₁) (h₂ : a₁ < b₀)
    (h₃ : b₀ < b₂) (h₄ : b₂ < b₁)
    {ψ : (Fin N → Fin 2) → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star ψ ⬝ᵥ (cyclicTwoTruncationDetector (leftDressedOnSiteInterval σX σZ)
      a₀ a₁ a₂ b₀ b₁ b₂ *ᵥ ψ) = -1 := by
  rw [cyclicTwoTruncationDetector_leftDressedOnSiteInterval_pauliX h₀ h₁ h₂ h₃ h₄,
    neg_mulVec, one_mulVec, dotProduct_neg, hψ]

end Matrix

end
