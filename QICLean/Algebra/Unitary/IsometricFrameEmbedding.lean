/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.Matrix.Order

/-!
# Embedding a space while replacing its occupied frame

For isometries \(F:S\to H\) and \(W:S\to K\), the map
\(v\mapsto(WF^\dagger v,(I-FF^\dagger)v)\) embeds \(H\) isometrically
into \(K\oplus H\). It sends the occupied frame to \((W,0)\) and
retains its orthogonal complement. This construction places two isometric
frames in a common space, as in arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym; it is an auxiliary construction, not a theorem
stated separately in the paper. A general linear matrix whose underlying matrix is unitary
has its conjugate transpose as inverse.

## Main results

* `Matrix.isometricFrameEmbedding_isometry`, `Matrix.isometricFrameEmbedding_mul_frame`,
  `Matrix.isometricFrameEmbedding_intertwiner`.
* `Matrix.unitaryDirectSum`, `Matrix.unitaryDirectSumHom`.
* `Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup`.

Moved from TNLean, `TNLean/Algebra/IsometricFrameEmbedding.lean` and
`TNLean/Algebra/UnitaryGeneralLinearInverse.lean` at commit `49b78ed821` (Apache-2.0).

Moved from TNLean, `TNLean/MPS/MPDO/Vertical/VerticalCoisometry.lean`,
`TNLean/MPS/Preparation/BlockSum/DiagonalPolar.lean` at commit `021ba0bd19` (Apache-2.0).
-/

open scoped Matrix

namespace Matrix

variable {r d m : ℕ}

/-- Replace the frame \(F\) by \(W\), retaining the orthogonal complement
in a second summand. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
def isometricFrameEmbedding (F : Matrix (Fin d) (Fin r) ℂ)
    (W : Matrix (Fin m) (Fin r) ℂ) : Matrix (Fin m ⊕ Fin d) (Fin d) ℂ :=
  fromRows (W * Fᴴ) (1 - F * Fᴴ)

/-- Replacing one isometric frame by another preserves the inner product
on the entire original space. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem isometricFrameEmbedding_isometry
    (F : Matrix (Fin d) (Fin r) ℂ) (W : Matrix (Fin m) (Fin r) ℂ)
    (hF : Fᴴ * F = 1) (hW : Wᴴ * W = 1) :
    (isometricFrameEmbedding F W)ᴴ * isometricFrameEmbedding F W = 1 := by
  rw [isometricFrameEmbedding, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromRows]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_sub, conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc F Wᴴ, ← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul,
    Matrix.mul_assoc F Fᴴ, ← Matrix.mul_assoc Fᴴ F, hF, Matrix.one_mul]
  abel

/-- The original occupied frame is sent entirely into the target frame.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem isometricFrameEmbedding_mul_frame
    (F : Matrix (Fin d) (Fin r) ℂ) (W : Matrix (Fin m) (Fin r) ℂ)
    (hF : Fᴴ * F = 1) :
    isometricFrameEmbedding F W * F = fromRows W 0 := by
  simp only [isometricFrameEmbedding, fromRows_mul, Matrix.sub_mul,
    Matrix.one_mul, Matrix.mul_assoc, hF, Matrix.mul_one, sub_self]

/-- The adjoint of an intertwiner between unitary actions intertwines
in the opposite direction. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem conjTranspose_intertwiner_of_unitary
    (F : Matrix (Fin d) (Fin r) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (S : Matrix.unitaryGroup (Fin r) ℂ)
    (hInt : (U : Matrix (Fin d) (Fin d) ℂ) * F =
      F * (S : Matrix (Fin r) (Fin r) ℂ)) :
    Fᴴ * (U : Matrix (Fin d) (Fin d) ℂ) =
      (S : Matrix (Fin r) (Fin r) ℂ) * Fᴴ := by
  have h := congrArg Matrix.conjTranspose hInt
  have h' := congrArg (fun M : Matrix (Fin r) (Fin d) ℂ =>
    (S : Matrix (Fin r) (Fin r) ℂ) * M * (U : Matrix (Fin d) (Fin d) ℂ)) h
  simp only [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose] at h'
  rw [(mem_unitaryGroup_iff').mp (SetLike.coe_mem U), Matrix.mul_one,
    ← Matrix.mul_assoc (S : Matrix (Fin r) (Fin r) ℂ),
    (mem_unitaryGroup_iff).mp (SetLike.coe_mem S), Matrix.one_mul] at h'
  exact h'.symm

/-- Compatible unitary actions on the two occupied frames extend to
covariance of the full embedding. Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem isometricFrameEmbedding_intertwiner
    (F : Matrix (Fin d) (Fin r) ℂ) (W : Matrix (Fin m) (Fin r) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (V : Matrix.unitaryGroup (Fin m) ℂ)
    (S : Matrix.unitaryGroup (Fin r) ℂ)
    (hF : (U : Matrix (Fin d) (Fin d) ℂ) * F =
      F * (S : Matrix (Fin r) (Fin r) ℂ))
    (hW : (V : Matrix (Fin m) (Fin m) ℂ) * W =
      W * (S : Matrix (Fin r) (Fin r) ℂ)) :
    fromBlocks (V : Matrix (Fin m) (Fin m) ℂ) 0 0
        (U : Matrix (Fin d) (Fin d) ℂ) * isometricFrameEmbedding F W =
      isometricFrameEmbedding F W * (U : Matrix (Fin d) (Fin d) ℂ) := by
  have hAdj := conjTranspose_intertwiner_of_unitary F U S hF
  simp only [isometricFrameEmbedding, fromBlocks_mul_fromRows, fromRows_mul,
    Matrix.zero_mul, add_zero, zero_add]
  congr 1
  case e_A₂ =>
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc, hAdj] using congrArg
      (fun M : Matrix (Fin d) (Fin r) ℂ => (U : Matrix (Fin d) (Fin d) ℂ) - M * Fᴴ) hF
  simpa only [Matrix.mul_assoc, hAdj] using
    congrArg (fun M : Matrix (Fin m) (Fin r) ℂ => M * Fᴴ) hW

/-- Configuration-index form of the frame embedding, with the direct sum
enumerated by \(\operatorname{Fin}(m+d)\). Source context: arXiv:1010.3732,
Section II.F.2, equation eq:1d-sym:jointsym. -/
def finIsometricFrameEmbedding (F : Matrix (Fin d) (Fin r) ℂ)
    (W : Matrix (Fin m) (Fin r) ℂ) : Matrix (Fin (m + d)) (Fin d) ℂ :=
  (isometricFrameEmbedding F W).submatrix finSumFinEquiv.symm id

/-- Enumerating the target direct sum preserves the isometry identity.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem finIsometricFrameEmbedding_isometry
    (F : Matrix (Fin d) (Fin r) ℂ) (W : Matrix (Fin m) (Fin r) ℂ)
    (hF : Fᴴ * F = 1) (hW : Wᴴ * W = 1) :
    (finIsometricFrameEmbedding F W)ᴴ * finIsometricFrameEmbedding F W = 1 := by
  rw [finIsometricFrameEmbedding, conjTranspose_submatrix, submatrix_mul_equiv,
    isometricFrameEmbedding_isometry F W hF hW]
  rfl

/-- The direct sum of two unitaries, in configuration indices.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
def unitaryDirectSum (V : Matrix.unitaryGroup (Fin m) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix.unitaryGroup (Fin (m + d)) ℂ :=
  ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks (V : Matrix (Fin m) (Fin m) ℂ) 0 0 (U : Matrix (Fin d) (Fin d) ℂ)), by
    apply Matrix.reindex_mem_unitaryGroup
    rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      fromBlocks_conjTranspose, fromBlocks_multiply]
    simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      ← Matrix.star_eq_conjTranspose, (mem_unitaryGroup_iff).mp (SetLike.coe_mem V),
      (mem_unitaryGroup_iff).mp (SetLike.coe_mem U), fromBlocks_one]⟩

/-- The coordinate form of the embedding intertwines the
original action with the unitary direct sum. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem finIsometricFrameEmbedding_intertwiner
    (F : Matrix (Fin d) (Fin r) ℂ) (W : Matrix (Fin m) (Fin r) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (V : Matrix.unitaryGroup (Fin m) ℂ)
    (S : Matrix.unitaryGroup (Fin r) ℂ)
    (hF : (U : Matrix (Fin d) (Fin d) ℂ) * F =
      F * (S : Matrix (Fin r) (Fin r) ℂ))
    (hW : (V : Matrix (Fin m) (Fin m) ℂ) * W =
      W * (S : Matrix (Fin r) (Fin r) ℂ)) :
    (unitaryDirectSum V U : Matrix (Fin (m + d)) (Fin (m + d)) ℂ) *
        finIsometricFrameEmbedding F W =
      finIsometricFrameEmbedding F W * (U : Matrix (Fin d) (Fin d) ℂ) := by
  change (fromBlocks (V : Matrix (Fin m) (Fin m) ℂ) 0 0
      (U : Matrix (Fin d) (Fin d) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      (isometricFrameEmbedding F W).submatrix finSumFinEquiv.symm id =
    (isometricFrameEmbedding F W).submatrix finSumFinEquiv.symm id *
      (U : Matrix (Fin d) (Fin d) ℂ)
  rw [submatrix_mul_equiv, isometricFrameEmbedding_intertwiner F W U V S hF hW]
  exact (submatrix_mul_equiv (isometricFrameEmbedding F W)
    (U : Matrix (Fin d) (Fin d) ℂ) finSumFinEquiv.symm (Equiv.refl (Fin d)) id).symm

/-- Direct sum is a homomorphism of unitary groups.
Composing it with two unitary representations gives their common action.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
def unitaryDirectSumHom :
    Matrix.unitaryGroup (Fin m) ℂ × Matrix.unitaryGroup (Fin d) ℂ →*
      Matrix.unitaryGroup (Fin (m + d)) ℂ where
  toFun x := unitaryDirectSum x.1 x.2
  map_one' := by
    apply Subtype.ext
    change (fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0
      (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm = 1
    rw [fromBlocks_one, submatrix_one_equiv]
  map_mul' x y := by
    apply Subtype.ext
    change (fromBlocks
      ((x.1 : Matrix (Fin m) (Fin m) ℂ) * (y.1 : Matrix (Fin m) (Fin m) ℂ)) 0 0
      ((x.2 : Matrix (Fin d) (Fin d) ℂ) * (y.2 : Matrix (Fin d) (Fin d) ℂ))).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm =
      (fromBlocks (x.1 : Matrix (Fin m) (Fin m) ℂ) 0 0
        (x.2 : Matrix (Fin d) (Fin d) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      (fromBlocks (y.1 : Matrix (Fin m) (Fin m) ℂ) 0 0
        (y.2 : Matrix (Fin d) (Fin d) ℂ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    rw [submatrix_mul_equiv, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- The configuration-index embedding sends the occupied frame to the
prescribed target frame, with zero spectator component. Source context:
arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem finIsometricFrameEmbedding_mul_frame
    (F : Matrix (Fin d) (Fin r) ℂ) (W : Matrix (Fin m) (Fin r) ℂ)
    (hF : Fᴴ * F = 1) :
    finIsometricFrameEmbedding F W * F =
      (fromRows W 0).submatrix finSumFinEquiv.symm id := by
  change (isometricFrameEmbedding F W).submatrix finSumFinEquiv.symm id * F = _
  rw [← isometricFrameEmbedding_mul_frame F W hF]
  exact submatrix_mul_equiv (isometricFrameEmbedding F W) F
    finSumFinEquiv.symm (Equiv.refl (Fin d)) id

/-- The general linear inverse of a unitary matrix is its conjugate
transpose. This is a general matrix identity used for the pair
actions in arXiv:1010.3732, Section II.F.2, equation eq:1d-sym:jointsym. -/
theorem coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup
    {ι : Type*} [Fintype ι] [DecidableEq ι] (X : GL ι ℂ)
    (hX : (X : Matrix ι ι ℂ) ∈ unitaryGroup ι ℂ) :
    ((X⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) = (X : Matrix ι ι ℂ)ᴴ := by
  rw [coe_units_inv, ← star_eq_conjTranspose]
  exact inv_eq_left_inv (mem_unitaryGroup_iff'.mp hX)

end Matrix

section

open scoped Matrix BigOperators ComplexOrder

namespace Matrix

variable {r d s : ℕ} {dim : Fin r → ℕ}

/-- The block row whose sector indexed by `k` is the adjoint of `W k`.

For $W_k : \mathbb C^{D_k}\to\mathbb C^d$, this is the map
$U=\bigl(W_0^\dagger,\ldots,W_{r-1}^\dagger\bigr)^\mathsf T$ from
$\mathbb C^d$ to $\bigoplus_k\mathbb C^{D_k}$.

Source: arXiv:1606.00608, Proposition 4.13, lines 1863--1870. -/
noncomputable def sigmaBlockRow
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ) :
    Matrix ((k : Fin r) × Fin (dim k)) (Fin d) ℂ :=
  fun x a ↦ (W x.1)ᴴ x.2 a

@[simp]
theorem sigmaBlockRow_conjTranspose
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ) :
    (sigmaBlockRow W)ᴴ = fun a x ↦ W x.1 a x.2 := by
  ext a x
  simp [sigmaBlockRow]

/-- Left multiplication of a block row by a block-diagonal matrix acts on
each row sector separately. -/
theorem blockDiagonal'_mul_sigmaBlockRow
    (B : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ) :
    blockDiagonal' B * sigmaBlockRow W =
      fun x a ↦ (B x.1 * (W x.1)ᴴ) x.2 a := by
  classical
  ext ⟨k, x⟩ a
  simp only [Matrix.mul_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Fintype.sum_eq_single k]
  · simp [sigmaBlockRow]
  · intro l hl
    apply Finset.sum_eq_zero
    intro y hy
    rw [blockDiagonal'_apply_ne B x y hl.symm]
    exact zero_mul _

/-- Multiplication of the adjoint block row by a matrix with the same row
sectors is the sum of the corresponding sector products. -/
theorem sigmaBlockRow_conjTranspose_mul
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (C : (k : Fin r) → Matrix (Fin (dim k)) (Fin d) ℂ) :
    (sigmaBlockRow W)ᴴ *
        (show Matrix ((k : Fin r) × Fin (dim k)) (Fin d) ℂ from
          fun x a ↦ C x.1 x.2 a) =
      ∑ k, W k * C k := by
  classical
  ext a b
  calc
    ((sigmaBlockRow W)ᴴ *
        (show Matrix ((k : Fin r) × Fin (dim k)) (Fin d) ℂ from
          fun x a ↦ C x.1 x.2 a)) a b =
        ∑ x : (k : Fin r) × Fin (dim k), W x.1 a x.2 * C x.1 x.2 b := by
      rw [sigmaBlockRow_conjTranspose]
      rfl
    _ = ∑ k : Fin r, ∑ j : Fin (dim k), W k a j * C k j b :=
      Fintype.sum_sigma _
    _ = (∑ k, W k * C k) a b := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun k _ => rfl

/-- The Gram matrix of a block row is block diagonal when the ranges of its
constituent isometries are pairwise orthogonal. -/
theorem sigmaBlockRow_mul_conjTranspose
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (horth : ∀ k l, k ≠ l → (W k)ᴴ * W l = 0) :
    sigmaBlockRow W * (sigmaBlockRow W)ᴴ =
      blockDiagonal' (fun k ↦ (W k)ᴴ * W k) := by
  classical
  ext ⟨k, x⟩ ⟨l, y⟩
  by_cases hkl : k = l
  · subst l
    rw [blockDiagonal'_apply_eq]
    calc
      (sigmaBlockRow W * (sigmaBlockRow W)ᴴ) ⟨k, x⟩ ⟨k, y⟩ =
          ∑ j : Fin d, star (W k j x) * W k j y := by
        rw [sigmaBlockRow_conjTranspose]
        rfl
      _ = ((W k)ᴴ * W k) x y := rfl
  · rw [blockDiagonal'_apply_ne _ _ _ hkl]
    have h := congrFun (congrFun (horth k l hkl) x) y
    calc
      (sigmaBlockRow W * (sigmaBlockRow W)ᴴ) ⟨k, x⟩ ⟨l, y⟩ =
          ∑ j : Fin d, star (W k j x) * W l j y := by
        rw [sigmaBlockRow_conjTranspose]
        rfl
      _ = 0 := h

/-- The block row of pairwise orthogonal isometries is a coisometry.

This is the identity $UU^\dagger=I$ in the coisometry conclusion of
arXiv:1606.00608, Proposition 4.13, lines 1863--1870. -/
theorem sigmaBlockRow_isCoisometry
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hiso : ∀ k, (W k)ᴴ * W k = 1)
    (horth : ∀ k l, k ≠ l → (W k)ᴴ * W l = 0) :
    sigmaBlockRow W * (sigmaBlockRow W)ᴴ = 1 := by
  classical
  rw [sigmaBlockRow_mul_conjTranspose W horth]
  simp_rw [hiso]
  exact blockDiagonal'_one

/-- Intertwining on pairwise orthogonal sectors makes conjugation by their
block-row coisometry block diagonal.

This is the identity $U\widetilde M_vU^\dagger=\bigoplus_k B_k^v$ in
arXiv:1606.00608, Proposition 4.13, lines 1863--1870. -/
theorem sigmaBlockRow_conjugation
    (T : Fin s → Matrix (Fin d) (Fin d) ℂ)
    (B : (k : Fin r) → Fin s → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hiso : ∀ k, (W k)ᴴ * W k = 1)
    (horth : ∀ k l, k ≠ l → (W k)ᴴ * W l = 0)
    (hinter : ∀ k v, T v * W k = W k * B k v) :
    ∀ v, sigmaBlockRow W * T v * (sigmaBlockRow W)ᴴ =
      blockDiagonal' (fun k ↦ B k v) := by
  classical
  intro v
  ext ⟨k, x⟩ ⟨l, y⟩
  rw [Matrix.mul_assoc]
  have hleft :
      (sigmaBlockRow W * (T v * (sigmaBlockRow W)ᴴ)) ⟨k, x⟩ ⟨l, y⟩ =
        ∑ a : Fin d, star (W k a x) * (∑ b : Fin d, T v a b * W l b y) := by
    rw [sigmaBlockRow_conjTranspose]
    rfl
  rw [hleft]
  have hinter_entry (a : Fin d) :
      (∑ b : Fin d, T v a b * W l b y) = (W l * B l v) a y :=
    congrFun (congrFun (hinter l v) a) y
  simp_rw [hinter_entry]
  change ((W k)ᴴ * (W l * B l v)) x y = _
  rw [← Matrix.mul_assoc]
  by_cases hkl : k = l
  · subst l
    rw [hiso k, one_mul, blockDiagonal'_apply_eq]
  · rw [horth k l hkl, Matrix.zero_mul, blockDiagonal'_apply_ne _ _ _ hkl]
    rfl

/-- A literal sum of orthogonal sector corners is reconstructed by the
block-row coisometry and the corresponding block-diagonal matrix.

This conditional reverse identity follows directly from the assumed literal
sector decomposition; it is not a separate assertion attributed to the source. -/
theorem sigmaBlockRow_reconstruction
    (T : Fin s → Matrix (Fin d) (Fin d) ℂ)
    (B : (k : Fin r) → Fin s → Matrix (Fin (dim k)) (Fin (dim k)) ℂ)
    (W : (k : Fin r) → Matrix (Fin d) (Fin (dim k)) ℂ)
    (hreconstruct : ∀ v, T v = ∑ k, W k * B k v * (W k)ᴴ) :
    ∀ v, T v =
      (sigmaBlockRow W)ᴴ * blockDiagonal' (fun k ↦ B k v) * sigmaBlockRow W := by
  classical
  intro v
  rw [hreconstruct v, Matrix.mul_assoc,
    blockDiagonal'_mul_sigmaBlockRow (fun k ↦ B k v) W,
    sigmaBlockRow_conjTranspose_mul W (fun k ↦ B k v * (W k)ᴴ)]
  simp_rw [← Matrix.mul_assoc]

end Matrix

end

section

open scoped BigOperators Matrix ComplexOrder MatrixOrder

open Matrix


namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The isometry `J : ℂ^κ → ℂ^κ ⊗ ℂ^κ`, `|e⟩ ↦ |e e⟩`, onto the diagonal pairs. -/
def diagPairEmbedding (κ : Type*) [DecidableEq κ] : Matrix (κ × κ) κ ℂ :=
  of fun p e => if p.1 = e ∧ p.2 = e then 1 else 0

theorem diagPairEmbedding_mul_apply {ρ : Type*} (X : Matrix κ ρ ℂ) (p : κ × κ)
    (r : ρ) : (diagPairEmbedding κ * X) p r = if p.1 = p.2 then X p.1 r else 0 := by
  rw [mul_apply, Finset.sum_eq_single p.1]
  · by_cases h : p.1 = p.2
    · simp [diagPairEmbedding, h]
    · simp [diagPairEmbedding, h, Ne.symm h]
  · intro e _ he
    simp [diagPairEmbedding, Ne.symm he]
  · simp

theorem mul_conjTranspose_diagPairEmbedding_apply {ρ : Type*}
    (X : Matrix ρ κ ℂ) (r : ρ) (p : κ × κ) :
    (X * (diagPairEmbedding κ)ᴴ) r p = if p.1 = p.2 then X r p.1 else 0 := by
  rw [mul_apply, Finset.sum_eq_single p.1]
  · by_cases h : p.1 = p.2
    · simp [diagPairEmbedding, conjTranspose_apply, h]
    · simp [diagPairEmbedding, conjTranspose_apply, h, Ne.symm h]
  · intro e _ he
    simp [diagPairEmbedding, conjTranspose_apply, Ne.symm he]
  · simp

/-- `J` is an isometry, `Jᴴ J = 1`. -/
theorem conjTranspose_diagPairEmbedding_mul_self :
    (diagPairEmbedding κ)ᴴ * diagPairEmbedding κ = 1 := by
  ext e e'
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single e]
  · rw [Finset.sum_eq_single e]
    · by_cases h : e = e' <;> simp [diagPairEmbedding, conjTranspose_apply, h, one_apply]
    · intro x _ hx; simp [diagPairEmbedding, conjTranspose_apply, hx]
    · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [diagPairEmbedding, conjTranspose_apply, hx]
  · simp

/-- The entries of `J X Jᴴ` on diagonal pairs are the entries of `X`. -/
theorem diagPairEmbedding_mul_mul_conjTranspose_apply (X : Matrix κ κ ℂ) (c e : κ) :
    (diagPairEmbedding κ * X * (diagPairEmbedding κ)ᴴ) (c, c) (e, e) = X c e := by
  rw [mul_conjTranspose_diagPairEmbedding_apply, diagPairEmbedding_mul_apply]
  simp

end Matrix

end
