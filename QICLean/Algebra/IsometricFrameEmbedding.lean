/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.Algebra.MatrixReindexUnitary
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

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
