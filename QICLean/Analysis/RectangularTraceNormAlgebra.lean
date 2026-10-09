/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RectangularTraceNorm
import QICLean.Analysis.MatrixFramePerturbation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Algebra of the rectangular nuclear norm

Attained operator-contraction duality gives the triangle inequality, complex
scalar homogeneity and finite-sum estimates for the actual rectangular trace
norm. No positivity, Hermiticity or equality of ket and bra dimensions is
required. Empty matrix spaces are allowed.

These are original proofs of the scalar norm properties used to reinsert
physical matrix entries and sum expanded branches in *Polynomial PEPS
approximation of gapped square-grid ground states*, Theorem 5.2,
`04-compression.tex:518–561`, immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
No OpenAI Lean code is copied or adapted.
-/

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The zero rectangular matrix has zero nuclear norm, including empty
domains and codomains. -/
@[simp]
theorem rectangularTraceNorm_zero : rectangularTraceNorm (0 : Matrix m n ℂ) = 0 := by
  apply le_antisymm
  · apply rectangularTraceNorm_le_of_forall_contraction
    intro U _
    simp
  · exact rectangularTraceNorm_nonneg _

/-- The triangle inequality for arbitrary rectangular complex matrices.
Source: the branch sum in Theorem 5.2, `04-compression.tex:540–549`. -/
theorem rectangularTraceNorm_add_le (A B : Matrix m n ℂ) :
    rectangularTraceNorm (A + B) ≤ rectangularTraceNorm A + rectangularTraceNorm B := by
  apply rectangularTraceNorm_le_of_forall_contraction
  intro U hU
  rw [conjTranspose_add, Matrix.add_mul, trace_add]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_trace_conjTranspose_mul_le_rectangularTraceNorm A U hU)
    (norm_trace_conjTranspose_mul_le_rectangularTraceNorm B U hU))

/-- Complex scalar homogeneity of the rectangular nuclear norm preserves
arbitrary phases. Source: the coefficient sum in Theorem 5.2,
`04-compression.tex:518–549`. -/
@[simp]
theorem rectangularTraceNorm_smul (c : ℂ) (A : Matrix m n ℂ) :
    rectangularTraceNorm (c • A) = ‖c‖ * rectangularTraceNorm A := by
  apply le_antisymm
  · apply rectangularTraceNorm_le_of_forall_contraction
    intro U hU
    rw [conjTranspose_smul, Matrix.smul_mul, trace_smul, norm_smul, norm_star]
    exact mul_le_mul_of_nonneg_left
      (norm_trace_conjTranspose_mul_le_rectangularTraceNorm A U hU) (norm_nonneg c)
  · obtain ⟨U, hU, heq⟩ := exists_contraction_trace_conjTranspose_mul_eq A
    have h := norm_trace_conjTranspose_mul_le_rectangularTraceNorm (c • A) U hU
    rw [conjTranspose_smul, Matrix.smul_mul, trace_smul, norm_smul, norm_star,
      heq, Complex.norm_of_nonneg (rectangularTraceNorm_nonneg A)] at h
    exact h

/-- A finite rectangular matrix sum is bounded by the sum of its nuclear
norms. The empty sum has no exceptional case. Source: Theorem 5.2,
`eq:compression-total-error`. -/
theorem rectangularTraceNorm_sum_le {ι : Type*} (s : Finset ι)
    (A : ι → Matrix m n ℂ) :
    rectangularTraceNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, rectangularTraceNorm (A i) := by
  apply rectangularTraceNorm_le_of_forall_contraction
  intro U hU
  rw [conjTranspose_sum, Matrix.sum_mul, trace_sum]
  exact (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun i _ ↦ norm_trace_conjTranspose_mul_le_rectangularTraceNorm (A i) U hU)

/-- Complex branch coefficients enter the nuclear-norm sum through their
absolute values. Source: Theorem 5.2, `04-compression.tex:518–549`. -/
theorem rectangularTraceNorm_sum_smul_le {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (A : ι → Matrix m n ℂ) :
    rectangularTraceNorm (∑ i ∈ s, c i • A i) ≤
      ∑ i ∈ s, ‖c i‖ * rectangularTraceNorm (A i) := by
  simpa only [rectangularTraceNorm_smul] using
    rectangularTraceNorm_sum_le s (fun i ↦ c i • A i)

/-- Adjoint contraction tests give the nuclear norm bound in the opposite
rectangular orientation. -/
theorem rectangularTraceNorm_conjTranspose_le [DecidableEq m] (A : Matrix m n ℂ) :
    rectangularTraceNorm Aᴴ ≤ rectangularTraceNorm A := by
  apply rectangularTraceNorm_le_of_forall_contraction
  intro U hU
  have hpair : ((Aᴴ)ᴴ * U).trace = star ((Aᴴ * Uᴴ).trace) := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_conjTranspose, trace_mul_comm]
  rw [hpair, norm_star]
  exact norm_trace_conjTranspose_mul_le_rectangularTraceNorm A Uᴴ
    (by simpa only [l2_opNorm_conjTranspose] using hU)

/-- Passing to the adjoint preserves the nuclear norm, also when the
rectangular domain and codomain have unequal or zero dimensions. -/
@[simp]
theorem rectangularTraceNorm_conjTranspose [DecidableEq m] (A : Matrix m n ℂ) :
    rectangularTraceNorm Aᴴ = rectangularTraceNorm A := by
  exact le_antisymm (rectangularTraceNorm_conjTranspose_le A)
    (by simpa only [conjTranspose_conjTranspose] using rectangularTraceNorm_conjTranspose_le Aᴴ)

/-- Independent isometric embeddings of the ket and bra spaces preserve the
nuclear norm of an arbitrary rectangular matrix. This gives exact physical
reinsertion without any positivity hypothesis. Source: Theorem 5.2,
`04-compression.tex:535–538`. -/
theorem rectangularTraceNorm_isometry_sandwich
    {p q : Type*} [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq q]
    (A : Matrix m n ℂ) (K : Matrix p m ℂ) (L : Matrix q n ℂ)
    (hK : Kᴴ * K = 1) (hL : Lᴴ * L = 1) :
    rectangularTraceNorm (K * A * Lᴴ) = rectangularTraceNorm A := by
  classical
  have hKn := l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hK
  have hLn := l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hL
  apply le_antisymm
  · exact rectangularTraceNorm_mul_conjTranspose_le A K L hKn hLn
  · have h := rectangularTraceNorm_mul_conjTranspose_le (K * A * Lᴴ) Kᴴ Lᴴ
      (by simpa only [l2_opNorm_conjTranspose] using hKn)
      (by simpa only [l2_opNorm_conjTranspose] using hLn)
    have heq : Kᴴ * (K * A * Lᴴ) * (Lᴴ)ᴴ = A := by
      simp only [conjTranspose_conjTranspose, ← Matrix.mul_assoc, hK, Matrix.one_mul]
      rw [Matrix.mul_assoc, hL, Matrix.mul_one]
    simpa only [heq] using h

/-- Insert a fixed basis coordinate into the first factor of a product
register. This embedding is isometric and makes no assumption on the size
of the second register. -/
def basisRegisterInjection {X a : Type*} [DecidableEq X] [DecidableEq a]
    (x : X) : Matrix (X × a) a ℂ :=
  fun i j ↦ if i.1 = x then (1 : Matrix a a ℂ) i.2 j else 0

/-- The basis-register insertion is isometric, including a zero-dimensional
inserted domain. -/
theorem basisRegisterInjection_conjTranspose_mul_self
    {X a : Type*} [Fintype X] [Fintype a] [DecidableEq X] [DecidableEq a]
    (x : X) : (basisRegisterInjection (a := a) x)ᴴ *
      basisRegisterInjection (a := a) x = (1 : Matrix a a ℂ) := by
  ext i j
  simp [basisRegisterInjection, mul_apply, conjTranspose_apply, Fintype.sum_prod_type,
    one_apply, eq_comm]

/-- A pair of independent basis-register embeddings gives exactly a
matrix-unit Kronecker insertion. Source: Theorem 5.2,
`04-compression.tex:535–538`. -/
theorem basisRegisterInjection_sandwich_eq_single_kronecker
    {X Y a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq X] [DecidableEq Y] [DecidableEq a] [DecidableEq b]
    (x : X) (y : Y) (A : Matrix a b ℂ) :
    basisRegisterInjection x * A * (basisRegisterInjection y)ᴴ = single x y 1 ⊗ₖ A := by
  ext ⟨x', i⟩ ⟨y', j⟩
  by_cases hx : x' = x
  · subst x'
    by_cases hy : y' = y
    · subst y'
      simp [basisRegisterInjection, mul_apply, conjTranspose_apply, one_apply]
    · simp [basisRegisterInjection, mul_apply, conjTranspose_apply, one_apply,
        hy, Ne.symm hy]
  · simp [basisRegisterInjection, mul_apply, conjTranspose_apply, one_apply,
      hx, Ne.symm hx]

/-- Reinserting an arbitrary affected physical basis matrix unit preserves
the rectangular nuclear norm exactly. Source: Theorem 5.2,
`04-compression.tex:535–538`. -/
@[simp]
theorem rectangularTraceNorm_single_kronecker
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (x : X) (y : Y) (A : Matrix m n ℂ) :
    rectangularTraceNorm (single x y 1 ⊗ₖ A) = rectangularTraceNorm A := by
  classical
  rw [← basisRegisterInjection_sandwich_eq_single_kronecker]
  exact rectangularTraceNorm_isometry_sandwich A _ _
    (basisRegisterInjection_conjTranspose_mul_self x)
    (basisRegisterInjection_conjTranspose_mul_self y)

end Matrix
