/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RectangularTraceNorm
import QICLean.Analysis.RootChannel
import QICLean.Channel.PartialTrace

/-!
# Separate contraction maps followed by discarding a register

The trace norm contracts under `Z ↦ Tr_g(K Z L†)` when `K` and `L` are
independent rectangular contractions. The input may be rectangular, neither
Hermitian nor positive. The proof pulls a contraction test back through the
partial trace and uses dimension-independent amplification by an identity.

This is the exterior-map estimate `eq:compression-exterior-contraction` in
*Polynomial PEPS approximation of gapped square-grid ground states*, Theorem
5.2, `04-compression.tex:454–470`. These proofs are original, with no reuse of
OpenAI Lean code.
-/

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

namespace Matrix

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

omit [DecidableEq a] in
/-- The partial trace and identity amplification are adjoint for the
Hilbert--Schmidt pairing, without Hermiticity assumptions. -/
theorem trace_partialTraceRight_conjTranspose_mul
    (H : Matrix (a × b) (a × b) ℂ) (M : Matrix a a ℂ) :
    ((partialTraceRight H)ᴴ * M).trace = (Hᴴ * (M ⊗ₖ (1 : Matrix b b ℂ))).trace := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, partialTraceRight_apply,
    star_sum, Finset.sum_mul, Fintype.sum_prod_type, kroneckerMap_apply, one_apply,
    mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm

/-- Discarding a register does not increase the trace norm of an arbitrary
complex matrix. Theorem 5.2, `eq:compression-exterior-contraction`. -/
theorem rectangularTraceNorm_partialTraceRight_le
    (H : Matrix (a × b) (a × b) ℂ) :
    rectangularTraceNorm (partialTraceRight H) ≤ rectangularTraceNorm H := by
  apply rectangularTraceNorm_le_of_forall_contraction
  intro M hM
  rw [trace_partialTraceRight_conjTranspose_mul]
  exact norm_trace_conjTranspose_mul_le_rectangularTraceNorm H _
    ((l2_opNorm_kronecker_one_le M).trans hM)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq b] in
/-- The exterior calculation of Theorem 5.2 contracts the trace norm even for
an arbitrary nonpositive, non-Hermitian rectangular input and different ket
and bra maps. Source: `eq:compression-exterior-contraction`,
`04-compression.tex:454–470`. -/
theorem rectangularTraceNorm_partialTraceRight_mul_conjTranspose_le
    (Z : Matrix m n ℂ) (K : Matrix (a × b) m ℂ) (L : Matrix (a × b) n ℂ)
    (hK : ‖K‖ ≤ 1) (hL : ‖L‖ ≤ 1) :
    rectangularTraceNorm (partialTraceRight (K * Z * Lᴴ)) ≤ rectangularTraceNorm Z := by
  classical
  exact (rectangularTraceNorm_partialTraceRight_le _).trans
    (rectangularTraceNorm_mul_conjTranspose_le Z K L hK hL)

end Matrix
