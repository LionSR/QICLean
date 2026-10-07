/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RectangularTraceNormAlgebra
import QICLean.Channel.RectangularTraceNormContraction

/-!
# Absolute density error for subnormalized pure vectors

The outer product of independent finite Euclidean ket and bra vectors has
nuclear norm at most the product of their vector norms. Splitting a difference
of pure densities into two such products gives the absolute density error
bound, without dividing by either vector norm. Discarding a register preserves
this estimate.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
Theorem 5.2, the source-only reduction and
`eq:compression-effect-circuit-error`, `04-compression.tex:199–229`, immutable
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are original proofs; no OpenAI Lean code is copied or adapted.
-/

/-
Provenance-ID: p09-qic-pure-euclideanouterproduct
Downstream declaration: Matrix.euclideanOuterProduct
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-pure-trace_euclideanouterproduct_conjtranspose_mul
Downstream declaration: Matrix.trace_euclideanOuterProduct_conjTranspose_mul
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-pure-rectangulartracenorm_euclideanouterproduct_le
Downstream declaration: Matrix.rectangularTraceNorm_euclideanOuterProduct_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-pure-euclideanouterproduct_self_sub
Downstream declaration: Matrix.euclideanOuterProduct_self_sub
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-pure-rectangulartracenorm_pure_density_sub_le
Downstream declaration: Matrix.rectangularTraceNorm_pure_density_sub_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-pure-rectangulartracenorm_pure_density_sub_le_two
Downstream declaration: Matrix.rectangularTraceNorm_pure_density_sub_le_two
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-pure-rectangulartracenorm_partialtraceright_pure_density_sub_le
Downstream declaration: Matrix.rectangularTraceNorm_partialTraceRight_pure_density_sub_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-pure-rectangulartracenorm_partialtraceright_pure_density_sub_le_two
Downstream declaration: Matrix.rectangularTraceNorm_partialTraceRight_pure_density_sub_le_two
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The rectangular outer product `|u⟩⟨v|` of Euclidean vectors. It retains
their actual norms, including zero vectors and empty ambient spaces. -/
def euclideanOuterProduct (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
    Matrix m n ℂ := vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp v))

omit [DecidableEq n] in
/-- The Hilbert--Schmidt trace pairing of an outer product is the corresponding
vector inner product. -/
theorem trace_euclideanOuterProduct_conjTranspose_mul
    (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) (U : Matrix m n ℂ) :
    ((euclideanOuterProduct u v)ᴴ * U).trace =
      ⟪u, (EuclideanSpace.equiv m ℂ).symm (U *ᵥ WithLp.ofLp v)⟫_ℂ := by
  change ((euclideanOuterProduct u v)ᴴ * U).trace =
    ⟪u, WithLp.toLp 2 (U *ᵥ WithLp.ofLp v)⟫_ℂ
  simp only [euclideanOuterProduct, trace, diag, mul_apply, conjTranspose_apply,
    vecMulVec_apply, Pi.star_apply, star_mul, star_star,
    EuclideanSpace.inner_eq_star_dotProduct, mulVec, dotProduct,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- Dimension-independent rank-one nuclear bound for independent ket and bra
spaces. Source: the pure-density estimate preceding
`eq:compression-effect-circuit-error`. -/
theorem rectangularTraceNorm_euclideanOuterProduct_le
    (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
    rectangularTraceNorm (euclideanOuterProduct u v) ≤ ‖u‖ * ‖v‖ := by
  apply rectangularTraceNorm_le_of_forall_contraction
  intro U hU
  rw [trace_euclideanOuterProduct_conjTranspose_mul]
  have hv := U.l2_opNorm_mulVec v
  have huv : ‖(EuclideanSpace.equiv m ℂ).symm (U *ᵥ WithLp.ofLp v)‖ ≤ ‖v‖ := by
    exact hv.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hU (norm_nonneg v))
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left huv (norm_nonneg u))

omit [Fintype n] [DecidableEq n] in
/-- Split a pure-density difference without normalizing either vector.
Source: Theorem 5.2, `04-compression.tex:218–222`. -/
theorem euclideanOuterProduct_self_sub
    (v w : EuclideanSpace ℂ n) :
    euclideanOuterProduct v v - euclideanOuterProduct w w =
      euclideanOuterProduct (v - w) v + euclideanOuterProduct w (v - w) := by
  ext i j
  simp only [euclideanOuterProduct, sub_apply, add_apply, vecMulVec_apply,
    WithLp.ofLp_sub, Pi.sub_apply, Pi.star_apply, star_sub]
  ring

/-- Absolute trace-norm error between arbitrary, possibly subnormalized pure
densities. No lower bound on either vector norm is required. Source:
Theorem 5.2, `04-compression.tex:218–222`. -/
theorem rectangularTraceNorm_pure_density_sub_le
    (v w : EuclideanSpace ℂ n) :
    rectangularTraceNorm (euclideanOuterProduct v v - euclideanOuterProduct w w) ≤
      (‖v‖ + ‖w‖) * ‖v - w‖ := by
  rw [euclideanOuterProduct_self_sub]
  exact (rectangularTraceNorm_add_le _ _).trans
    ((add_le_add (rectangularTraceNorm_euclideanOuterProduct_le (v - w) v)
      (rectangularTraceNorm_euclideanOuterProduct_le w (v - w))).trans_eq (by ring))

/-- Two vectors of norm at most one have absolute density error at most twice
their vector error. Source: Theorem 5.2,
`eq:compression-effect-circuit-error`. -/
theorem rectangularTraceNorm_pure_density_sub_le_two
    (v w : EuclideanSpace ℂ n) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    rectangularTraceNorm (euclideanOuterProduct v v - euclideanOuterProduct w w) ≤
      2 * ‖v - w‖ := by
  exact (rectangularTraceNorm_pure_density_sub_le v w).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg (v - w)))

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]

/-- Discarding any finite register preserves the absolute pure-density error
estimate, without a factor depending on its dimension. Source: Theorem 5.2,
`04-compression.tex:223–227`. -/
theorem rectangularTraceNorm_partialTraceRight_pure_density_sub_le
    (v w : EuclideanSpace ℂ (a × b)) :
    rectangularTraceNorm
      (partialTraceRight (euclideanOuterProduct v v) -
        partialTraceRight (euclideanOuterProduct w w)) ≤ (‖v‖ + ‖w‖) * ‖v - w‖ := by
  classical
  change rectangularTraceNorm
    (partialTraceRightLM (euclideanOuterProduct v v) -
      partialTraceRightLM (euclideanOuterProduct w w)) ≤ _
  rw [← map_sub partialTraceRightLM]
  exact (rectangularTraceNorm_partialTraceRight_le _).trans
    (rectangularTraceNorm_pure_density_sub_le v w)

/-- The physical density error after discarding an owned register is at most
twice the vector error for subnormalized vectors. Source: Theorem 5.2,
`eq:compression-effect-circuit-error`. -/
theorem rectangularTraceNorm_partialTraceRight_pure_density_sub_le_two
    (v w : EuclideanSpace ℂ (a × b)) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    rectangularTraceNorm
      (partialTraceRight (euclideanOuterProduct v v) -
        partialTraceRight (euclideanOuterProduct w w)) ≤ 2 * ‖v - w‖ := by
  exact (rectangularTraceNorm_partialTraceRight_pure_density_sub_le v w).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg (v - w)))

end Matrix
