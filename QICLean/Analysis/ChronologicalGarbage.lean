/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionChain
import QICLean.Analysis.SubnormalizedPureStateError
import QICLean.Analysis.MatrixFramePerturbation

/-!
# Chronological accumulation of idle garbage registers

At each stage a supplied finite register is appended beside the working
memory. All earlier appended registers are kept literally idle. The ideal
chain, which appends supplied pure vectors, has an exact prefix factorization
and gives the original density after discarding the accumulated registers.
The coefficient lift also accepts arbitrary replacement maps whose new
register may become correlated with the memory.

Per-gate inventory spaces, vectors and replacements are caller data. This
module does not construct effect replacements, assign registers to parties,
or identify arbitrary entangled discarded registers with fresh pure ones.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
Theorem 5.2, source-only reduction, `04-compression.tex:199–229`, immutable
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are original proofs; no OpenAI Lean code is copied or adapted.
-/

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace Kronecker

noncomputable section

namespace Matrix

universe u v

/-- The previously appended inventory, in chronological order. The empty
inventory is a one-dimensional scalar register. -/
/-
Provenance-ID: p09-qic-garbage-garbageinventory
Downstream declaration: Matrix.garbageInventory
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
@[reducible] def garbageInventory (B : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | t + 1 => garbageInventory B t × B t

/-
Provenance-ID: p09-qic-garbage-garbageinventoryfintype
Downstream declaration: Matrix.garbageInventoryFintype
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
@[reducible] instance garbageInventoryFintype (B : ℕ → Type u) [∀ t, Fintype (B t)] (t : ℕ) :
    Fintype (garbageInventory B t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ t ih =>
    letI := ih
    exact inferInstanceAs (Fintype (garbageInventory B t × B t))

/-
Provenance-ID: p09-qic-garbage-garbageinventorydecidableeq
Downstream declaration: Matrix.garbageInventoryDecidableEq
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
@[reducible] instance garbageInventoryDecidableEq (B : ℕ → Type u)
    [∀ t, DecidableEq (B t)] (t : ℕ) :
    DecidableEq (garbageInventory B t) := by
  induction t with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ t ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (garbageInventory B t × B t))

variable {m n b c : Type*}

/-- Coordinate tensor product of two arbitrary finite Euclidean vectors. -/
/-
Provenance-ID: p09-qic-garbage-euclideantensorvector
Downstream declaration: Matrix.euclideanTensorVector
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
def euclideanTensorVector (v : EuclideanSpace ℂ m) (w : EuclideanSpace ℂ n) :
    EuclideanSpace ℂ (m × n) := WithLp.toLp 2 (fun p ↦ v p.1 * w p.2)

@[simp]
/-
Provenance-ID: p09-qic-garbage-euclideantensorvector_apply
Downstream declaration: Matrix.euclideanTensorVector_apply
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem euclideanTensorVector_apply (v : EuclideanSpace ℂ m)
    (w : EuclideanSpace ℂ n) (i : m) (j : n) :
    euclideanTensorVector v w (i, j) = v i * w j := rfl

/-- Tensor products multiply actual vector norms, with no nonzero assumption. -/
/-
Provenance-ID: p09-qic-garbage-norm_euclideantensorvector
Downstream declaration: Matrix.norm_euclideanTensorVector
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem norm_euclideanTensorVector [Fintype m] [Fintype n] (v : EuclideanSpace ℂ m)
    (w : EuclideanSpace ℂ n) : ‖euclideanTensorVector v w‖ = ‖v‖ * ‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simp only [EuclideanSpace.norm_sq_eq, euclideanTensorVector,
    Fintype.sum_prod_type, norm_mul, mul_pow]
  rw [Finset.sum_mul_sum]

/-- Outer products retain the literal tensor-factor placement. -/
/-
Provenance-ID: p09-qic-garbage-euclideanouterproduct_tensorvector
Downstream declaration: Matrix.euclideanOuterProduct_tensorVector
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem euclideanOuterProduct_tensorVector (v : EuclideanSpace ℂ m)
    (w : EuclideanSpace ℂ n) :
    euclideanOuterProduct (euclideanTensorVector v w) (euclideanTensorVector v w) =
      euclideanOuterProduct v v ⊗ₖ euclideanOuterProduct w w := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [euclideanOuterProduct, vecMulVec_apply, Pi.star_apply,
    euclideanTensorVector_apply, kroneckerMap_apply, star_mul]
  ring

/-- The trace of the actual pure density is the squared Euclidean norm. -/
/-
Provenance-ID: p09-qic-garbage-trace_euclideanouterproduct_self
Downstream declaration: Matrix.trace_euclideanOuterProduct_self
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem trace_euclideanOuterProduct_self [Fintype n] (w : EuclideanSpace ℂ n) :
    (euclideanOuterProduct w w).trace = (‖w‖ : ℂ) ^ 2 := by
  calc
    _ = ⟪w, w⟫_ℂ := by
      simp only [euclideanOuterProduct, trace, diag, vecMulVec_apply, Pi.star_apply,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    _ = _ := inner_self_eq_norm_sq_to_K w

/-- Discarding a fresh normalized pure register preserves the exact density,
also for zero or subnormalized working vectors. -/
/-
Provenance-ID: p09-qic-garbage-partialtraceright_tensorvector
Downstream declaration: Matrix.partialTraceRight_tensorVector
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem partialTraceRight_tensorVector [Fintype n] (v : EuclideanSpace ℂ m)
    (w : EuclideanSpace ℂ n) (hw : ‖w‖ = 1) :
    partialTraceRight (euclideanOuterProduct
      (euclideanTensorVector v w) (euclideanTensorVector v w)) =
        euclideanOuterProduct v v := by
  rw [euclideanOuterProduct_tensorVector, partialTraceRight_kronecker,
    trace_euclideanOuterProduct_self, hw]
  simp

variable [Fintype n] [Fintype c] [DecidableEq c]

/-- Lift a map that creates a new register, leaving every earlier register
idle. The output order is memory, earlier inventory, fresh register. -/
/-
Provenance-ID: p09-qic-garbage-idlegarbagelift
Downstream declaration: Matrix.idleGarbageLift
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
def idleGarbageLift (A : Matrix (m × b) n ℂ) :
    Matrix (m × (c × b)) (n × c) ℂ :=
  fun y x ↦ A (y.1, y.2.2) x.1 * if y.2.1 = x.2 then 1 else 0

/-- Append the specified pure vector after an actual working-memory gate. -/
/-
Provenance-ID: p09-qic-garbage-appendgarbagegate
Downstream declaration: Matrix.appendGarbageGate
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
def appendGarbageGate (G : Matrix m n ℂ) (γ : EuclideanSpace ℂ b) :
    Matrix (m × b) n ℂ := fun y x ↦ G y.1 x * γ y.2

/-- The idle coefficient lift acts only on the working memory and fresh
register, without altering any earlier inventory coordinate. -/
/-
Provenance-ID: p09-qic-garbage-idlegarbagelift_mulvec
Downstream declaration: Matrix.idleGarbageLift_mulVec
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem idleGarbageLift_mulVec (A : Matrix (m × b) n ℂ)
    (ξ : EuclideanSpace ℂ (n × c)) (y : m) (k : c) (e : b) :
    (idleGarbageLift A *ᵥ WithLp.ofLp ξ) (y, (k, e)) =
      (A *ᵥ fun x ↦ ξ (x, k)) (y, e) := by
  classical
  simp [idleGarbageLift, mulVec, dotProduct, Fintype.sum_prod_type,
    mul_ite, ite_mul]

/-- One chronological ideal stage preserves the tensor factorization. -/
/-
Provenance-ID: p09-qic-garbage-idlegarbagelift_append_mulvec
Downstream declaration: Matrix.idleGarbageLift_append_mulVec
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem idleGarbageLift_append_mulVec [DecidableEq n] (G : Matrix m n ℂ)
    (γ : EuclideanSpace ℂ b) (v : EuclideanSpace ℂ n) (w : EuclideanSpace ℂ c) :
    toEuclideanLin (idleGarbageLift (appendGarbageGate G γ))
      (euclideanTensorVector v w) =
        euclideanTensorVector (toEuclideanLin G v) (euclideanTensorVector w γ) := by
  ext ⟨y, k, e⟩
  change (idleGarbageLift (appendGarbageGate G γ) *ᵥ
    WithLp.ofLp (euclideanTensorVector v w)) (y, (k, e)) = _
  rw [idleGarbageLift_mulVec]
  change (∑ i, (G y i * γ e) * (v i * w k)) = (∑ i, G y i * v i) * (w k * γ e)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

omit [Fintype n] [Fintype c] in
/-- The idle lift is exactly a rectangular identity amplification followed
by the stated output-register permutation. -/
/-
Provenance-ID: p09-qic-garbage-idlegarbagelift_eq_kronecker_submatrix
Downstream declaration: Matrix.idleGarbageLift_eq_kronecker_submatrix
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem idleGarbageLift_eq_kronecker_submatrix (A : Matrix (m × b) n ℂ) :
    idleGarbageLift (c := c) A =
      (A ⊗ₖ (1 : Matrix c c ℂ)).submatrix
        (fun y ↦ ((y.1, y.2.2), y.2.1)) id := by
  ext y x
  simp [idleGarbageLift, kroneckerMap_apply, one_apply]

/-- Keeping earlier inventories idle introduces no dimension factor into
the operator norm, even for empty memory or inventory spaces. -/
/-
Provenance-ID: p09-qic-garbage-norm_idlegarbagelift_le
Downstream declaration: Matrix.norm_idleGarbageLift_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem norm_idleGarbageLift_le [Fintype m] [Fintype b] [DecidableEq n]
    (A : Matrix (m × b) n ℂ) : ‖idleGarbageLift (c := c) A‖ ≤ ‖A‖ := by
  rw [l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro ξ
  change ‖toEuclideanLin (idleGarbageLift A) ξ‖ ≤ ‖A‖ * ‖ξ‖
  have hnorm : ‖toEuclideanLin (idleGarbageLift A) ξ‖ =
      ‖WithLp.toLp 2 ((A ⊗ₖ (1 : Matrix c c ℂ)) *ᵥ WithLp.ofLp ξ)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.norm_sq_eq, toLpLin_apply,
      Fintype.sum_prod_type]
    simp_rw [idleGarbageLift_mulVec]
    have hcoord (y : m) (e : b) (k : c) :
        ((A ⊗ₖ (1 : Matrix c c ℂ)) *ᵥ WithLp.ofLp ξ) ((y, e), k) =
          (A *ᵥ fun x ↦ ξ (x, k)) (y, e) := by
      simp [mulVec, dotProduct, Fintype.sum_prod_type,
        kroneckerMap_apply, one_apply, mul_ite, ite_mul]
    simp_rw [hcoord]
    exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_comm
  rw [hnorm]
  exact l2_opNorm_kronecker_one_mulVec_le A ξ

omit [Fintype n] [Fintype c] in
/-- The idle lift respects actual differences of replacement coefficients. -/
/-
Provenance-ID: p09-qic-garbage-idlegarbagelift_sub
Downstream declaration: Matrix.idleGarbageLift_sub
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem idleGarbageLift_sub (A A' : Matrix (m × b) n ℂ) :
    idleGarbageLift (c := c) (A - A') = idleGarbageLift A - idleGarbageLift A' := by
  ext y x
  simp only [idleGarbageLift, sub_apply, sub_mul]

/-- A replacement's operator error is preserved when the earlier garbage
is kept idle; no restriction is imposed on its correlations. -/
/-
Provenance-ID: p09-qic-garbage-norm_idlegarbagelift_sub_le
Downstream declaration: Matrix.norm_idleGarbageLift_sub_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem norm_idleGarbageLift_sub_le [Fintype m] [Fintype b] [DecidableEq n]
    (A A' : Matrix (m × b) n ℂ) :
    ‖idleGarbageLift (c := c) A - idleGarbageLift A'‖ ≤ ‖A - A'‖ := by
  rw [← idleGarbageLift_sub]
  exact norm_idleGarbageLift_le _

omit [Fintype c] [DecidableEq c] in
/-- Appending a pure register acts on every actual input by a coordinate
tensor product, without requiring unit norm. -/
/-
Provenance-ID: p09-qic-garbage-appendgarbagegate_mulvec
Downstream declaration: Matrix.appendGarbageGate_mulVec
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem appendGarbageGate_mulVec [DecidableEq n] (G : Matrix m n ℂ)
    (γ : EuclideanSpace ℂ b) (v : EuclideanSpace ℂ n) :
    toEuclideanLin (appendGarbageGate G γ) v =
      euclideanTensorVector (toEuclideanLin G v) γ := by
  ext ⟨y, e⟩
  change (∑ i, (G y i * γ e) * v i) = (∑ i, G y i * v i) * γ e
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

omit [Fintype c] [DecidableEq c] in
/-- The norm cost of appending an arbitrary pure register is its vector
norm, rather than its dimension. -/
/-
Provenance-ID: p09-qic-garbage-norm_appendgarbagegate_le
Downstream declaration: Matrix.norm_appendGarbageGate_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem norm_appendGarbageGate_le [Fintype m] [Fintype b] [DecidableEq n]
    (G : Matrix m n ℂ) (γ : EuclideanSpace ℂ b) :
    ‖appendGarbageGate G γ‖ ≤ ‖G‖ * ‖γ‖ := by
  rw [l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg G) (norm_nonneg γ))
  intro ξ
  change ‖toEuclideanLin (appendGarbageGate G γ) ξ‖ ≤ (‖G‖ * ‖γ‖) * ‖ξ‖
  rw [appendGarbageGate_mulVec, norm_euclideanTensorVector]
  exact (mul_le_mul_of_nonneg_right (G.l2_opNorm_mulVec ξ) (norm_nonneg γ)).trans_eq
    (by ring)

/-- The final identity amplification leaves the entire inventory unchanged. -/
/-
Provenance-ID: p09-qic-garbage-kronecker_one_tensorvector
Downstream declaration: Matrix.kronecker_one_tensorVector
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem kronecker_one_tensorVector [DecidableEq n] (K : Matrix m n ℂ)
    (v : EuclideanSpace ℂ n) (w : EuclideanSpace ℂ c) :
    toEuclideanLin (K ⊗ₖ (1 : Matrix c c ℂ)) (euclideanTensorVector v w) =
      euclideanTensorVector (toEuclideanLin K v) w := by
  ext ⟨y, k⟩
  change ((K ⊗ₖ (1 : Matrix c c ℂ)) *ᵥ
    WithLp.ofLp (euclideanTensorVector v w)) (y, k) =
      (K *ᵥ WithLp.ofLp v) y * w k
  simp only [mulVec, dotProduct, kroneckerMap_apply, one_apply, mul_ite, mul_one,
    mul_zero, euclideanTensorVector, ite_mul, zero_mul, Fintype.sum_prod_type,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- An arbitrary rectangular readout amplified by the garbage identity has
the same operator bound, including empty spaces. -/
/-
Provenance-ID: p09-qic-garbage-norm_kronecker_one_rectangular_le
Downstream declaration: Matrix.norm_kronecker_one_rectangular_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem norm_kronecker_one_rectangular_le [Fintype m] [DecidableEq n]
    (K : Matrix m n ℂ) : ‖K ⊗ₖ (1 : Matrix c c ℂ)‖ ≤ ‖K‖ := by
  rw [l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K)
  intro ξ
  exact l2_opNorm_kronecker_one_mulVec_le K ξ

variable {D : ℕ → Type v} {B : ℕ → Type u}
  [∀ t, Fintype (D t)] [∀ t, DecidableEq (D t)]
  [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

/-- Product of the supplied fresh inventory vectors through the first `t`
stages; the initial scalar factor has coefficient one. -/
/-
Provenance-ID: p09-qic-garbage-cumulativegarbagevector
Downstream declaration: Matrix.cumulativeGarbageVector
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
def cumulativeGarbageVector (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) :
    (t : ℕ) → EuclideanSpace ℂ (garbageInventory B t)
  | 0 => WithLp.toLp 2 (fun _ ↦ 1)
  | t + 1 => euclideanTensorVector (cumulativeGarbageVector γ t) (γ t)

/-- The concrete chain of ideal gates with all accumulated inventories idle. -/
/-
Provenance-ID: p09-qic-garbage-chronologicalgarbagechain
Downstream declaration: Matrix.chronologicalGarbageChain
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
def chronologicalGarbageChain
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (t : ℕ) :
    Matrix (D (t + 1) × garbageInventory B (t + 1))
      (D t × garbageInventory B t) ℂ :=
  idleGarbageLift (appendGarbageGate (G t) (γ t))

/-- Actual replacement stages lifted into the same chronological inventory.
The supplied maps may create correlations with their fresh output registers. -/
/-
Provenance-ID: p09-qic-garbage-chronologicalreplacementchain
Downstream declaration: Matrix.chronologicalReplacementChain
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
def chronologicalReplacementChain
    (A : (t : ℕ) → Matrix (D (t + 1) × B t) (D t) ℂ) (t : ℕ) :
    Matrix (D (t + 1) × garbageInventory B (t + 1))
      (D t × garbageInventory B t) ℂ := idleGarbageLift (A t)

/-- The lifted replacement's actual error against the ideal fresh-inventory
gate is bounded by its original per-gate error, independent of old garbage. -/
/-
Provenance-ID: p09-qic-garbage-chronologicalreplacementchain_sub_norm_le
Downstream declaration: Matrix.chronologicalReplacementChain_sub_norm_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem chronologicalReplacementChain_sub_norm_le
    (A : (t : ℕ) → Matrix (D (t + 1) × B t) (D t) ℂ)
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (t : ℕ) :
    ‖chronologicalReplacementChain A t - chronologicalGarbageChain G γ t‖ ≤
      ‖A t - appendGarbageGate (G t) (γ t)‖ := norm_idleGarbageLift_sub_le _ _

/-- Contractive replacement gates remain contractive after all earlier
inventories are kept idle. -/
/-
Provenance-ID: p09-qic-garbage-chronologicalreplacementchain_norm_le_one
Downstream declaration: Matrix.chronologicalReplacementChain_norm_le_one
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem chronologicalReplacementChain_norm_le_one
    (A : (t : ℕ) → Matrix (D (t + 1) × B t) (D t) ℂ)
    (hA : ∀ t, ‖A t‖ ≤ 1) (t : ℕ) : ‖chronologicalReplacementChain A t‖ ≤ 1 :=
  (norm_idleGarbageLift_le _).trans (hA t)

omit [∀ t, DecidableEq (B t)] in
/-- Every accumulated ideal inventory is normalized when its supplied
stage vectors are normalized. No dimension lower bounds are imposed. -/
/-
Provenance-ID: p09-qic-garbage-norm_cumulativegarbagevector
Downstream declaration: Matrix.norm_cumulativeGarbageVector
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem norm_cumulativeGarbageVector
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (hγ : ∀ t, ‖γ t‖ = 1) (t : ℕ) :
    ‖cumulativeGarbageVector γ t‖ = 1 := by
  induction t with
  | zero =>
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simp [cumulativeGarbageVector, EuclideanSpace.norm_sq_eq, garbageInventory]
  | succ t ih =>
    rw [cumulativeGarbageVector, norm_euclideanTensorVector, ih, hγ, mul_one]

/-- Exact evaluation of the augmented chronological prefix, without any
normalization or contraction assumptions on the gates or vectors. -/
/-
Provenance-ID: p09-qic-garbage-chronologicalgarbagechain_prefix_vector
Downstream declaration: Matrix.chronologicalGarbageChain_prefix_vector
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem chronologicalGarbageChain_prefix_vector
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (ψ : EuclideanSpace ℂ (D 0)) (t : ℕ) :
    toEuclideanLin (contractionPrefix (D := fun t ↦ D t × garbageInventory B t)
      (chronologicalGarbageChain G γ) t)
      (euclideanTensorVector ψ (cumulativeGarbageVector γ 0)) =
        euclideanTensorVector (toEuclideanLin (contractionPrefix G t) ψ)
          (cumulativeGarbageVector γ t) := by
  induction t with
  | zero => simp [contractionPrefix]
  | succ t ih =>
    simp only [contractionPrefix, toLpLin_mul_same, LinearMap.comp_apply]
    rw [ih]
    exact idleGarbageLift_append_mulVec (G t) (γ t) _ _

/-- Literal discarded density of the augmented ideal circuit equals the
original circuit density. The working input need not be normalized. -/
/-
Provenance-ID: p09-qic-garbage-chronologicalgarbagechain_discard_density
Downstream declaration: Matrix.chronologicalGarbageChain_discard_density
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem chronologicalGarbageChain_discard_density
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (hγ : ∀ t, ‖γ t‖ = 1)
    (ψ : EuclideanSpace ℂ (D 0)) (t : ℕ) :
    let v := toEuclideanLin (contractionPrefix (D := fun t ↦ D t × garbageInventory B t)
      (chronologicalGarbageChain G γ) t)
      (euclideanTensorVector ψ (cumulativeGarbageVector γ 0))
    partialTraceRight (euclideanOuterProduct v v) =
      euclideanOuterProduct (toEuclideanLin (contractionPrefix G t) ψ)
        (toEuclideanLin (contractionPrefix G t) ψ) := by
  dsimp only
  rw [chronologicalGarbageChain_prefix_vector]
  exact partialTraceRight_tensorVector _ _ (norm_cumulativeGarbageVector γ hγ t)

/-- The actual ideal augmented stages are contractions whenever the
working gates contract and the supplied fresh vectors are normalized. -/
/-
Provenance-ID: p09-qic-garbage-chronologicalgarbagechain_norm_le_one
Downstream declaration: Matrix.chronologicalGarbageChain_norm_le_one
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem chronologicalGarbageChain_norm_le_one
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t))
    (hG : ∀ t, ‖G t‖ ≤ 1) (hγ : ∀ t, ‖γ t‖ = 1) (t : ℕ) :
    ‖chronologicalGarbageChain G γ t‖ ≤ 1 := by
  exact (norm_idleGarbageLift_le _).trans
    ((norm_appendGarbageGate_le (G t) (γ t)).trans (by simpa [hγ t] using hG t))

variable {P E : Type*} [Fintype E]

/-- Actual readout of the augmented prefix, acting identically on the
accumulated inventory. Its output order is `(physical, owned)`, then inventory. -/
/-
Provenance-ID: p09-qic-garbage-chronologicalgarbagereadout
Downstream declaration: Matrix.chronologicalGarbageReadout
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
def chronologicalGarbageReadout
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (ψ : EuclideanSpace ℂ (D 0)) (t : ℕ)
    (K : Matrix (P × E) (D t) ℂ) :
    EuclideanSpace ℂ ((P × E) × garbageInventory B t) :=
  toEuclideanLin (K ⊗ₖ (1 : Matrix (garbageInventory B t) (garbageInventory B t) ℂ))
    (toEuclideanLin (contractionPrefix (D := fun s ↦ D s × garbageInventory B s)
      (chronologicalGarbageChain G γ) t)
      (euclideanTensorVector ψ (cumulativeGarbageVector γ 0)))

omit [Fintype E] in
/-- Exact final vector factorization for the common physical readout. -/
/-
Provenance-ID: p09-qic-garbage-chronologicalgarbagereadout_eq
Downstream declaration: Matrix.chronologicalGarbageReadout_eq
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem chronologicalGarbageReadout_eq
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (ψ : EuclideanSpace ℂ (D 0)) (t : ℕ)
    (K : Matrix (P × E) (D t) ℂ) :
    chronologicalGarbageReadout G γ ψ t K =
      euclideanTensorVector (toEuclideanLin (K * contractionPrefix G t) ψ)
        (cumulativeGarbageVector γ t) := by
  unfold chronologicalGarbageReadout
  rw [chronologicalGarbageChain_prefix_vector, kronecker_one_tensorVector]
  simp only [toLpLin_mul_same, LinearMap.comp_apply]

/-- Discard the actual accumulated inventories and the originally owned
readout register: the resulting physical density equals the original circuit's
readout density. No gate, readout or input normalization is needed. -/
/-
Provenance-ID: p09-qic-garbage-chronologicalgarbagereadout_discard_density
Downstream declaration: Matrix.chronologicalGarbageReadout_discard_density
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/
theorem chronologicalGarbageReadout_discard_density
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (hγ : ∀ t, ‖γ t‖ = 1)
    (ψ : EuclideanSpace ℂ (D 0)) (t : ℕ) (K : Matrix (P × E) (D t) ℂ) :
    partialTraceRight (partialTraceRight (euclideanOuterProduct
      (chronologicalGarbageReadout G γ ψ t K)
      (chronologicalGarbageReadout G γ ψ t K))) =
        partialTraceRight (euclideanOuterProduct
          (toEuclideanLin (K * contractionPrefix G t) ψ)
          (toEuclideanLin (K * contractionPrefix G t) ψ)) := by
  rw [chronologicalGarbageReadout_eq,
    partialTraceRight_tensorVector _ _ (norm_cumulativeGarbageVector γ hγ t)]

end Matrix
