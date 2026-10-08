/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionChain
import QICLean.Analysis.SubnormalizedPureStateError

/-!
# Source-only density error from an approximate contraction chain

Rescale each approximate gate, apply the actual chronological prefixes to an
input vector of norm at most one, and use the same contractive final readout
into physical and discarded registers. The resulting physical density error
is at most `4 n δ`. Choosing `δ = ε / (8 n)` gives an error at most `ε / 2`.
For a zero-length chain the densities coincide exactly.

The uniform budget counts every approximated stage. The marked-stage budget
instead counts only the selected occurrences and leaves the other gates
exact, as needed when the paper counts nonprivate gates. A caller identifies
the changing-memory chain and common readout. This module does not construct
that circuit identification or effect elimination.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
Theorem 5.2, source-only reduction and `eq:compression-effect-circuit-error`,
`04-compression.tex:199–229`, immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are original proofs; no OpenAI Lean code is copied or adapted.
-/

/-
Provenance-ID: p09-qic-density-rescaledgatechain
Downstream declaration: Matrix.rescaledGateChain
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-markedrescaledgatechain
Downstream declaration: Matrix.markedRescaledGateChain
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-sourceonlyreadoutvector
Downstream declaration: Matrix.sourceOnlyReadoutVector
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-sourceonlyreadoutdensity
Downstream declaration: Matrix.sourceOnlyReadoutDensity
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-sourceonlyreadoutvector_norm_le_one
Downstream declaration: Matrix.sourceOnlyReadoutVector_norm_le_one
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-sourceonlyreadoutvector_sub_norm_le
Downstream declaration: Matrix.sourceOnlyReadoutVector_sub_norm_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-rectangulartracenorm_sourceonlyreadoutdensity_sub_le_prefix
Downstream declaration: Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le_prefix
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-rectangulartracenorm_sourceonlyreadoutdensity_sub_le_sum
Downstream declaration: Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le_sum
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-rectangulartracenorm_sourceonlyreadoutdensity_sub_le
Downstream declaration: Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-rectangulartracenorm_sourceonlyreadoutdensity_sub_le_half
Downstream declaration: Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le_half
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-rectangulartracenorm_sourceonlyreadoutdensity_marked_sub_le
Downstream declaration: Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_marked_sub_le
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-rectangulartracenorm_sourceonlyreadoutdensity_marked_sub_le_half
Downstream declaration: Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_marked_sub_le_half
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-rectangulartracenorm_sourceonlyreadoutdensity_marked_empty
Downstream declaration: Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_marked_empty
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-sourceonlyreadoutdensity_zero
Downstream declaration: Matrix.sourceOnlyReadoutDensity_zero
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

/-
Provenance-ID: p09-qic-density-rectangulartracenorm_sourceonlyreadoutdensity_sub_zero
Downstream declaration: Matrix.rectangularTraceNorm_sourceOnlyReadoutDensity_sub_zero
Source: September 24, 2026.
Label: eq:compression-effect-circuit-error.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L199-L229
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {D : ℕ → Type*} [∀ t, Fintype (D t)] [∀ t, DecidableEq (D t)]
variable {P E : Type*} [Fintype P] [Fintype E]

/-- Rescale the actual approximate gates by the common approximation budget.
Source: Theorem 5.2, `04-compression.tex:210–212`. -/
def rescaledGateChain (A : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ) (δ : ℝ) :
    (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ :=
  fun t ↦ ((1 + δ)⁻¹ : ℝ) • A t

/-- Rescale only the selected approximate gates and retain the actual original
gate at every other occurrence. Source: Theorem 5.2,
`04-compression.tex:199–217`. -/
def markedRescaledGateChain (G A : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (S : Finset ℕ) (δ : ℝ) : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ :=
  fun t ↦ if t ∈ S then rescaledGateChain A δ t else G t

/-- Apply the chronological prefix and the common readout to the actual input
vector. The readout may include a fixed layout projection or reindexing. -/
def sourceOnlyReadoutVector
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ) :
    EuclideanSpace ℂ (P × E) :=
  toEuclideanLin (K * contractionPrefix G n) ψ

/-- The physical density obtained from the actual final readout vector by
discarding the owned register. It retains its subnormalization. -/
def sourceOnlyReadoutDensity
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ) :
    Matrix P P ℂ :=
  partialTraceRight (euclideanOuterProduct (sourceOnlyReadoutVector G ψ n K)
    (sourceOnlyReadoutVector G ψ n K))

/-- Contractive gates and a contractive common readout preserve the input's
upper norm bound. No normalization lower bound is imposed. -/
theorem sourceOnlyReadoutVector_norm_le_one
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ)
    (hG : ∀ t, ‖G t‖ ≤ 1) (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    ‖sourceOnlyReadoutVector G ψ n K‖ ≤ 1 := by
  have hprefix := l2_opNorm_mul_le_one K (contractionPrefix G n) hK
    (contractionPrefix_norm_le_one G hG n)
  have h := (K * contractionPrefix G n).l2_opNorm_mulVec ψ
  exact h.trans ((mul_le_mul hprefix hψ (norm_nonneg ψ) zero_le_one).trans_eq (mul_one 1))

/-- A common contraction readout cannot amplify the actual prefix vector
error. This result assumes no contraction bound on either prefix. -/
theorem sourceOnlyReadoutVector_sub_norm_le
    (G H : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ)
    (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    ‖sourceOnlyReadoutVector G ψ n K - sourceOnlyReadoutVector H ψ n K‖ ≤
      ‖contractionPrefix G n - contractionPrefix H n‖ := by
  have heq : sourceOnlyReadoutVector G ψ n K - sourceOnlyReadoutVector H ψ n K =
      toEuclideanLin (K * (contractionPrefix G n - contractionPrefix H n)) ψ := by
    simp only [sourceOnlyReadoutVector, Matrix.mul_sub, map_sub, LinearMap.sub_apply]
  rw [heq]
  have h := (K * (contractionPrefix G n - contractionPrefix H n)).l2_opNorm_mulVec ψ
  calc
    _ ≤ ‖K * (contractionPrefix G n - contractionPrefix H n)‖ * ‖ψ‖ := h
    _ ≤ (‖K‖ * ‖contractionPrefix G n - contractionPrefix H n‖) * ‖ψ‖ :=
      mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg ψ)
    _ ≤ (1 * ‖contractionPrefix G n - contractionPrefix H n‖) * 1 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) hψ
        (norm_nonneg ψ) (by positivity)
    _ = _ := by ring

variable [DecidableEq P]

/-- For two actual contraction chains, the common physical readout has
density error bounded by twice the operator error of their prefixes. -/
theorem rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le_prefix
    (G H : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ)
    (hG : ∀ t, ‖G t‖ ≤ 1) (hH : ∀ t, ‖H t‖ ≤ 1)
    (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    rectangularTraceNorm (sourceOnlyReadoutDensity H ψ n K -
      sourceOnlyReadoutDensity G ψ n K) ≤
      2 * ‖contractionPrefix H n - contractionPrefix G n‖ := by
  have hdensity := rectangularTraceNorm_partialTraceRight_pure_density_sub_le_two
    (sourceOnlyReadoutVector H ψ n K) (sourceOnlyReadoutVector G ψ n K)
    (sourceOnlyReadoutVector_norm_le_one H ψ n K hH hψ hK)
    (sourceOnlyReadoutVector_norm_le_one G ψ n K hG hψ hK)
  exact hdensity.trans (mul_le_mul_of_nonneg_left
    (sourceOnlyReadoutVector_sub_norm_le H G ψ n K hψ hK) (by norm_num))

/-- The actual physical density error is at most twice the sum of per-gate
operator errors. Exact private stages contribute zero. Source: Theorem 5.2,
`eq:compression-effect-circuit-error`. -/
theorem rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le_sum
    (G H : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ)
    (hG : ∀ t, ‖G t‖ ≤ 1) (hH : ∀ t, ‖H t‖ ≤ 1)
    (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    rectangularTraceNorm (sourceOnlyReadoutDensity H ψ n K -
      sourceOnlyReadoutDensity G ψ n K) ≤
      2 * ∑ t ∈ Finset.range n, ‖H t - G t‖ := by
  exact (rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le_prefix G H ψ n K
    hG hH hψ hK).trans (mul_le_mul_of_nonneg_left
      (contractionPrefix_sub_norm_le H G hH hG n) (by norm_num))

/-- The actual rescaled chain has physical density error at most `4 n δ`.
All gates share the prescribed changing memory types and the final readout is
common. Source: Theorem 5.2, `eq:compression-effect-circuit-error`. -/
theorem rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le
    (G A : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hG : ∀ t, ‖G t‖ ≤ 1)
    (herror : ∀ t, ‖A t - G t‖ ≤ δ) (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    rectangularTraceNorm
      (sourceOnlyReadoutDensity (rescaledGateChain A δ) ψ n K -
        sourceOnlyReadoutDensity G ψ n K) ≤ 4 * n * δ := by
  have hscale := fun t ↦ NormedSpace.rescale_approximation (G t) (A t) δ hδ
    (hG t) (herror t)
  have hH : ∀ t, ‖rescaledGateChain A δ t‖ ≤ 1 := fun t ↦ (hscale t).1
  have hchain : ‖contractionPrefix (rescaledGateChain A δ) n - contractionPrefix G n‖ ≤
      n * (2 * δ) :=
    contractionPrefix_sub_norm_le_uniform (rescaledGateChain A δ) G hH hG (2 * δ)
      (fun t ↦ (hscale t).2) n
  exact (rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le_prefix
    G (rescaledGateChain A δ) ψ n K hG hH hψ hK).trans
    ((mul_le_mul_of_nonneg_left hchain (by norm_num)).trans_eq (by ring))

/-- For a positive number of approximated stages, the noncircular choice
`δ = ε / (8 n)` gives physical density error at most `ε / 2`.
Source: Theorem 5.2, `eq:compression-effect-circuit-error`. -/
theorem rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le_half
    (G A : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hn : 0 < n) (hG : ∀ t, ‖G t‖ ≤ 1)
    (herror : ∀ t, ‖A t - G t‖ ≤ ε / (8 * n)) (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    rectangularTraceNorm
      (sourceOnlyReadoutDensity (rescaledGateChain A (ε / (8 * n))) ψ n K -
        sourceOnlyReadoutDensity G ψ n K) ≤ ε / 2 := by
  have hδ : 0 ≤ ε / (8 * n) := div_nonneg hε (by positivity)
  have h := rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le G A ψ n K
    (ε / (8 * n)) hδ hG herror hψ hK
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  convert h using 1
  field_simp
  ring

/-- Approximate and rescale only the marked gate occurrences. Exact private
stages contribute no error, so the density budget counts only `S.card`.
The set may include stages beyond the prefix; those stages have no effect.
Source: Theorem 5.2, `eq:compression-effect-circuit-error`. -/
theorem rectangularTraceNorm_sourceOnlyReadoutDensity_marked_sub_le
    (G A : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ)
    (S : Finset ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hG : ∀ t, ‖G t‖ ≤ 1)
    (herror : ∀ t ∈ S, ‖A t - G t‖ ≤ δ) (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    rectangularTraceNorm
      (sourceOnlyReadoutDensity (markedRescaledGateChain G A S δ) ψ n K -
        sourceOnlyReadoutDensity G ψ n K) ≤ 4 * S.card * δ := by
  have hscale := fun t ht ↦ NormedSpace.rescale_approximation (G t) (A t) δ hδ
    (hG t) (herror t ht)
  have hH : ∀ t, ‖markedRescaledGateChain G A S δ t‖ ≤ 1 := by
    intro t
    by_cases ht : t ∈ S
    · simpa only [markedRescaledGateChain, ht, ↓reduceIte, rescaledGateChain] using
        (hscale t ht).1
    · simpa only [markedRescaledGateChain, ht, ↓reduceIte] using hG t
  have herr : ∀ t ∈ S, ‖markedRescaledGateChain G A S δ t - G t‖ ≤ 2 * δ := by
    intro t ht
    simpa only [markedRescaledGateChain, ht, ↓reduceIte, rescaledGateChain] using
      (hscale t ht).2
  have hexact : ∀ t ∉ S, markedRescaledGateChain G A S δ t = G t := by
    intro t ht
    simp only [markedRescaledGateChain, ht, ↓reduceIte]
  have hchain := contractionPrefix_sub_norm_le_supported
    (markedRescaledGateChain G A S δ) G hH hG S (2 * δ) (by positivity) herr hexact n
  exact (rectangularTraceNorm_sourceOnlyReadoutDensity_sub_le_prefix
    G (markedRescaledGateChain G A S δ) ψ n K hG hH hψ hK).trans
    ((mul_le_mul_of_nonneg_left hchain (by norm_num)).trans_eq (by ring))

/-- Choosing the approximation scale using only the number of marked
nonprivate occurrences gives the paper's `ε / 2` density budget. Unmarked
private stages stay exact. Source: Theorem 5.2,
`eq:compression-effect-circuit-error`. -/
theorem rectangularTraceNorm_sourceOnlyReadoutDensity_marked_sub_le_half
    (G A : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ)
    (S : Finset ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hS : 0 < S.card) (hG : ∀ t, ‖G t‖ ≤ 1)
    (herror : ∀ t ∈ S, ‖A t - G t‖ ≤ ε / (8 * S.card))
    (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    rectangularTraceNorm
      (sourceOnlyReadoutDensity
        (markedRescaledGateChain G A S (ε / (8 * S.card))) ψ n K -
        sourceOnlyReadoutDensity G ψ n K) ≤ ε / 2 := by
  have hδ : 0 ≤ ε / (8 * S.card) := div_nonneg hε (by positivity)
  have h := rectangularTraceNorm_sourceOnlyReadoutDensity_marked_sub_le G A ψ n K S
    (ε / (8 * S.card)) hδ hG herror hψ hK
  have hS' : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  convert h using 1
  field_simp
  ring

/-- With no marked nonprivate gates, the actual density error is exactly
zero, regardless of the number of retained exact private stages. -/
@[simp]
theorem rectangularTraceNorm_sourceOnlyReadoutDensity_marked_empty
    (G A : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ) (δ : ℝ) :
    rectangularTraceNorm
      (sourceOnlyReadoutDensity (markedRescaledGateChain G A ∅ δ) ψ n K -
        sourceOnlyReadoutDensity G ψ n K) = 0 := by
  have heq : markedRescaledGateChain G A ∅ δ = G := by
    funext t
    simp only [markedRescaledGateChain, Finset.notMem_empty, ↓reduceIte]
  rw [heq, sub_self, rectangularTraceNorm_zero]

omit [Fintype P] [DecidableEq P] in
/-- A zero-stage chain has the same actual physical density for any two gate
families, independently of their norms. Source: Theorem 5.2, the `M = 0`
case of the source-only reduction. -/
@[simp]
theorem sourceOnlyReadoutDensity_zero
    (G H : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (K : Matrix (P × E) (D 0) ℂ) :
    sourceOnlyReadoutDensity G ψ 0 K = sourceOnlyReadoutDensity H ψ 0 K := by
  simp only [sourceOnlyReadoutDensity, sourceOnlyReadoutVector, contractionPrefix]

/-- The exact zero-stage density error has nuclear norm zero. -/
@[simp]
theorem rectangularTraceNorm_sourceOnlyReadoutDensity_sub_zero
    (G H : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (ψ : EuclideanSpace ℂ (D 0)) (K : Matrix (P × E) (D 0) ℂ) :
    rectangularTraceNorm
      (sourceOnlyReadoutDensity G ψ 0 K - sourceOnlyReadoutDensity H ψ 0 K) = 0 := by
  rw [sourceOnlyReadoutDensity_zero G H, sub_self, rectangularTraceNorm_zero]

end Matrix
