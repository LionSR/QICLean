/-
Released under Apache 2.0 license as described in the file LICENSE.
Assisted-by: OpenAI Codex (GPT-6).
These constructions and proofs are independently written from the manuscript
and Mathlib; no upstream OpenAI Lean proof text is reused in this file.
The imported Gaussian foundation retains its own source and modification notices.
-/
import QICLean.Probability.ComplexGaussian.ProductSource

/-!
# Ambient transport of the Gaussian product source

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `04-compression.tex:279–309`, `eq:compression-random-source`.

Four local basis matrices embed the ket and bra Schmidt supports into finite
ambient endpoint spaces. The exact product and expectation identities hold for
arbitrary basis matrices, and hence apply to isometric Schmidt basis embeddings.
The resulting source is the outer product of the explicitly represented ambient
Schmidt vectors. The ambient endpoint dimensions may all differ.
-/

open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate Kronecker Matrix.Norms.Elementwise

namespace QICLean.ComplexGaussian

noncomputable section

variable {A C W X Y Z : Type*} [Fintype A] [Fintype C]
    [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq A] [DecidableEq C]

-- Matrix's norm is inherited from finite function spaces; expose its continuous enorm directly.
local instance {m n : Type*} [Fintype m] [Fintype n] : ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The ambient Schmidt vector in explicit local bases.
Source: `04-compression.tex:281–289`. -/
/-
Provenance-ID: p09-qic-product-transport-ambientschmidtvector
Downstream declaration: QICLean.ComplexGaussian.ambientSchmidtVector
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
def ambientSchmidtVector (lam : A → ℝ) (E : Matrix W A ℂ) (F : Matrix X A ℂ)
    (p : W × X) : ℂ :=
  ∑ a, (Real.sqrt (lam a) : ℂ) * E p.1 a * F p.2 a

/-- The actual ambient ket/bra outer product specified by the two Schmidt representations.
Source: `eq:compression-random-source`, `04-compression.tex:281–305`. -/
/-
Provenance-ID: p09-qic-product-transport-ambientschmidtsource
Downstream declaration: QICLean.ComplexGaussian.ambientSchmidtSource
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
def ambientSchmidtSource (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    Matrix (W × X) (Y × Z) ℂ :=
  Matrix.vecMulVec (ambientSchmidtVector lam E F)
    (fun q ↦ conj (ambientSchmidtVector mu Et Ft q))

/-- Transport a rectangular coordinate source through its ket and bra endpoint bases.
Source: `eq:compression-random-source`, `04-compression.tex:294–309`. -/
/-
Provenance-ID: p09-qic-product-transport-sourcetransport
Downstream declaration: QICLean.ComplexGaussian.sourceTransport
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
def sourceTransport (E : Matrix W A ℂ) (F : Matrix X A ℂ)
    (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (M : Matrix (A × A) (C × C) ℂ) : Matrix (W × X) (Y × Z) ℂ :=
  (E ⊗ₖ F) * M * (Et ⊗ₖ Ft).conjTranspose

/-- The first actual sampled source operator in its ambient endpoint bases.
Source: `eq:compression-random-source`, `04-compression.tex:294–297`. -/
/-
Provenance-ID: p09-qic-product-transport-ambientsourceu
Downstream declaration: QICLean.ComplexGaussian.ambientSourceU
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
def ambientSourceU (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (Et : Matrix Y C ℂ) (j : Fin k)
    (x : Sample (Fin k × (A × C))) : Matrix W Y ℂ :=
  E * sourceU k lam mu j x * Et.conjTranspose

/-- The second actual sampled source operator in its ambient endpoint bases.
Source: `eq:compression-random-source`, `04-compression.tex:297–300`. -/
/-
Provenance-ID: p09-qic-product-transport-ambientsourcev
Downstream declaration: QICLean.ComplexGaussian.ambientSourceV
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
def ambientSourceV (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (F : Matrix X A ℂ) (Ft : Matrix Z C ℂ) (j : Fin k)
    (x : Sample (Fin k × (A × C))) : Matrix X Z ℂ :=
  F * sourceV k lam mu j x * Ft.conjTranspose

/-- The sampled product-operator average acting between ambient endpoint spaces.
Source: `eq:compression-random-source`, `04-compression.tex:300–309`. -/
/-
Provenance-ID: p09-qic-product-transport-ambientsampledsource
Downstream declaration: QICLean.ComplexGaussian.ambientSampledSource
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
def ambientSampledSource (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (x : Sample (Fin k × (A × C))) : Matrix (W × X) (Y × Z) ℂ :=
  (k : ℂ)⁻¹ • ∑ j : Fin k,
    ambientSourceU k lam mu E Et j x ⊗ₖ ambientSourceV k lam mu F Ft j x

/-- The actual centered ambient source replacement.
Source: `eq:compression-random-source`, `04-compression.tex:302–305`. -/
/-
Provenance-ID: p09-qic-product-transport-ambientsourcecorrection
Downstream declaration: QICLean.ComplexGaussian.ambientSourceCorrection
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
def ambientSourceCorrection (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (x : Sample (Fin k × (A × C))) : Matrix (W × X) (Y × Z) ℂ :=
  ambientSampledSource k lam mu E F Et Ft x - ambientSchmidtSource lam mu E F Et Ft

omit [Fintype C] [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-ambientschmidtvector_eq_mulvec
Downstream declaration: QICLean.ComplexGaussian.ambientSchmidtVector_eq_mulVec
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem ambientSchmidtVector_eq_mulVec (lam : A → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) :
    ambientSchmidtVector lam E F = (E ⊗ₖ F) *ᵥ schmidtVector lam := by
  funext p
  simp only [Matrix.mulVec_apply_eq_sum, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, schmidtVector,
    mul_ite, mul_zero]
  change (∑ a, (Real.sqrt (lam a) : ℂ) * E p.1 a * F p.2 a) =
    ∑ a, ∑ b, if a = b then (E p.1 a * F p.2 b) * (Real.sqrt (lam a) : ℂ) else 0
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq A] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-sourcetransport_kronecker
Downstream declaration: QICLean.ComplexGaussian.sourceTransport_kronecker
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem sourceTransport_kronecker (E : Matrix W A ℂ) (F : Matrix X A ℂ)
    (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) (U V : Matrix A C ℂ) :
    sourceTransport E F Et Ft (U ⊗ₖ V) =
      (E * U * Et.conjTranspose) ⊗ₖ (F * V * Ft.conjTranspose) := by
  simp only [sourceTransport, Matrix.mul_kronecker_mul, Matrix.conjTranspose_kronecker]

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq A] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-ambientsourceu_kronecker_ambientsourcev
Downstream declaration: QICLean.ComplexGaussian.ambientSourceU_kronecker_ambientSourceV
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem ambientSourceU_kronecker_ambientSourceV (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (j : Fin k) (x : Sample (Fin k × (A × C))) :
    ambientSourceU k lam mu E Et j x ⊗ₖ ambientSourceV k lam mu F Ft j x =
      sourceTransport E F Et Ft (sourceU k lam mu j x ⊗ₖ sourceV k lam mu j x) :=
  (sourceTransport_kronecker E F Et Ft _ _).symm

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq A] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-ambientsampledsource_eq_transport
Downstream declaration: QICLean.ComplexGaussian.ambientSampledSource_eq_transport
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem ambientSampledSource_eq_transport (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (x : Sample (Fin k × (A × C))) :
    ambientSampledSource k lam mu E F Et Ft x =
      sourceTransport E F Et Ft (sampledSource k lam mu x) := by
  simp only [ambientSampledSource, ambientSourceU_kronecker_ambientSourceV,
    sourceTransport, sampledSource, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] in
/-
Provenance-ID: p09-qic-product-transport-sourcetransport_schmidtsource
Downstream declaration: QICLean.ComplexGaussian.sourceTransport_schmidtSource
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem sourceTransport_schmidtSource (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    sourceTransport E F Et Ft (schmidtSource lam mu) =
      ambientSchmidtSource lam mu E F Et Ft := by
  unfold ambientSchmidtSource
  rw [ambientSchmidtVector_eq_mulVec, ambientSchmidtVector_eq_mulVec]
  simp only [sourceTransport, schmidtSource, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  exact (Matrix.star_mulVec _ _).symm

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] in
/-
Provenance-ID: p09-qic-product-transport-ambientsourcecorrection_eq_transport
Downstream declaration: QICLean.ComplexGaussian.ambientSourceCorrection_eq_transport
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem ambientSourceCorrection_eq_transport (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (x : Sample (Fin k × (A × C))) :
    ambientSourceCorrection k lam mu E F Et Ft x =
      sourceTransport E F Et Ft (sourceCorrection k lam mu x) := by
  rw [ambientSourceCorrection, ambientSampledSource_eq_transport,
    ← sourceTransport_schmidtSource]
  simp only [sourceTransport, sourceCorrection, Matrix.mul_sub, Matrix.sub_mul]

private theorem integrable_sandwich_entry {Ω m n r s : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] (μ : Measure Ω)
    (L : Matrix r m ℂ) (R : Matrix n s ℂ) (f : Ω → Matrix m n ℂ)
    (hf : ∀ i j, Integrable (fun x ↦ f x i j) μ) (p : r) (q : s) :
    Integrable (fun x ↦ (L * f x * R) p q) μ := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro i _
  exact ((hf i j).const_mul _).mul_const _

private theorem integral_sandwich_entry {Ω m n r s : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] (μ : Measure Ω)
    (L : Matrix r m ℂ) (R : Matrix n s ℂ) (f : Ω → Matrix m n ℂ)
    (hf : ∀ i j, Integrable (fun x ↦ f x i j) μ) (p : r) (q : s) :
    (∫ x, (L * f x * R) p q ∂μ) =
      (L * Matrix.of (fun i j ↦ ∫ x, f x i j ∂μ) * R) p q := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.of_apply]
  rw [integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _
    (fun i _ ↦ ((hf i j).const_mul _).mul_const _))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun i _ ↦ ((hf i j).const_mul _).mul_const _)]
  simp only [integral_mul_const, integral_const_mul]

private theorem integrable_matrix_of_entries {Ω m n : Type*} [MeasurableSpace Ω]
    [Fintype m] [Fintype n] (μ : Measure Ω) (f : Ω → Matrix m n ℂ)
    (hf : ∀ i j, Integrable (fun x ↦ f x i j) μ) : Integrable f μ := by
  have hpi : Integrable (fun x ↦ ((fun i j ↦ f x i j) : m → n → ℂ)) μ :=
    Integrable.of_eval fun i ↦ Integrable.of_eval fun j ↦ hf i j
  have hMatrix : AEStronglyMeasurable f μ :=
    (show Continuous (Matrix.of (m := m) (n := n) (α := ℂ)) from
      continuous_id.matrixOf).comp_aestronglyMeasurable hpi.aestronglyMeasurable
  exact hpi.congr'_enorm hMatrix (Filter.Eventually.of_forall fun _ ↦ rfl)

omit [Fintype X] [Fintype Z] [DecidableEq A] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-integrable_ambientsourceu
Downstream declaration: QICLean.ComplexGaussian.integrable_ambientSourceU
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem integrable_ambientSourceU (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (Et : Matrix Y C ℂ) (j : Fin k) :
    Integrable (ambientSourceU k lam mu E Et j) (law (Fin k × (A × C))) := by
  apply integrable_matrix_of_entries
  intro p q
  apply integrable_sandwich_entry
  intro a c
  simp only [sourceU, Matrix.of_apply]
  exact ((memLp_coordinate (j, (a, c)) 1 (by norm_num)).integrable (by norm_num)).const_mul _

omit [Fintype W] [Fintype Y] [DecidableEq A] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-integrable_ambientsourcev
Downstream declaration: QICLean.ComplexGaussian.integrable_ambientSourceV
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem integrable_ambientSourceV (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (F : Matrix X A ℂ) (Ft : Matrix Z C ℂ) (j : Fin k) :
    Integrable (ambientSourceV k lam mu F Ft j) (law (Fin k × (A × C))) := by
  apply integrable_matrix_of_entries
  intro p q
  apply integrable_sandwich_entry
  intro a c
  simp only [sourceV, Matrix.of_apply]
  exact ((memLp_conj_coordinate (j, (a, c)) 1 (by norm_num)).integrable
    (by norm_num)).const_mul _

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq A] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-integrable_ambientsampledsource_entry
Downstream declaration: QICLean.ComplexGaussian.integrable_ambientSampledSource_entry
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem integrable_ambientSampledSource_entry (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (p : W × X) (q : Y × Z) :
    Integrable (fun x ↦ ambientSampledSource k lam mu E F Et Ft x p q)
      (law (Fin k × (A × C))) := by
  simp_rw [ambientSampledSource_eq_transport]
  exact integrable_sandwich_entry _ _ _ _
    (integrable_sampledSource_entry k hk lam mu hlam hmu) p q

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq A] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-integral_ambientsampledsource_entry
Downstream declaration: QICLean.ComplexGaussian.integral_ambientSampledSource_entry
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem integral_ambientSampledSource_entry (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (p : W × X) (q : Y × Z) :
    (∫ x, ambientSampledSource k lam mu E F Et Ft x p q ∂law (Fin k × (A × C))) =
      ambientSchmidtSource lam mu E F Et Ft p q := by
  classical
  simp_rw [ambientSampledSource_eq_transport]
  change (∫ x, ((E ⊗ₖ F) * sampledSource k lam mu x * (Et ⊗ₖ Ft).conjTranspose) p q
    ∂law (Fin k × (A × C))) = _
  rw [integral_sandwich_entry _ _ _ _
    (integrable_sampledSource_entry k hk lam mu hlam hmu)]
  simp_rw [integral_sampledSource_entry k hk lam mu hlam hmu]
  exact congrArg (fun M ↦ M p q) (sourceTransport_schmidtSource lam mu E F Et Ft)

omit [DecidableEq A] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-integrable_ambientsampledsource
Downstream declaration: QICLean.ComplexGaussian.integrable_ambientSampledSource
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem integrable_ambientSampledSource (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    Integrable (ambientSampledSource k lam mu E F Et Ft) (law (Fin k × (A × C))) :=
  integrable_matrix_of_entries _ _
    (integrable_ambientSampledSource_entry k hk lam mu hlam hmu E F Et Ft)

omit [DecidableEq A] [DecidableEq C] in
/-- Genuine matrix-valued unbiasedness in the ambient endpoint spaces.
Source: `eq:compression-random-source`, `04-compression.tex:294–309`. -/
/-
Provenance-ID: p09-qic-product-transport-integral_ambientsampledsource
Downstream declaration: QICLean.ComplexGaussian.integral_ambientSampledSource
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem integral_ambientSampledSource (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    (∫ x, ambientSampledSource k lam mu E F Et Ft x ∂law (Fin k × (A × C))) =
      ambientSchmidtSource lam mu E F Et Ft := by
  ext p q
  change (∫ x, (fun p q ↦ ambientSampledSource k lam mu E F Et Ft x p q)
    ∂law (Fin k × (A × C))) p q = _
  have hr (p : W × X) : Integrable
      (fun x ↦ (fun q ↦ ambientSampledSource k lam mu E F Et Ft x p q))
      (law (Fin k × (A × C))) := Integrable.of_eval fun q ↦
    integrable_ambientSampledSource_entry k hk lam mu hlam hmu E F Et Ft p q
  rw [eval_integral hr, eval_integral (fun q ↦
    integrable_ambientSampledSource_entry k hk lam mu hlam hmu E F Et Ft p q),
    integral_ambientSampledSource_entry k hk lam mu hlam hmu]

omit [DecidableEq A] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-integrable_ambientsourcecorrection
Downstream declaration: QICLean.ComplexGaussian.integrable_ambientSourceCorrection
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem integrable_ambientSourceCorrection (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    Integrable (ambientSourceCorrection k lam mu E F Et Ft)
      (law (Fin k × (A × C))) :=
  (integrable_ambientSampledSource k hk lam mu hlam hmu E F Et Ft).sub (integrable_const _)

omit [DecidableEq A] [DecidableEq C] in
/-
Provenance-ID: p09-qic-product-transport-integral_ambientsourcecorrection
Downstream declaration: QICLean.ComplexGaussian.integral_ambientSourceCorrection
Source: September 24, 2026.
Label: eq:compression-random-source.
Independently formalized; no upstream Lean proof text reused.
Paper URL: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L279-L309
-/
theorem integral_ambientSourceCorrection (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    (∫ x, ambientSourceCorrection k lam mu E F Et Ft x ∂law (Fin k × (A × C))) = 0 := by
  change (∫ x, ambientSampledSource k lam mu E F Et Ft x -
    ambientSchmidtSource lam mu E F Et Ft ∂law (Fin k × (A × C))) = 0
  rw [integral_sub (integrable_ambientSampledSource k hk lam mu hlam hmu E F Et Ft)
    (integrable_const _), integral_ambientSampledSource k hk lam mu hlam hmu]
  simp

end

end QICLean.ComplexGaussian
