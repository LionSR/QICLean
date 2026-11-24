/-
Released under Apache 2.0 license as described in the file LICENSE.
Assisted-by: OpenAI Codex (GPT-6).
These constructions and proofs are independently written from the manuscript
and Mathlib; no upstream OpenAI Lean proof text is reused in this file.
The imported Gaussian foundation retains its own source and modification notices.
-/
import QICLean.Probability.Gaussian.ProductSource

/-!
# Ambient transport of the Gaussian product source

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `04-compression.tex:279–309`, `eq:compression-random-source`.

Four local basis matrices embed the ket and bra Schmidt supports into finite
ambient endpoint spaces. The exact product and expectation identities hold for
arbitrary basis matrices, and hence apply to isometric Schmidt basis embeddings.
The resulting source is the outer product of the explicitly represented ambient
Schmidt vectors. The ambient endpoint dimensions may all differ. The matrices themselves
are `ProductSource.ambientSampledSource` and `ProductSource.ambientSourceCorrection`.
-/

open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate Kronecker Matrix.Norms.Elementwise

namespace QICLean.ComplexGaussian

open ProductSource

noncomputable section

variable {A C W X Y Z : Type*} [Fintype A] [Fintype C]
    [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq A] [DecidableEq C]

-- Matrix's norm is inherited from finite function spaces; expose its continuous enorm directly.
local instance {m n : Type*} [Fintype m] [Fintype n] : ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

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
theorem integrable_ambientSampledSource_entry (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (p : W × X) (q : Y × Z) :
    Integrable (fun x ↦ ambientSampledSource k lam mu E F Et Ft x p q)
      (law (Fin k × (A × C))) := by
  simp_rw [ProductSource.ambientSampledSource_eq_kroneckerSandwich]
  exact integrable_sandwich_entry _ _ _ _
    (integrable_sampledSource_entry k hk lam mu hlam hmu) p q

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq A] [DecidableEq C] in
theorem integral_ambientSampledSource_entry (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (p : W × X) (q : Y × Z) :
    (∫ x, ambientSampledSource k lam mu E F Et Ft x p q ∂law (Fin k × (A × C))) =
      Matrix.schmidtFrameOuterProduct lam mu E F Et Ft p q := by
  classical
  simp_rw [ProductSource.ambientSampledSource_eq_kroneckerSandwich]
  change (∫ x, ((E ⊗ₖ F) * sampledSource k lam mu x * (Et ⊗ₖ Ft).conjTranspose) p q
    ∂law (Fin k × (A × C))) = _
  rw [integral_sandwich_entry _ _ _ _
    (integrable_sampledSource_entry k hk lam mu hlam hmu)]
  simp_rw [integral_sampledSource_entry k hk lam mu hlam hmu]
  exact congrArg (fun M ↦ M p q) (Matrix.kroneckerSandwich_schmidtOuterProduct lam mu E F Et Ft)

omit [DecidableEq A] [DecidableEq C] in
theorem integrable_ambientSampledSource (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    Integrable (ambientSampledSource k lam mu E F Et Ft) (law (Fin k × (A × C))) :=
  integrable_matrix_of_entries _ _
    (integrable_ambientSampledSource_entry k hk lam mu hlam hmu E F Et Ft)

omit [DecidableEq A] [DecidableEq C] in
/-- Genuine matrix-valued unbiasedness in the ambient endpoint spaces.
Source: `eq:compression-random-source`, `04-compression.tex:294–309`. -/
theorem integral_ambientSampledSource (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    (∫ x, ambientSampledSource k lam mu E F Et Ft x ∂law (Fin k × (A × C))) =
      Matrix.schmidtFrameOuterProduct lam mu E F Et Ft := by
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
theorem integrable_ambientSourceCorrection (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    Integrable (ambientSourceCorrection k lam mu E F Et Ft)
      (law (Fin k × (A × C))) :=
  (integrable_ambientSampledSource k hk lam mu hlam hmu E F Et Ft).sub (integrable_const _)

omit [DecidableEq A] [DecidableEq C] in
theorem integral_ambientSourceCorrection (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    (∫ x, ambientSourceCorrection k lam mu E F Et Ft x ∂law (Fin k × (A × C))) = 0 := by
  change (∫ x, ambientSampledSource k lam mu E F Et Ft x -
    Matrix.schmidtFrameOuterProduct lam mu E F Et Ft ∂law (Fin k × (A × C))) = 0
  rw [integral_sub (integrable_ambientSampledSource k hk lam mu hlam hmu E F Et Ft)
    (integrable_const _), integral_ambientSampledSource k hk lam mu hlam hmu]
  simp

end

end QICLean.ComplexGaussian
