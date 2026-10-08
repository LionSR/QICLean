/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).

These are original integration proofs of the cited mathematical argument. No OpenAI Lean
proof text is copied or adapted here. The imported Gaussian construction retains its explicit
source and modification notices in Basic.lean and Covariance.lean.
-/
import QICLean.Probability.ComplexGaussian.GlobalBranchLaw
import QICLean.Probability.ComplexGaussian.ProductSource
import QICLean.Analysis.SourceContraction

/-!
# Global unbiasedness of actual Gaussian source contractions

A finite coefficient array is contracted with the actual sampled Schmidt-source matrices on
one global Gaussian law. The sampled-minus-exact output is its literal nonempty corrected-
position expansion. Each corrected term factors into exact outside entries and the actual
selected Gaussian correction coefficients, so every nonempty term has zero expectation.
The whole sampled output is genuinely Bochner-integrable and has the exact contraction as
its expectation. Source probabilities need only be nonnegative; normalization is unnecessary.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 5.2,
`eq:compression-random-source` and `eq:compression-subset-expansion`,
`04-compression.tex:279--379`, OpenAI/math revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The coefficient array and deterministic branch selector are supplied data. No norm bound or
identification with an actual distributed circuit or tensor network is asserted here.
Positive sample count is essential to the centered-source entry identity.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace QICLean.ComplexGaussian

variable {P : Type*} [Fintype P] [DecidableEq P] {B : P → Type*} [∀ p, Fintype (B p)]
    {A C : (p : P) → B p → Type*}
    [∀ p b, Fintype (A p b)] [∀ p b, Fintype (C p b)]
    [∀ p b, DecidableEq (A p b)] [∀ p b, DecidableEq (C p b)]
    {m n : Type*}

/-- The actual finite contraction of globally sampled source matrices for fixed branch labels.
Source: Theorem 5.2, `eq:compression-random-source`, `04-compression.tex:279--340`. -/

def gaussianSourceContraction (k : ℕ) (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (coeff : ((p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) →
      Matrix m n ℂ)
    (ω : (p : P) → (b : B p) → Sample (Fin k × (A p b × C p b))) : Matrix m n ℂ :=
  Matrix.sourceContraction coeff (fun p ↦ sampledSource k (lam p) (mu p) (ω p (σ p)))

/-- A literal corrected-position term: actual centered sources at `S`, exact sources elsewhere.
Source: Theorem 5.2, `eq:compression-subset-expansion`, `04-compression.tex:342--379`. -/

def correctedGaussianSourceContraction (k : ℕ) (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (coeff : ((p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) →
      Matrix m n ℂ) (S : Finset P)
    (ω : (p : P) → (b : B p) → Sample (Fin k × (A p b × C p b))) : Matrix m n ℂ :=
  Matrix.sourceContraction coeff (S.piecewise
    (fun p ↦ sourceCorrection k (lam p) (mu p) (ω p (σ p)))
    (fun p ↦ schmidtSource (lam p) (mu p)))

omit [∀ p, Fintype (B p)] in
/-- Actual correction-entry products use exactly the selected-position Gaussian coefficients.
Source: Theorem 5.2, `eq:compression-random-source`, `04-compression.tex:311--379`. -/

theorem corrected_source_entry_product (k : ℕ) (hk : 0 < k) (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (hlam : ∀ p a, 0 ≤ lam p a) (hmu : ∀ p c, 0 ≤ mu p c) (S : Finset P)
    (x : (p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p)))
    (ω : (p : P) → (b : B p) → Sample (Fin k × (A p b × C p b))) :
    (∏ p, (S.piecewise
      (fun p ↦ sourceCorrection k (lam p) (mu p) (ω p (σ p)))
      (fun p ↦ schmidtSource (lam p) (mu p)) p) (x p).1 (x p).2) =
      (∏ p ∈ Finset.univ \ S, schmidtSource (lam p) (mu p) (x p).1 (x p).2) *
        selectedBranchDensityCoefficient k S (fun p ↦ σ p)
          (fun p ↦ lam p) (fun p ↦ mu p) (fun p ↦ (x p).1) (fun p ↦ (x p).2) ω := by
  have hentry (p : P) :
      (S.piecewise (fun p ↦ sourceCorrection k (lam p) (mu p) (ω p (σ p)))
        (fun p ↦ schmidtSource (lam p) (mu p)) p) (x p).1 (x p).2 =
      S.piecewise (fun p ↦ densityCoefficient k (lam p) (mu p) (x p) (ω p (σ p)))
        (fun p ↦ schmidtSource (lam p) (mu p) (x p).1 (x p).2) p := by
    by_cases hp : p ∈ S
    · simp only [Finset.piecewise, hp, ite_true]
      exact sourceCorrection_apply k hk (lam p) (mu p) (hlam p) (hmu p) _ _ _
    · simp only [Finset.piecewise, hp, ite_false]
  let f : P → ℂ := fun p ↦ densityCoefficient k (lam p) (mu p) (x p) (ω p (σ p))
  let g : P → ℂ := fun p ↦ schmidtSource (lam p) (mu p) (x p).1 (x p).2
  have hprod : (∏ p, (S.piecewise
      (fun p ↦ sourceCorrection k (lam p) (mu p) (ω p (σ p)))
      (fun p ↦ schmidtSource (lam p) (mu p)) p) (x p).1 (x p).2) =
      ∏ p, S.piecewise f g p := Finset.prod_congr rfl (fun p _ ↦ hentry p)
  have hcoef : selectedBranchDensityCoefficient k S (fun p ↦ σ p)
      (fun p ↦ lam p) (fun p ↦ mu p) (fun p ↦ (x p).1) (fun p ↦ (x p).2) ω =
      ∏ p ∈ S, f p := by
    change (∏ p : S, f p) = ∏ p ∈ S, f p
    exact Finset.prod_coe_sort S f
  change _ = (∏ p ∈ Finset.univ \ S, g p) * _
  rw [hprod, Finset.prod_piecewise, Finset.univ_inter, hcoef]
  exact mul_comm _ _

omit [∀ p, Fintype (B p)] in
/-- Each corrected contraction is the finite sum of its explicitly factored source entries.
Source: Theorem 5.2, `eq:compression-subset-expansion`, `04-compression.tex:342--379`. -/

theorem correctedGaussianSourceContraction_eq_sum (k : ℕ) (hk : 0 < k)
    (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (hlam : ∀ p a, 0 ≤ lam p a) (hmu : ∀ p c, 0 ≤ mu p c)
    (coeff : ((p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) →
      Matrix m n ℂ) (S : Finset P)
    (ω : (p : P) → (b : B p) → Sample (Fin k × (A p b × C p b))) :
    correctedGaussianSourceContraction k σ lam mu coeff S ω =
      ∑ x, ((∏ p ∈ Finset.univ \ S, schmidtSource (lam p) (mu p) (x p).1 (x p).2) *
        selectedBranchDensityCoefficient k S (fun p ↦ σ p)
          (fun p ↦ lam p) (fun p ↦ mu p) (fun p ↦ (x p).1) (fun p ↦ (x p).2) ω) • coeff x := by
  rw [correctedGaussianSourceContraction, Matrix.sourceContraction_apply]
  simp_rw [corrected_source_entry_product k hk σ lam mu hlam hmu S]

omit [∀ p, Fintype (B p)] in
/-- The actual sampled-minus-exact output is the literal nonempty corrected-position sum.
Source: Theorem 5.2, `eq:compression-subset-expansion`, `04-compression.tex:342--355`. -/

theorem gaussianSourceContraction_sub (k : ℕ) (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (coeff : ((p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) →
      Matrix m n ℂ)
    (ω : (p : P) → (b : B p) → Sample (Fin k × (A p b × C p b))) :
    gaussianSourceContraction k σ lam mu coeff ω -
        Matrix.sourceContraction coeff (fun p ↦ schmidtSource (lam p) (mu p)) =
      ∑ S ∈ (Finset.univ : Finset (Finset P)).erase ∅,
        correctedGaussianSourceContraction k σ lam mu coeff S ω := by
  have hadd : (fun p ↦ sampledSource k (lam p) (mu p) (ω p (σ p))) =
      (fun p ↦ sourceCorrection k (lam p) (mu p) (ω p (σ p))) +
        (fun p ↦ schmidtSource (lam p) (mu p)) := by
    funext p
    exact (sub_add_cancel _ _).symm
  simpa only [gaussianSourceContraction, hadd, correctedGaussianSourceContraction] using
    Matrix.sourceContraction_sub coeff (fun p ↦ schmidtSource (lam p) (mu p))
      (fun p ↦ sourceCorrection k (lam p) (mu p) (ω p (σ p)))

private theorem integrable_factored_corrected_entry (k : ℕ) (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ) (S : Finset P)
    (x : (p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) :
    Integrable (fun ω ↦
      (∏ p ∈ Finset.univ \ S, schmidtSource (lam p) (mu p) (x p).1 (x p).2) *
        selectedBranchDensityCoefficient k S (fun p ↦ σ p)
          (fun p ↦ lam p) (fun p ↦ mu p) (fun p ↦ (x p).1) (fun p ↦ (x p).2) ω)
      (globalBranchLaw k A C) :=
  (integrable_selectedBranchDensityCoefficient k S (fun p ↦ σ p)
    (fun p ↦ lam p) (fun p ↦ mu p) (fun p ↦ (x p).1) (fun p ↦ (x p).2)).const_mul _

variable [Fintype m] [Fintype n]

local instance : ContinuousENorm (Matrix m n ℂ) := SeminormedAddGroup.toContinuousENorm

private theorem integrable_matrix_entries {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f : Ω → Matrix m n ℂ)
    (hf : ∀ a b, Integrable (fun ω ↦ f ω a b) ν) : Integrable f ν := by
  have hpi : Integrable (fun ω ↦ ((fun a b ↦ f ω a b) : m → n → ℂ)) ν :=
    Integrable.of_eval fun a ↦ Integrable.of_eval fun b ↦ hf a b
  have hMatrix : AEStronglyMeasurable f ν :=
    (show Continuous (Matrix.of (m := m) (n := n) (α := ℂ)) from
      continuous_id.matrixOf).comp_aestronglyMeasurable hpi.aestronglyMeasurable
  exact hpi.congr'_enorm hMatrix (Filter.Eventually.of_forall fun _ ↦ rfl)

omit [Fintype m] [Fintype n] in
private theorem integrable_corrected_entry (k : ℕ) (hk : 0 < k) (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (hlam : ∀ p a, 0 ≤ lam p a) (hmu : ∀ p c, 0 ≤ mu p c)
    (coeff : ((p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) →
      Matrix m n ℂ) (S : Finset P) (a : m) (b : n) :
    Integrable (fun ω ↦ correctedGaussianSourceContraction k σ lam mu coeff S ω a b)
      (globalBranchLaw k A C) := by
  unfold correctedGaussianSourceContraction
  simp_rw [Matrix.sourceContraction_apply_apply,
    corrected_source_entry_product k hk σ lam mu hlam hmu S]
  exact integrable_finsetSum _ (fun x _ ↦
    (integrable_factored_corrected_entry k σ lam mu S x).const_mul (coeff x a b))

/-- Every actual corrected-position contraction is Bochner-integrable.
Source: Theorem 5.2, `eq:compression-subset-expansion`, `04-compression.tex:342--379`. -/

theorem integrable_correctedGaussianSourceContraction (k : ℕ) (hk : 0 < k)
    (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (hlam : ∀ p a, 0 ≤ lam p a) (hmu : ∀ p c, 0 ≤ mu p c)
    (coeff : ((p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) →
      Matrix m n ℂ) (S : Finset P) :
    Integrable (correctedGaussianSourceContraction k σ lam mu coeff S) (globalBranchLaw k A C) := by
  exact integrable_matrix_entries _ _
    (integrable_corrected_entry k hk σ lam mu hlam hmu coeff S)

/-- Every nonempty actual corrected-position contraction has zero global expectation.
Source: Theorem 5.2, centered corrections and `eq:compression-subset-expansion`,
`04-compression.tex:311--379`. No coefficient norm or probability normalization is needed. -/

theorem integral_correctedGaussianSourceContraction_eq_zero (k : ℕ) (hk : 0 < k)
    (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (hlam : ∀ p a, 0 ≤ lam p a) (hmu : ∀ p c, 0 ≤ mu p c)
    (coeff : ((p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) →
      Matrix m n ℂ) (S : Finset P) (hS : S.Nonempty) :
    (∫ ω, correctedGaussianSourceContraction k σ lam mu coeff S ω ∂globalBranchLaw k A C) = 0 := by
  let : Nonempty S := by rcases hS with ⟨p, hp⟩; exact ⟨⟨p, hp⟩⟩
  ext a b
  change (∫ ω, (fun a b ↦ correctedGaussianSourceContraction k σ lam mu coeff S ω a b)
    ∂globalBranchLaw k A C) a b = 0
  have hr (a : m) : Integrable (fun ω ↦ fun b ↦
      correctedGaussianSourceContraction k σ lam mu coeff S ω a b) (globalBranchLaw k A C) :=
    Integrable.of_eval (integrable_corrected_entry k hk σ lam mu hlam hmu coeff S a)
  rw [eval_integral hr,
    eval_integral (integrable_corrected_entry k hk σ lam mu hlam hmu coeff S a)]
  change (∫ ω, Matrix.sourceContraction coeff (S.piecewise
    (fun p ↦ sourceCorrection k (lam p) (mu p) (ω p (σ p)))
    (fun p ↦ schmidtSource (lam p) (mu p))) a b ∂globalBranchLaw k A C) = 0
  simp_rw [Matrix.sourceContraction_apply_apply,
    corrected_source_entry_product k hk σ lam mu hlam hmu S]
  rw [integral_finsetSum _ (fun x _ ↦
    (integrable_factored_corrected_entry k σ lam mu S x).const_mul (coeff x a b))]
  simp_rw [integral_const_mul, integral_selectedBranchDensityCoefficient_eq_zero]
  simp

omit [∀ p b, DecidableEq (A p b)] [∀ p b, DecidableEq (C p b)]
  [Fintype m] [Fintype n] in
open Classical in
private theorem integrable_gaussian_entry (k : ℕ) (hk : 0 < k) (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (hlam : ∀ p a, 0 ≤ lam p a) (hmu : ∀ p c, 0 ≤ mu p c)
    (coeff : ((p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) →
      Matrix m n ℂ) (a : m) (b : n) :
    Integrable (fun ω ↦ gaussianSourceContraction k σ lam mu coeff ω a b)
      (globalBranchLaw k A C) := by
  have heq (ω) := congrArg (fun M : Matrix m n ℂ ↦ M a b)
    (sub_eq_iff_eq_add.mp (gaussianSourceContraction_sub k σ lam mu coeff ω))
  simp only [Matrix.add_apply, Matrix.sum_apply] at heq
  simp_rw [heq]
  exact (integrable_finsetSum _ (fun S _ ↦
    integrable_corrected_entry k hk σ lam mu hlam hmu coeff S a b)).add (integrable_const _)

omit [∀ p b, DecidableEq (A p b)] [∀ p b, DecidableEq (C p b)] in
open Classical in
/-- The actual coefficient-contracted sampled output is globally Bochner-integrable.
Source: Theorem 5.2, `eq:compression-subset-expansion`, `04-compression.tex:342--379`. -/

theorem integrable_gaussianSourceContraction (k : ℕ) (hk : 0 < k) (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (hlam : ∀ p a, 0 ≤ lam p a) (hmu : ∀ p c, 0 ≤ mu p c)
    (coeff : ((p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) →
      Matrix m n ℂ) :
    Integrable (gaussianSourceContraction k σ lam mu coeff) (globalBranchLaw k A C) := by
  exact integrable_matrix_entries _ _ (integrable_gaussian_entry k hk σ lam mu hlam hmu coeff)

/-- The actual sampled contraction is globally unbiased for the exact Schmidt-source contraction.
Source: Theorem 5.2, `eq:compression-random-source` and `eq:compression-subset-expansion`,
`04-compression.tex:279--379`. The result follows from the literal nonempty-position expansion;
there is no supplied output expectation identity, coefficient norm or normalized weight premise. -/

theorem integral_gaussianSourceContraction (k : ℕ) (hk : 0 < k) (σ : (p : P) → B p)
    (lam : (p : P) → A p (σ p) → ℝ) (mu : (p : P) → C p (σ p) → ℝ)
    (hlam : ∀ p a, 0 ≤ lam p a) (hmu : ∀ p c, 0 ≤ mu p c)
    (coeff : ((p : P) → (A p (σ p) × A p (σ p)) × (C p (σ p) × C p (σ p))) →
      Matrix m n ℂ) :
    (∫ ω, gaussianSourceContraction k σ lam mu coeff ω ∂globalBranchLaw k A C) =
      Matrix.sourceContraction coeff (fun p ↦ schmidtSource (lam p) (mu p)) := by
  ext a b
  change (∫ ω, (fun a b ↦ gaussianSourceContraction k σ lam mu coeff ω a b)
    ∂globalBranchLaw k A C) a b = _
  have hr (a : m) : Integrable (fun ω ↦ fun b ↦
      gaussianSourceContraction k σ lam mu coeff ω a b) (globalBranchLaw k A C) :=
    Integrable.of_eval (integrable_gaussian_entry k hk σ lam mu hlam hmu coeff a)
  rw [eval_integral hr, eval_integral (integrable_gaussian_entry k hk σ lam mu hlam hmu coeff a)]
  have heq (ω) := congrArg (fun M : Matrix m n ℂ ↦ M a b)
    (sub_eq_iff_eq_add.mp (gaussianSourceContraction_sub k σ lam mu coeff ω))
  simp only [Matrix.add_apply, Matrix.sum_apply] at heq
  simp_rw [heq]
  rw [integral_add (integrable_finsetSum _ (fun S _ ↦
    integrable_corrected_entry k hk σ lam mu hlam hmu coeff S a b)) (integrable_const _),
    integral_finsetSum _ (fun S _ ↦
      integrable_corrected_entry k hk σ lam mu hlam hmu coeff S a b)]
  have hz (S : Finset P) (hS : S.Nonempty) :
      (∫ ω, correctedGaussianSourceContraction k σ lam mu coeff S ω a b
        ∂globalBranchLaw k A C) = 0 := by
    have hrS (a : m) : Integrable (fun ω ↦ fun b ↦
        correctedGaussianSourceContraction k σ lam mu coeff S ω a b) (globalBranchLaw k A C) :=
      Integrable.of_eval (integrable_corrected_entry k hk σ lam mu hlam hmu coeff S a)
    have he := congrArg (fun M : Matrix m n ℂ ↦ M a b)
      (integral_correctedGaussianSourceContraction_eq_zero k hk σ lam mu hlam hmu coeff S hS)
    change (∫ ω, (fun a b ↦ correctedGaussianSourceContraction k σ lam mu coeff S ω a b)
      ∂globalBranchLaw k A C) a b = 0 at he
    rwa [eval_integral hrS,
      eval_integral (integrable_corrected_entry k hk σ lam mu hlam hmu coeff S a)] at he
  have hzero : (∑ S ∈ (Finset.univ : Finset (Finset P)).erase ∅,
      ∫ ω, correctedGaussianSourceContraction k σ lam mu coeff S ω a b
        ∂globalBranchLaw k A C) = 0 :=
    Finset.sum_eq_zero (fun S hS ↦ hz S
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1))
  simp [hzero]

end QICLean.ComplexGaussian
