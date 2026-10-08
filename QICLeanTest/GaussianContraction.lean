/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).
-/
import QICLean.Probability.ComplexGaussian.GaussianContraction

/-! Actual Gaussian contraction regressions: empty positions, empty supports, unequal
branch supports, complex coefficients, unnormalized and zero weights, nonempty correction
centering, and the essential positive sample count. -/

noncomputable section

open MeasureTheory QICLean.ComplexGaussian
open scoped BigOperators Matrix.Norms.Elementwise

local instance : ContinuousENorm (Matrix (Fin 2) (Fin 3) ℂ) :=
  SeminormedAddGroup.toContinuousENorm

-- An empty set of positions leaves the arbitrary rectangular coefficient unchanged,
-- even when the algebraic source definition has zero samples.
example (k : ℕ) (K : Matrix (Fin 2) (Fin 3) ℂ)
    (ω : (p : Fin 0) → (b : Fin 2) → Sample (Fin k × (Fin 1 × Fin 2))) :
    gaussianSourceContraction k (fun _ : Fin 0 ↦ (0 : Fin 2))
      (fun (_ : Fin 0) (_ : Fin 1) ↦ 4) (fun (_ : Fin 0) (_ : Fin 2) ↦ 9) (fun _ ↦ K) ω = K := by
  rw [gaussianSourceContraction, Matrix.sourceContraction_apply]
  simp

-- A genuine empty ket support annihilates the actual sampled contraction.
example (k : ℕ)
    (coeff : ((p : Fin 1) → (Fin 0 × Fin 0) × (Fin 3 × Fin 3)) →
      Matrix (Fin 2) (Fin 1) ℂ)
    (ω : (p : Fin 1) → (b : Fin 2) → Sample (Fin k × (Fin 0 × Fin 3))) :
    gaussianSourceContraction k (fun _ : Fin 1 ↦ (1 : Fin 2))
      (fun (_ : Fin 1) (_ : Fin 0) ↦ 4) (fun (_ : Fin 1) (_ : Fin 3) ↦ 9) coeff ω = 0 := by
  let : IsEmpty ((p : Fin 1) → (Fin 0 × Fin 0) × (Fin 3 × Fin 3)) :=
    ⟨fun x ↦ Fin.elim0 (x 0).1.1⟩
  rw [gaussianSourceContraction, Matrix.sourceContraction_apply]
  simp

namespace GaussianContractionRegression

private abbrev Branch (_ : Fin 2) := Fin 2
private abbrev Ket (_ : Fin 2) (b : Fin 2) := Fin (if b = 0 then 1 else 2)
private abbrev Bra (_ : Fin 2) (b : Fin 2) := Fin (if b = 0 then 3 else 2)
private def selector (p : Fin 2) : Branch p := if p = 0 then 0 else 1
private def lam (p : Fin 2) (_ : Ket p (selector p)) : ℝ := 4
private def mu (p : Fin 2) (c : Bra p (selector p)) : ℝ := if c.val = 0 then 9 else 0
private abbrev Index := (p : Fin 2) →
  (Ket p (selector p) × Ket p (selector p)) × (Bra p (selector p) × Bra p (selector p))
private def coeff (_ : Index) : Matrix (Fin 2) (Fin 3) ℂ :=
  Matrix.of fun a _ ↦ if a = 0 then Complex.I else -Complex.I
private theorem hlam (p : Fin 2) (a : Ket p (selector p)) : 0 ≤ lam p a := by
  norm_num [lam]
private theorem hmu (p : Fin 2) (c : Bra p (selector p)) : 0 ≤ mu p c := by
  by_cases h : c.val = 0 <;> simp [mu, h]

-- Different branch support sizes and rectangular complex output coefficients are valid.
-- The weights deliberately have sums different from one.
example : Integrable (gaussianSourceContraction 3 selector lam mu coeff)
    (globalBranchLaw 3 Ket Bra) :=
  integrable_gaussianSourceContraction 3 (by norm_num) selector lam mu hlam hmu coeff

example :
    (∫ ω, gaussianSourceContraction 3 selector lam mu coeff ω ∂globalBranchLaw 3 Ket Bra) =
      Matrix.sourceContraction coeff (fun p ↦ schmidtSource (lam p) (mu p)) :=
  integral_gaussianSourceContraction 3 (by norm_num) selector lam mu hlam hmu coeff

-- Just the first corrected position has mean zero on the same global branch law;
-- the second position and the unused branches are integrated out.
example :
    (∫ ω, correctedGaussianSourceContraction 3 selector lam mu coeff {0} ω
      ∂globalBranchLaw 3 Ket Bra) = 0 :=
  integral_correctedGaussianSourceContraction_eq_zero 3 (by norm_num) selector lam mu
    hlam hmu coeff {0} (by simp)

-- A zero ket weight is permitted and makes the exact mean zero without division.
example :
    (∫ ω, gaussianSourceContraction 3 selector (fun p (_ : Ket p (selector p)) ↦ 0)
      mu coeff ω ∂globalBranchLaw 3 Ket Bra) = 0 := by
  rw [integral_gaussianSourceContraction 3 (by norm_num) selector
    (fun p (_ : Ket p (selector p)) ↦ 0) mu (by intros; norm_num) hmu coeff]
  apply (Matrix.sourceContraction coeff).map_coord_zero (0 : Fin 2)
  ext a b
  simp [schmidtSource_apply]

end GaussianContractionRegression

-- With no samples, every actual sampled source is zero. At a nonempty position this
-- gives zero output, which explains why the unbiasedness theorem requires k > 0.
example
    (coeff : ((p : Fin 1) → (Fin 1 × Fin 1) × (Fin 1 × Fin 1)) →
      Matrix (Fin 1) (Fin 1) ℂ)
    (ω : (p : Fin 1) → (b : Fin 1) → Sample (Fin 0 × (Fin 1 × Fin 1))) :
    gaussianSourceContraction 0 (fun _ : Fin 1 ↦ (0 : Fin 1))
      (fun (_ : Fin 1) (_ : Fin 1) ↦ 1) (fun (_ : Fin 1) (_ : Fin 1) ↦ 1) coeff ω = 0 := by
  unfold gaussianSourceContraction
  apply (Matrix.sourceContraction coeff).map_coord_zero (0 : Fin 1)
  simp [sampledSource]

-- The corresponding exact source need not vanish: singleton unit Schmidt data and
-- a unit coefficient contract to one, unlike the zero-sample output above.
example :
    Matrix.sourceContraction
      (fun _ : (p : Fin 1) → (Fin 1 × Fin 1) × (Fin 1 × Fin 1) ↦
        (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (fun _ ↦ schmidtSource (fun _ : Fin 1 ↦ 1) (fun _ : Fin 1 ↦ 1)) = 1 := by
  let x0 : (p : Fin 1) → (Fin 1 × Fin 1) × (Fin 1 × Fin 1) :=
    fun _ ↦ ((0, 0), (0, 0))
  let : Unique ((p : Fin 1) → (Fin 1 × Fin 1) × (Fin 1 × Fin 1)) :=
    { default := x0
      uniq x := by
        funext p
        exact Prod.ext (Prod.ext (Fin.eq_zero _) (Fin.eq_zero _))
          (Prod.ext (Fin.eq_zero _) (Fin.eq_zero _)) }
  ext a b
  rw [Matrix.sourceContraction_apply_apply, Fintype.sum_unique]
  change (1 : Matrix (Fin 1) (Fin 1) ℂ) a b *
    (∏ _ : Fin 1, schmidtSource (fun _ : Fin 1 ↦ 1) (fun _ : Fin 1 ↦ 1)
      (0, 0) (0, 0)) = (1 : Matrix (Fin 1) (Fin 1) ℂ) a b
  simp [schmidtSource_apply]
