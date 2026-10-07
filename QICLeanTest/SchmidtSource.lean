/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.ComplexGaussian.SchmidtSource

/-! Boundary regressions for actual Schmidt frames and unbiased Gaussian source replacement. -/

open MeasureTheory Matrix QICLean.ComplexGaussian
open scoped BigOperators ComplexConjugate Matrix.Norms.Elementwise

noncomputable section

local instance {m n : Type*} [Fintype m] [Fintype n] : ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toContinuousENorm

private abbrev KetSupport := Fin (min (Fintype.card Bool) (Fintype.card (Fin 3)))
private abbrev BraSupport := Fin (min (Fintype.card Unit) (Fintype.card Bool))
private abbrev ZeroSupport := Fin (min (Fintype.card Bool) (Fintype.card (Option (Fin 2))))
private abbrev EmptySupport := Fin (min (Fintype.card (Fin 0)) (Fintype.card Bool))

private def phaseKet : EuclideanSpace ℂ (Bool × Fin 3) :=
  EuclideanSpace.single (false, 1) Complex.I

private def phaseBra : EuclideanSpace ℂ (Unit × Bool) :=
  EuclideanSpace.single ((), true) (-Complex.I)

-- Zero vectors keep genuine isometries but all their Schmidt weights vanish.
example : ∃ (lam : ZeroSupport → ℝ)
    (E : Matrix Bool ZeroSupport ℂ)
    (F : Matrix (Option (Fin 2)) ZeroSupport ℂ),
    (∀ a, lam a = 0) ∧ E.conjTranspose * E = 1 ∧ F.conjTranspose * F = 1 ∧
      ambientSchmidtVector lam E F = 0 := by
  classical
  obtain ⟨lam, E, F, hnonneg, hE, hF, hrepr, hmass⟩ :=
    exists_schmidtSourceFrames (0 : EuclideanSpace ℂ (Bool × Option (Fin 2)))
  have hzero : ∑ a, lam a = 0 := by simpa using hmass
  have hall : ∀ a, lam a = 0 := by
    exact fun a ↦ (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hnonneg i)).mp
      hzero a (Finset.mem_univ a)
  exact ⟨lam, E, F, hall, hE, hF, by simpa only [WithLp.ofLp_zero] using hrepr⟩

-- An empty ambient endpoint gives empty Schmidt support, without a Nonempty hypothesis.
example : ∃ (lam : EmptySupport → ℝ)
    (E : Matrix (Fin 0) EmptySupport ℂ)
    (F : Matrix Bool EmptySupport ℂ),
    (∀ a, 0 ≤ lam a) ∧
      (E.conjTranspose * E : Matrix EmptySupport EmptySupport ℂ) = 1 ∧
      F.conjTranspose * F = 1 ∧
      ambientSchmidtVector lam E F = 0 ∧ ∑ a, lam a = 0 := by
  simpa only [WithLp.ofLp_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
    exists_schmidtSourceFrames (0 : EuclideanSpace ℂ (Fin 0 × Bool))

-- The phase-bearing product vector has rank one although its support capacity is two.
example : Matrix.schmidtRank phaseKet.ofLp ≤ 1 := by
  classical
  have hrepr : phaseKet.ofLp =
      fun p : Bool × Fin 3 ↦ (if p.1 = false then Complex.I else 0) *
        (if p.2 = 1 then 1 else 0) := by
    funext p
    simp only [phaseKet, EuclideanSpace.single, PiLp.ofLp_single, Pi.single_apply]
    rcases p with ⟨l, r⟩
    fin_cases r <;> cases l <;> norm_num [Pi.single_apply]
  rw [hrepr]
  exact Matrix.schmidtRank_product_le_one
    (fun l : Bool ↦ if l = false then Complex.I else 0)
    (fun r : Fin 3 ↦ if r = 1 then 1 else 0)

-- Normalization follows from the actual Euclidean norm, not an assumed probability list.
example : ∃ (lam : KetSupport → ℝ)
    (E : Matrix Bool KetSupport ℂ)
    (F : Matrix (Fin 3) KetSupport ℂ),
    (∀ a, 0 ≤ lam a) ∧ ∑ a, lam a = 1 ∧ E.conjTranspose * E = 1 ∧
      F.conjTranspose * F = 1 ∧ ambientSchmidtVector lam E F = phaseKet.ofLp := by
  apply exists_probability_schmidtSourceFrames phaseKet
  simp only [phaseKet, EuclideanSpace.single, PiLp.norm_single, Complex.norm_I]

-- A subnormalized actual vector has its true squared mass, rather than an artificial mass one.
example : ∃ (lam : KetSupport → ℝ)
    (E : Matrix Bool KetSupport ℂ)
    (F : Matrix (Fin 3) KetSupport ℂ),
    (∀ a, 0 ≤ lam a) ∧ E.conjTranspose * E = 1 ∧ F.conjTranspose * F = 1 ∧
      ambientSchmidtVector lam E F =
        (EuclideanSpace.single (false, 1) (1 / 2 : ℂ)).ofLp ∧ ∑ a, lam a = 1 / 4 := by
  obtain ⟨lam, E, F, hnonneg, hE, hF, hrepr, hmass⟩ := exists_schmidtSourceFrames
    (EuclideanSpace.single (false, 1) (1 / 2 : ℂ) : EuclideanSpace ℂ (Bool × Fin 3))
  refine ⟨lam, E, F, hnonneg, hE, hF, hrepr, ?_⟩
  simpa only [EuclideanSpace.single, PiLp.norm_single, norm_div, norm_one,
    Complex.norm_ofNat, show (1 / (2 : ℝ)) ^ 2 = 1 / 4 by norm_num] using hmass

-- Both actual vectors determine the frames; the ket/bra supports and ambient spaces differ.
example : ∃ (lam : KetSupport → ℝ) (mu : BraSupport → ℝ)
    (E : Matrix Bool KetSupport ℂ)
    (F : Matrix (Fin 3) KetSupport ℂ)
    (Et : Matrix Unit BraSupport ℂ)
    (Ft : Matrix Bool BraSupport ℂ),
    (∀ a, 0 ≤ lam a) ∧ (∀ c, 0 ≤ mu c) ∧ ∑ a, lam a = 1 ∧ ∑ c, mu c = 1 ∧
      E.conjTranspose * E = 1 ∧ F.conjTranspose * F = 1 ∧
      Et.conjTranspose * Et = 1 ∧ Ft.conjTranspose * Ft = 1 ∧
      Integrable (ambientSampledSource 3 lam mu E F Et Ft)
        (law (Fin 3 × (KetSupport × BraSupport))) ∧
      (∫ x, ambientSampledSource 3 lam mu E F Et Ft x
        ∂law (Fin 3 × (KetSupport × BraSupport))) =
          Matrix.vecMulVec phaseKet.ofLp (fun q ↦ conj (phaseBra.ofLp q)) ∧
      (∫ x, ambientSampledSource 3 lam mu E F Et Ft x
        ∂law (Fin 3 × (KetSupport × BraSupport)))
          (false, 1) ((), true) = -1 := by
  obtain ⟨lam, mu, E, F, Et, Ft, hlam, hmu, hmass, hmass', hE, hF, hEt, hFt,
    _, hint, hmean⟩ := exists_schmidtSourceReplacement phaseKet phaseBra 3 (by decide)
  refine ⟨lam, mu, E, F, Et, Ft, hlam, hmu, ?_, ?_, hE, hF, hEt, hFt,
    hint, hmean, ?_⟩
  · simpa only [phaseKet, EuclideanSpace.single, PiLp.norm_single,
      Complex.norm_I, one_pow] using hmass
  · simpa only [phaseBra, EuclideanSpace.single, PiLp.norm_single,
      norm_neg, Complex.norm_I, one_pow] using hmass'
  · rw [hmean]
    norm_num [Matrix.vecMulVec_apply, phaseKet, phaseBra, EuclideanSpace.single,
      PiLp.ofLp_single, Pi.single_apply, Complex.I_mul_I]

-- Actual replacement remains well-defined and unbiased for an empty ket endpoint.
example : ∃ (lam : EmptySupport → ℝ) (mu : BraSupport → ℝ)
    (E : Matrix (Fin 0) EmptySupport ℂ)
    (F : Matrix Bool EmptySupport ℂ)
    (Et : Matrix Unit BraSupport ℂ)
    (Ft : Matrix Bool BraSupport ℂ),
    Integrable (ambientSampledSource 2 lam mu E F Et Ft)
      (law (Fin 2 × (EmptySupport × BraSupport))) ∧
      (∫ x, ambientSampledSource 2 lam mu E F Et Ft x
        ∂law (Fin 2 × (EmptySupport × BraSupport))) = 0 := by
  obtain ⟨lam, mu, E, F, Et, Ft, _, _, _, _, _, _, _, _, _, hint, hmean⟩ :=
    exists_schmidtSourceReplacement (0 : EuclideanSpace ℂ (Fin 0 × Bool))
      phaseBra 2 (by decide)
  refine ⟨lam, mu, E, F, Et, Ft, hint, ?_⟩
  rw [hmean]
  ext p q
  simp only [Matrix.vecMulVec_apply, WithLp.ofLp_zero, Pi.zero_apply,
    zero_mul, Matrix.zero_apply]

end
