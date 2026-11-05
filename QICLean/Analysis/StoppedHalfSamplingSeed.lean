/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.StoppedHalfSamplingIteration

/-!
# Finite seeds for the stopped half-sampling iteration

A prescribed finite sequence supplies all rounds of the existing stopped
iteration. Coordinates after the prescribed rounds are the identity.
The current input is unchanged when its own next seed is varied.
This supports ALVV, arXiv:1602.08828v2, the resampling description,
lines 749–755. It asserts no sampling-success estimate.
-/

open MeasureTheory

noncomputable section
namespace Entropy

/-- Extend a finite prescribed seed sequence by the identity. This is the
finite-seed realization of the stopped iteration used for ALVV,
arXiv:1602.08828v2, lines 749–755. -/
def halfSamplingSeedSequence {d R : ℕ}
    (U : Fin R → Matrix.rankUnitaryProduct d) (j : ℕ) : Matrix.rankUnitaryProduct d :=
  if h : j < R then U ⟨j, h⟩ else 1

/-- Extending the finite seed sequence is Borel. Auxiliary for ALVV,
arXiv:1602.08828v2, lines 749–755. -/
theorem measurable_halfSamplingSeedSequence (d R : ℕ) :
    Measurable (halfSamplingSeedSequence (d := d) (R := R)) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j < R
  · simpa only [halfSamplingSeedSequence, dite_eq_left h] using measurable_pi_apply (⟨j, h⟩ : Fin R)
  · simpa only [halfSamplingSeedSequence, dite_eq_right h] using
      (measurable_const : Measurable (fun _ : Fin R → Matrix.rankUnitaryProduct d ↦
        (1 : Matrix.rankUnitaryProduct d)))

/-- Replacing the next seed leaves every earlier prescribed seed unchanged.
Auxiliary for ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem halfSamplingSeedSequence_update_of_lt {d R : ℕ}
    (U : Fin R → Matrix.rankUnitaryProduct d) (i : Fin R)
    (u : Matrix.rankUnitaryProduct d) (j : ℕ) (hj : j < i.val) :
    halfSamplingSeedSequence (Function.update U i u) j = halfSamplingSeedSequence U j := by
  have hjR : j < R := hj.trans i.isLt
  simp only [halfSamplingSeedSequence, dite_eq_left hjR]
  have hji : (⟨j, hjR⟩ : Fin R) ≠ i := by
    intro h
    exact (Nat.ne_of_lt hj) (congrArg Fin.val h)
  exact Function.update_of_ne hji _ _

/-- The prescribed coordinate at the updated round is the new seed.
Auxiliary for ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem halfSamplingSeedSequence_update_self {d R : ℕ}
    (U : Fin R → Matrix.rankUnitaryProduct d) (i : Fin R)
    (u : Matrix.rankUnitaryProduct d) :
    halfSamplingSeedSequence (Function.update U i u) i.val = u := by
  simp only [halfSamplingSeedSequence, dite_eq_left i.isLt, Function.update_self]

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {n : V → ℕ} {d R : ℕ}

/-- The actual matrix at a prescribed round is Borel in the finite seed.
Auxiliary for ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem measurable_canonicalHalfSampleTrimIterate_finite_seed
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ) (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (j : ℕ) :
    Measurable (fun U : Fin R → Matrix.rankUnitaryProduct d ↦
      canonicalHalfSampleTrimIterate e cuts xi k D threshold F P
        (halfSamplingSeedSequence U) j) :=
  (measurable_canonicalHalfSampleTrimIterate e cuts xi k D threshold F j).comp
    (measurable_const.prodMk (measurable_halfSamplingSeedSequence d R))

/-- Replacing the round's own seed leaves its actual input unchanged.
Auxiliary for ALVV, arXiv:1602.08828v2, lines 749–755. -/
theorem canonicalHalfSampleTrimIterate_update_input
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ) (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (U : Fin R → Matrix.rankUnitaryProduct d)
    (i : Fin R) (u : Matrix.rankUnitaryProduct d) :
    canonicalHalfSampleTrimIterate e cuts xi k D threshold F P
      (halfSamplingSeedSequence (Function.update U i u)) i.val =
    canonicalHalfSampleTrimIterate e cuts xi k D threshold F P
      (halfSamplingSeedSequence U) i.val :=
  canonicalHalfSampleTrimIterate_eq_of_seed_prefix e cuts xi k D threshold F P _ _ i.val
    (halfSamplingSeedSequence_update_of_lt U i u)

/-- At the next round, replacing its seed gives precisely the actual
one-step operation on the fixed previous input. Auxiliary for ALVV,
arXiv:1602.08828v2, lines 749–755. -/
theorem canonicalHalfSampleTrimIterate_update_next
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ) (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (U : Fin R → Matrix.rankUnitaryProduct d)
    (i : Fin R) (u : Matrix.rankUnitaryProduct d) :
    canonicalHalfSampleTrimIterate e cuts xi k D threshold F P
      (halfSamplingSeedSequence (Function.update U i u)) (i.val + 1) =
    canonicalHalfSampleTrimMatrix e cuts xi k D threshold F
      (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P
        (halfSamplingSeedSequence U) i.val) u := by
  change canonicalHalfSampleTrimMatrix e cuts xi k D threshold F
    (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P
      (halfSamplingSeedSequence (Function.update U i u)) i.val)
    (halfSamplingSeedSequence (Function.update U i u) i.val) = _
  rw [canonicalHalfSampleTrimIterate_update_input,
    halfSamplingSeedSequence_update_self]

end Entropy
