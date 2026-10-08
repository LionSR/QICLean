/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.CompatiblePhysicalLabel
import QICLean.Analysis.WeightedTraceHolder

/-!
# Five-factor trace Hölder for the actual merge deficits

Let Q, Y, V, C and R be independent finite factors, indexed in that order.
The copy actions on the indicated factors define the actual label observables
F_Q, F_Y, F_V, F_C, F_R, F_QC and F_VR. Put
`D_C = F_Q + F_C - F_QC`, `D_R = F_V + F_R - F_VR` and
`G = F_Q + F_V - F_Y`.

For an arbitrary positive semidefinite matrix ρ and real a, five-factor trace
Hölder bounds the exponential moment of a(D_C + D_R - G) by the product
of the five separate moments at 5a, each raised to the power 1/5. All
Hermiticity and commutation facts are derived from the actual nested or
disjoint subsystem copy actions. The trace weight need not be normalized or
commute with these observables. Zero copies and empty factors are included.

This is the analytic step in OpenAI, *A two-dimensional area law from a global
spectral gap*, September 24, 2026, `07-comparators.tex`, lines 556–560, with
the actual operators defined at lines 501–506, immutable revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Nested and disjoint central-label
commutation is Lemma 6.1(2) in `05-replicas.tex`, lines 101–102, 172–176.
The region Y remains independent of Q and V. No global positivity of G,
physical symmetric support, preservation of that support under a merge,
component-density identification, moment rate or inverse estimate is asserted.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix PermutationRepresentation
open scoped BigOperators ComplexOrder Matrix.Norms.Operator
namespace TensorPower

private theorem commute_labelObservables_laminar
    {F : Type*} [Fintype F] [DecidableEq F]
    (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (m : ℕ) (A B : Finset F) (h : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B)
    (f g : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    Commute (labelObservable (subsystemPerm m ι A) f)
      (labelObservable (subsystemPerm m ι B) g) := by
  unfold labelObservable
  refine Commute.sum_left _ _ _ fun l _ =>
    (Commute.sum_right _ _ _ fun l' _ =>
      (?_ : Commute (labelProj (subsystemPerm m ι A) l)
        (labelProj (subsystemPerm m ι B) l')).smul_right _).smul_left _
  exact h.elim
    (fun h => commute_labelProj_subsystemPerm_of_subset ι m h l l')
    (fun h => h.elim
      (fun h => (commute_labelProj_subsystemPerm_of_subset ι m h l' l).symm)
      (fun h => commute_labelProj_subsystemPerm_of_disjoint ι m h l l'))

private def labelSets : Fin 7 → Finset (Fin 5) :=
  ![{0}, {1}, {2}, {3}, {4}, {0, 3}, {2, 4}]

private def signedFive {M : Type*} [Add M] [Sub M] [Neg M] (B : Fin 7 → M) : Fin 5 → M :=
  ![B 0 + B 3 - B 5, B 2 + B 4 - B 6, -B 0, -B 2, B 1]

private theorem commute_signedFive {n : Type*} [Fintype n]
    (B : Fin 7 → Matrix n n ℂ) (h : ∀ i j, Commute (B i) (B j)) (i j : Fin 5) :
    Commute (signedFive B i) (signedFive B j) := by
  have hrow (i : Fin 5) (j : Fin 7) : Commute (signedFive B i) (B j) := by
    fin_cases i
    · exact ((h 0 j).add_left (h 3 j)).sub_left (h 5 j)
    · exact ((h 2 j).add_left (h 4 j)).sub_left (h 6 j)
    · exact (h 0 j).neg_left
    · exact (h 2 j).neg_left
    · exact h 1 j
  fin_cases j
  · exact ((hrow i 0).add_right (hrow i 3)).sub_right (hrow i 5)
  · exact ((hrow i 2).add_right (hrow i 4)).sub_right (hrow i 6)
  · exact (hrow i 0).neg_right
  · exact (hrow i 2).neg_right
  · exact hrow i 1

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (m : ℕ)

private theorem commute_seven_labels (i j : Fin 7) :
    Commute (labelEntropy (subsystemPerm m ι (labelSets i)))
      (labelEntropy (subsystemPerm m ι (labelSets j))) := by
  apply commute_labelObservables_laminar
  exact (by decide : ∀ i j : Fin 7,
    labelSets i ⊆ labelSets j ∨ labelSets j ⊆ labelSets i ∨
      Disjoint (labelSets i) (labelSets j)) i j

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, 07-comparators.tex, lines 501–506 and 556–560.
Labels: comparator:merge-decomposition, comparator:component-inverse.
Source revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

/-- Five-factor trace Hölder for the actual QC and VR merge deficits and the
physical expression `F_Q + F_V - F_Y`, where Y is an independent factor.
The positive semidefinite trace weight is arbitrary; its normalization and
commutation are not hypotheses. All five signed operators commute by their
actual nested or disjoint copy actions. OpenAI, September 24, 2026,
`07-comparators.tex`, lines 556–560, with definitions at lines 501–506. -/
theorem re_trace_mul_exp_mergeDeficits_sub_physicalMergeDeficit_le
    {ρ : Matrix (Config m ι) (Config m ι) ℂ} (hρ : ρ.PosSemidef) (a : ℝ) :
    let F := fun A => labelEntropy (subsystemPerm m ι A)
    let DC := F {0} + F {3} - F {0, 3}
    let DR := F {2} + F {4} - F {2, 4}
    (ρ * NormedSpace.exp ((a : ℂ) • (DC + DR - physicalMergeDeficit ι m))).trace.re ≤
      (ρ * NormedSpace.exp (((5 * a : ℝ) : ℂ) • DC)).trace.re ^ (1 / 5 : ℝ) *
      (ρ * NormedSpace.exp (((5 * a : ℝ) : ℂ) • DR)).trace.re ^ (1 / 5 : ℝ) *
      (ρ * NormedSpace.exp (((-5 * a : ℝ) : ℂ) • F {0})).trace.re ^ (1 / 5 : ℝ) *
      (ρ * NormedSpace.exp (((-5 * a : ℝ) : ℂ) • F {2})).trace.re ^ (1 / 5 : ℝ) *
      (ρ * NormedSpace.exp (((5 * a : ℝ) : ℂ) • F {1})).trace.re ^ (1 / 5 : ℝ) := by
  dsimp only
  let B := fun j => labelEntropy (subsystemPerm m ι (labelSets j))
  have hB (i : Fin 7) : (B i).IsHermitian := isHermitian_labelObservable _ _
  have hA (i : Fin 5) : (signedFive B i).IsHermitian := by
    fin_cases i
    · exact ((hB 0).add (hB 3)).sub (hB 5)
    · exact ((hB 2).add (hB 4)).sub (hB 6)
    · exact (hB 0).neg
    · exact (hB 2).neg
    · exact hB 1
  have hsum : ∑ i, signedFive B i =
      (B 0 + B 3 - B 5) + (B 2 + B 4 - B 6) - (B 0 + B 2 - B 1) := by
    simp [Fin.sum_univ_succ, signedFive]
    abel
  have h := hρ.re_trace_mul_exp_sum_le_prod 4 (signedFive B) hA
    (commute_signedFive B (commute_seven_labels ι m)) a
  rw [hsum] at h
  simpa [Fin.prod_univ_succ, signedFive, B, labelSets, physicalMergeDeficit,
    neg_mul, Complex.ofReal_neg, smul_neg, neg_smul, mul_assoc] using h

end TensorPower
