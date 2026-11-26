/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.Permutation.MergeExponential
import QICLean.Spectral.Projection.ProjectionIntertwiner
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import QICLean.Analysis.TraceInequality.WeightedTraceHolder

/-!
# The compatible physical-label projection

On five independent finite factors Q, Y, V, C and R, the actual physical
label operator is `G = F_Q + F_V - F_Y`. The middle region Y is independent
of Q and V. On the projection P onto symmetry of the physical QYV copies,
complementary central labels give `G * P = P * (F_Q + F_V - F_QV)`.
The actual QV merge deficit is positive semidefinite, so the closed
nonnegative spectral projection of G fixes P.

Every real functional calculus of G commutes with the actual merged QC and
VR label observables, both auxiliary singleton label observables, and both
actual merge deficits. These identities
follow from nesting and disjointness of the specified copy actions. No
full-space positivity of G, invariance of P under a merge, density
invariance, normalization or supplied compatibility premise is used.

OpenAI, *A two-dimensional area law from a global spectral gap*
(September 24, 2026), `07-comparators.tex`, lines 501–522,
`comparator:merge-decomposition`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`; complementary central labels use
`05-replicas.tex`, Lemma 6.1(2), lines 168–181. The factors are indexed in
the order Q=0, Y=1, V=2, C=3, R=4. Zero copies and empty factors are included.
The actual excitation density and its physical symmetric support are
separate assertions, as is the complete metric comparison.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.

It also contains the following results.

* `TensorPower.re_trace_mul_exp_mergeDeficits_sub_physicalMergeDeficit_le`: five-factor trace Hölder
  for the actual merge deficits.
-/

open Matrix PermutationRepresentation

section CompatiblePhysicalLabel

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace TensorPower

section ComplementaryLabels

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (k : ℕ)

private theorem commute_labelObservables_of_subset_or_disjoint (A B : Finset F)
    (hAB : A ⊆ B ∨ Disjoint A B)
    (f g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k ι A) f)
      (labelObservable (subsystemPerm k ι B) g) := by
  unfold labelObservable
  refine Commute.sum_left _ _ _ fun l _ =>
    (Commute.sum_right _ _ _ fun l' _ =>
      (?_ : Commute (labelProj (subsystemPerm k ι A) l)
        (labelProj (subsystemPerm k ι B) l')).smul_right _).smul_left _
  exact hAB.elim
    (fun h => commute_labelProj_subsystemPerm_of_subset ι k h l l')
    (fun h => commute_labelProj_subsystemPerm_of_disjoint ι k h l l')

end ComplementaryLabels

section Physical

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (k : ℕ)

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition.
-/

/-- The actual physical label operator `F_Q + F_V - F_Y` on independent
factors Q, Y, V, C and R in that order. In particular, Y is not QV.
OpenAI, September 24, 2026, `07-comparators.tex`, lines 501–506. -/
noncomputable def physicalMergeDeficit : Matrix (Config k ι) (Config k ι) ℂ :=
  labelEntropy (subsystemPerm k ι {0}) + labelEntropy (subsystemPerm k ι {2}) -
    labelEntropy (subsystemPerm k ι {1})

private theorem commute_physicalMergeDeficit_labelObservable_of_subset_or_disjoint
    (B : Finset (Fin 5))
    (hQ : ({0} : Finset (Fin 5)) ⊆ B ∨ Disjoint ({0} : Finset (Fin 5)) B)
    (hV : ({2} : Finset (Fin 5)) ⊆ B ∨ Disjoint ({2} : Finset (Fin 5)) B)
    (hY : ({1} : Finset (Fin 5)) ⊆ B ∨ Disjoint ({1} : Finset (Fin 5)) B)
    (g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (physicalMergeDeficit ι k) (labelObservable (subsystemPerm k ι B) g) := by
  exact ((commute_labelObservables_of_subset_or_disjoint
    ι k {0} B hQ (fun l => Real.log l.dim) g).add_left
    (commute_labelObservables_of_subset_or_disjoint
      ι k {2} B hV (fun l => Real.log l.dim) g)).sub_left
    (commute_labelObservables_of_subset_or_disjoint ι k {1} B hY (fun l => Real.log l.dim) g)

private theorem posSemidef_qvMergeDeficit :
    (labelEntropy (subsystemPerm k ι {0}) + labelEntropy (subsystemPerm k ι {2}) -
      labelEntropy (subsystemPerm k ι {0, 2})).PosSemidef := by
  refine posSemidef_mergeDeficit
    (commute_subsystemPerm_of_disjoint k ι
      (show Disjoint ({0} : Finset (Fin 5)) {2} from by decide)) ?_
  simpa only [Finset.singleton_union] using
    (subsystemPerm_union k ι (show Disjoint ({0} : Finset (Fin 5)) {2} from by decide))

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition.
-/

/-- On the actual physical symmetric projection, the physical operator
intertwines with the actual QV merge deficit. Complementary central labels
and all needed commutations are derived from the specified copy actions.
OpenAI, September 24, 2026, `07-comparators.tex`, lines 515–522, and
`05-replicas.tex`, Lemma 6.1(2), lines 168–181. -/
theorem physicalMergeDeficit_mul_symProj :
    physicalMergeDeficit ι k * symProj (subsystemPerm k ι {0, 1, 2}) =
      symProj (subsystemPerm k ι {0, 1, 2}) *
        (labelEntropy (subsystemPerm k ι {0}) + labelEntropy (subsystemPerm k ι {2}) -
          labelEntropy (subsystemPerm k ι {0, 2})) := by
  have hY := labelEntropy_mul_symProj_union ι k ({1} : Finset (Fin 5)) {0, 2}
    (by decide)
  simp only [show (({1} : Finset (Fin 5)) ∪ {0, 2}) = {0, 1, 2} from by decide] at hY
  have h : ∀ A : Finset (Fin 5), A ⊆ ({0, 1, 2} : Finset (Fin 5)) →
      Commute (labelEntropy (subsystemPerm k ι A)) (symProj (subsystemPerm k ι {0, 1, 2})) :=
    fun A hA => commute_labelObservable_symProj_of_subset ι k A {0, 1, 2} hA
      (fun l => Real.log l.dim)
  have hD := ((h {0} (by decide)).add_left (h {2} (by decide))).sub_left
    (h {0, 2} (by decide))
  rw [← hD.eq, physicalMergeDeficit, Matrix.sub_mul, Matrix.sub_mul, hY]

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition.
-/

/-- The closed nonnegative spectral projection of the actual physical
operator fixes the physical symmetric projection. Positivity is derived
for the QV merge deficit and transferred through the actual intertwining.
OpenAI, September 24, 2026, `07-comparators.tex`, lines 515–522. -/
theorem spectralProjectionGE_physicalMergeDeficit_mul_symProj :
    spectralProjectionGE (physicalMergeDeficit ι k) 0 *
      symProj (subsystemPerm k ι {0, 1, 2}) = symProj (subsystemPerm k ι {0, 1, 2}) := by
  exact Matrix.spectralProjectionGE_zero_mul_of_intertwine
    (A := physicalMergeDeficit ι k)
    (((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _))
    (posSemidef_qvMergeDeficit ι k) _ (physicalMergeDeficit_mul_symProj ι k)

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition.
-/

/-- Every real functional calculus of the actual physical label operator
commutes with the actual QC, VR, C and R real label observables, whose
coefficients are chosen independently. Central-label commutations follow
from literal nesting and disjointness.
OpenAI, September 24, 2026, `07-comparators.tex`, lines 501–522. -/
theorem commute_cfc_physicalMergeDeficit_labelObservables (f : ℝ → ℝ)
    (gQC gVR gC gR : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (cfc f (physicalMergeDeficit ι k))
      (labelObservable (subsystemPerm k ι {0, 3}) gQC) ∧
    Commute (cfc f (physicalMergeDeficit ι k))
      (labelObservable (subsystemPerm k ι {2, 4}) gVR) ∧
    Commute (cfc f (physicalMergeDeficit ι k))
      (labelObservable (subsystemPerm k ι {3}) gC) ∧
    Commute (cfc f (physicalMergeDeficit ι k))
      (labelObservable (subsystemPerm k ι {4}) gR) := by
  exact ⟨(commute_physicalMergeDeficit_labelObservable_of_subset_or_disjoint ι k {0, 3}
    (Or.inl (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) gQC).cfc_real f,
    (commute_physicalMergeDeficit_labelObservable_of_subset_or_disjoint ι k {2, 4}
      (Or.inr (by decide)) (Or.inl (by decide)) (Or.inr (by decide)) gVR).cfc_real f,
    (commute_physicalMergeDeficit_labelObservable_of_subset_or_disjoint ι k {3}
      (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) gC).cfc_real f,
    (commute_physicalMergeDeficit_labelObservable_of_subset_or_disjoint ι k {4}
      (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)) gR).cfc_real f⟩

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-decomposition.
-/

/-- Every real functional calculus of the actual physical label operator
commutes with the two actual merge deficits, including its closed
nonnegative spectral projection. Singleton and merged-label commutations
are derived internally from the five specified factors.
OpenAI, September 24, 2026, `07-comparators.tex`, lines 501–522. -/
theorem commute_cfc_physicalMergeDeficit_mergeDeficits (f : ℝ → ℝ) :
    Commute (cfc f (physicalMergeDeficit ι k))
      (labelEntropy (subsystemPerm k ι {0}) + labelEntropy (subsystemPerm k ι {3}) -
        labelEntropy (subsystemPerm k ι {0, 3})) ∧
    Commute (cfc f (physicalMergeDeficit ι k))
      (labelEntropy (subsystemPerm k ι {2}) + labelEntropy (subsystemPerm k ι {4}) -
        labelEntropy (subsystemPerm k ι {2, 4})) := by
  have h (B : Finset (Fin 5))
      (hQ : ({0} : Finset (Fin 5)) ⊆ B ∨ Disjoint ({0} : Finset (Fin 5)) B)
      (hV : ({2} : Finset (Fin 5)) ⊆ B ∨ Disjoint ({2} : Finset (Fin 5)) B)
      (hY : ({1} : Finset (Fin 5)) ⊆ B ∨ Disjoint ({1} : Finset (Fin 5)) B) :
      Commute (cfc f (physicalMergeDeficit ι k)) (labelEntropy (subsystemPerm k ι B)) :=
    (commute_physicalMergeDeficit_labelObservable_of_subset_or_disjoint
      ι k B hQ hV hY (fun l => Real.log l.dim)).cfc_real f
  exact ⟨((h {0} (Or.inl (by decide)) (Or.inr (by decide)) (Or.inr (by decide))).add_right
    (h {3} (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)))).sub_right
    (h {0, 3} (Or.inl (by decide)) (Or.inr (by decide)) (Or.inr (by decide))),
    ((h {2} (Or.inr (by decide)) (Or.inl (by decide)) (Or.inr (by decide))).add_right
      (h {4} (Or.inr (by decide)) (Or.inr (by decide)) (Or.inr (by decide)))).sub_right
      (h {2, 4} (Or.inr (by decide)) (Or.inl (by decide)) (Or.inr (by decide)))⟩

end Physical

end TensorPower

end CompatiblePhysicalLabel

section PhysicalMergeHolder

/-!
## Five-factor trace Hölder for the actual merge deficits

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

end PhysicalMergeHolder
