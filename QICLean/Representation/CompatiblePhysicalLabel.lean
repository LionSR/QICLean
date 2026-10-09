/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchurLabelCommutation
import QICLean.Representation.MergeExponential
import QICLean.Analysis.SpectralProjectionIntertwiner
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

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
-/

open Matrix PermutationRepresentation
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
