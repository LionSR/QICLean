/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.MergeExponential
import QICLean.Representation.SchurLabelCommutation
import QICLean.Analysis.SpectralProjectionIntertwiner

/-!
# Nonnegative combined labels on simultaneous symmetric copies

The five coordinate factors are Q, Y, V, C and R, in that order. On the
subspace fixed by simultaneous permutations of all five factors, the label
of Y agrees with that of QCVR. The logarithmic merge dimension inequality
for the disjoint factors QC and VR therefore gives nonnegative spectral
support for F_QC + F_VR - F_Y on this simultaneous symmetric subspace.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `07-comparators.tex`, lines 439–456 and 481–485, at manuscript
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* The complementary-label and merge dimension identities are Lemma 6.1(2–3),
  `05-replicas.tex`, lines 102–115.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped Matrix ComplexOrder

namespace TensorPower

/-- The closed spectral-support identity on the simultaneous symmetric
subspace of all five factors, including zero copies and empty coordinate
factors. OpenAI, `07-comparators.tex`, lines 481–485. -/
theorem spectralProjectionGE_mergedLabel_mul_symProj
    (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (r : ℕ) :
    spectralProjectionGE
      (labelEntropy (subsystemPerm r ι {0, 3}) +
        labelEntropy (subsystemPerm r ι {2, 4}) -
        labelEntropy (subsystemPerm r ι {1})) 0 *
      symProj (copyPerm ((f : Fin 5) → ι f) r) =
        symProj (copyPerm ((f : Fin 5) → ι f) r) := by
  classical
  let P := symProj (copyPerm ((f : Fin 5) → ι f) r)
  let D := labelEntropy (subsystemPerm r ι {0, 3}) +
    labelEntropy (subsystemPerm r ι {2, 4}) -
    labelEntropy (subsystemPerm r ι ({1} : Finset (Fin 5))ᶜ)
  have hDisjoint : Disjoint ({0, 3} : Finset (Fin 5)) {2, 4} := by decide
  have hUnion : ({0, 3} : Finset (Fin 5)) ∪ {2, 4} = {1}ᶜ := by decide
  have hD : D.PosSemidef :=
    posSemidef_mergeDeficit
      (φQ := subsystemPerm r ι {0, 3})
      (φE := subsystemPerm r ι {2, 4})
      (φQE := subsystemPerm r ι ({1} : Finset (Fin 5))ᶜ)
      (commute_subsystemPerm_of_disjoint r ι hDisjoint)
      (fun σ => by simpa only [hUnion] using subsystemPerm_union r ι hDisjoint σ)
  have hComplement : labelEntropy (subsystemPerm r ι {1}) * P =
      labelEntropy (subsystemPerm r ι ({1} : Finset (Fin 5))ᶜ) * P := by
    dsimp [P]
    simp_rw [labelEntropy, labelObservable, Finset.sum_mul, smul_mul_assoc,
      labelProj_mul_symProj_compl ι r {1}]
  have hCommute : Commute D P := by
    have hAll (A : Finset (Fin 5)) :
        Commute (labelEntropy (subsystemPerm r ι A)) P := by
      dsimp [P, labelEntropy, labelObservable, symProj]
      refine Commute.sum_left _ _ _ fun l _ => ?_
      refine ((Commute.sum_right _ _ _ fun σ _ => ?_).smul_left _).smul_right _
      simpa only [labelProj, groupAlgebraRep_single, one_smul, subsystemPerm_univ] using
        commute_groupAlgebraRep_subsystemPerm_of_subset ι r (Finset.subset_univ A)
          (IrrepLabel.centralIdem_mem_center l) (MonoidAlgebra.single σ (1 : ℂ))
    exact ((hAll {0, 3}).add_left (hAll {2, 4})).sub_left (hAll {1}ᶜ)
  apply spectralProjectionGE_zero_mul_of_intertwine
    (((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)) hD P
  rw [← hCommute.eq]
  dsimp [D]
  simpa only [labelEntropy, sub_mul, add_mul] using congrArg
    (fun M => labelEntropy (subsystemPerm r ι {0, 3}) * P +
      labelEntropy (subsystemPerm r ι {2, 4}) * P - M) hComplement

end TensorPower
