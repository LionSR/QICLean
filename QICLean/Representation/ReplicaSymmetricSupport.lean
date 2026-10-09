/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.MergeExponential
import QICLean.Analysis.SpectralProjectionIntertwiner

/-!
# Nonnegative label support for a partition of arbitrary finite factors

The conclusion concerns simultaneous symmetry of all coordinate factors.
It requires neither nonempty coordinate factors nor a cutoff or a vector.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
`05-replicas.tex`, Lemma 6.1(2–3), lines 99–115.
-/

set_option relaxedAutoImplicit false

open scoped ComplexOrder

open Matrix PermutationRepresentation

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
  (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]

/-- For a disjoint cover of all one-copy factors, the logarithmic label
deficit has nonnegative spectral support on simultaneous symmetric copies.
OpenAI, `05-replicas.tex`, Lemma 6.1(2–3), lines 99–115.
-/
theorem spectralProjectionGE_labelDeficit_mul_symProj_of_partition
    (k : ℕ) (P Y F : Finset V)
    (hPY : Disjoint P Y) (hPF : Disjoint P F) (hYF : Disjoint Y F)
    (hcover : P ∪ Y ∪ F = Finset.univ) :
    spectralProjectionGE
      (labelEntropy (subsystemPerm k ι P) +
        labelEntropy (subsystemPerm k ι F) -
        labelEntropy (subsystemPerm k ι Y)) 0 *
      symProj (copyPerm ((v : V) → ι v) k) =
        symProj (copyPerm ((v : V) → ι v) k) := by
  let D := labelEntropy (subsystemPerm k ι P) +
    labelEntropy (subsystemPerm k ι F) -
    labelEntropy (subsystemPerm k ι (P ∪ F))
  have hD : D.PosSemidef := posSemidef_mergeDeficit
    (commute_subsystemPerm_of_disjoint k ι hPF) (subsystemPerm_union k ι hPF)
  have hY_PF : Disjoint Y (P ∪ F) :=
    Finset.disjoint_union_right.mpr ⟨hPY.symm, hYF⟩
  have hfull : Y ∪ (P ∪ F) = Finset.univ := by
    simpa only [Finset.union_assoc, Finset.union_left_comm Y P F] using hcover
  have hYS := labelEntropy_mul_symProj_union ι k Y (P ∪ F) hY_PF
  rw [hfull, subsystemPerm_univ k ι] at hYS
  have hcomm : ∀ A : Finset V,
      Commute (labelEntropy (subsystemPerm k ι A))
        (symProj (copyPerm ((v : V) → ι v) k)) := fun A => by
    simpa only [subsystemPerm_univ k ι, labelEntropy] using
      commute_labelObservable_symProj_of_subset ι k A Finset.univ
        (Finset.subset_univ A) (fun l => Real.log l.dim)
  have hDS : Commute D (symProj (copyPerm ((v : V) → ι v) k)) :=
    ((hcomm P).add_left (hcomm F)).sub_left (hcomm (P ∪ F))
  have hHS :
      (labelEntropy (subsystemPerm k ι P) + labelEntropy (subsystemPerm k ι F) -
        labelEntropy (subsystemPerm k ι Y)) * symProj (copyPerm ((v : V) → ι v) k) =
      symProj (copyPerm ((v : V) → ι v) k) * D := by
    simpa only [D, Matrix.sub_mul, hYS] using hDS.eq
  exact Matrix.spectralProjectionGE_zero_mul_of_intertwine
    (((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)) hD _ hHS

end TensorPower
