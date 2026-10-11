/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaSimilarity

/-!
# Central observables of nested subsystems after restricting the copy action

Restrict both subsystem actions along the same homomorphism of copy
permutation groups. Central label observables still commute when one
subsystem contains the other or the subsystems are disjoint. The
homomorphism need not be injective, and the local spaces may be empty.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 6.1(2), `05-replicas.tex`, lines 101–103,
and `07-comparators.tex`, lines 481–508, `comparator:good-auxiliary`
and `comparator:merge-decomposition`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation

namespace TensorPower

local instance subsystemLabelCommutation_decidableEqConfig
    {V : Type*} [Fintype V] [DecidableEq V] (ι : V → Type*)
    [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)] (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- Central label observables of nested or disjoint subsystems commute
under the same restricted copy action. No injectivity of the restriction
or nonempty local-space hypothesis is needed.

Source: area-law manuscript, Lemma 6.1(2), `05-replicas.tex`, lines 101–103;
its restriction to good copies is used in `07-comparators.tex`, lines 481–508. -/
theorem commute_subgroup_labelObservables_of_subset_or_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
    {m k : ℕ} (θ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin k))
    (S T : Finset V) (hST : S ⊆ T ∨ Disjoint S T)
    (f g : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    Commute (labelObservable ((subsystemPerm k ι S).comp θ) f)
      (labelObservable ((subsystemPerm k ι T).comp θ) g) := by
  rcases hST with hST | hST
  · rw [labelObservable_eq_groupAlgebraRep, labelObservable_eq_groupAlgebraRep]
    apply commute_groupAlgebraRep_of_eq_mul
      ((subsystemPerm k ι S).comp θ) ((subsystemPerm k ι (T \ S)).comp θ)
      ((subsystemPerm k ι T).comp θ) _ _ (sum_smul_centralIdem_mem_center f)
    · intro σ
      change subsystemPerm k ι T (θ σ) = _
      conv_lhs => rw [← Finset.union_sdiff_of_subset hST]
      exact subsystemPerm_union k ι Finset.disjoint_sdiff (θ σ)
    · exact fun σ τ => commute_subsystemPerm_of_disjoint k ι
        Finset.disjoint_sdiff (θ σ) (θ τ)
  · exact commute_labelObservable_of_commute _ _
      (fun σ τ => commute_subsystemPerm_of_disjoint k ι hST (θ σ) (θ τ)) f g

end TensorPower
