/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.YoungSubgroup.GroupedCopies
import QICLean.Representation.Permutation.MergeExponential
import QICLean.ManyBody.Replica.Metric.Similarity
import QICLean.Representation.Permutation.TrivialLabel
import QICLean.Spectral.Projection.ProjectionIntertwiner

/-!
# Signed subgroup labels on the simultaneous symmetric subspace

For three disjoint subsystems covering the whole space, the signed label
operator of any permutation subgroup is nonnegative on the simultaneous
symmetric subspace of that subgroup. Complementary labels replace the
negative middle label by the label of the union of the other two regions;
the resulting merge deficit is positive semidefinite.

Copy actions belonging to the two disjoint groups of copies commute even
when their physical subsystems overlap. Thus every good-copy label
observable preserves the bad-copy simultaneous symmetric subspace.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 454--480,
`comparator:whole-inverse`; complementary labels are Lemma 6.1(2) in
`05-replicas.tex`, lines 168--181, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

It also contains the following results.

* `TensorPower.subsystemLabelCommutation_decidableEqConfig`,
  `TensorPower.commute_subgroup_labelObservables_of_subset_or_disjoint`: central observables of
  nested subsystems after restricting the copy action.
* `TensorPower.spectralProjectionGE_labelDeficit_mul_symProj_of_partition`: nonnegative label
  support for a partition of arbitrary finite factors.
-/

section GroupedLabelSymmetricSupport

noncomputable section
open Matrix PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace PermutationRepresentation

/-- Complementary label entropies agree after simultaneous symmetrization.
Source: `05-replicas.tex`, Lemma 6.1(2), lines 168--181. -/
theorem labelEntropy_mul_symProj_of_eq_mul
    {r : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (φ χ ψ : Equiv.Perm (Fin r) →* Equiv.Perm X)
    (hψ : ∀ σ, ψ σ = φ σ * χ σ) :
    labelEntropy φ * symProj ψ = labelEntropy χ * symProj ψ := by
  have hlabel (ell : IrrepLabel (Equiv.Perm (Fin r))) :
      labelProj φ ell * symProj ψ = labelProj χ ell * symProj ψ := by
    ext x y
    have h := groupAlgebraRep_mulVec_eq_of_eq_mul φ χ ψ hψ
      (a := IrrepLabel.centralIdem ell)
      (IrrepLabel.coeff_inv_of_mem_center (IrrepLabel.centralIdem_mem_center ell))
      (symProj_mulVec_mem ψ (Pi.single y 1))
    simp only [mulVec_single_one] at h
    exact congrFun h x
  simp_rw [labelEntropy, labelObservable, Finset.sum_mul, smul_mul_assoc, hlabel]

end PermutationRepresentation

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]

local instance groupedLabelSymmetricSupport_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

omit [Fintype V] [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)] in
/-- Commuting permutations of copies induce commuting actions on arbitrary
subsystems, including overlapping subsystems. Source: `07-comparators.tex`,
lines 454--480. -/
theorem commute_subsystemPerm_of_commute (k : ℕ) (S T : Finset V)
    {σ τ : Equiv.Perm (Fin k)} (hστ : Commute σ τ) :
    Commute (subsystemPerm k ι S σ) (subsystemPerm k ι T τ) := by
  ext x j v
  simp only [Equiv.Perm.mul_apply, subsystemPerm_apply]
  by_cases hS : v ∈ S <;> by_cases hT : v ∈ T <;>
    simp only [hS, hT, ite_true, ite_false]
  exact congrArg (fun i => x i v)
    (congrArg (fun π : Equiv.Perm (Fin k) => π j) hστ.inv_inv.eq).symm

/-- A central subgroup observable on a smaller subsystem commutes with the
simultaneous symmetric projection on a larger subsystem.
Source: `05-replicas.tex`, Lemma 6.1(2), and `07-comparators.tex`, lines 454--480. -/
theorem commute_subgroup_labelObservable_symProj_of_subset
    {r k : ℕ} (θ : Equiv.Perm (Fin r) →* Equiv.Perm (Fin k))
    (S T : Finset V) (hST : S ⊆ T)
    (f : IrrepLabel (Equiv.Perm (Fin r)) → ℝ) :
    Commute (labelObservable ((subsystemPerm k ι S).comp θ) f)
      (symProj ((subsystemPerm k ι T).comp θ)) := by
  unfold labelObservable symProj
  refine Commute.sum_left _ _ _ fun ell _ => ?_
  refine ((Commute.sum_right _ _ _ (fun σ _ => ?_)).smul_left _).smul_right _
  simpa only [labelProj, groupAlgebraRep_single, one_smul] using
    commute_groupAlgebraRep_of_eq_mul
      ((subsystemPerm k ι S).comp θ) ((subsystemPerm k ι (T \ S)).comp θ)
      ((subsystemPerm k ι T).comp θ)
      (fun τ => by
        change subsystemPerm k ι T (θ τ) = _
        conv_lhs => rw [← Finset.union_sdiff_of_subset hST]
        exact subsystemPerm_union k ι Finset.disjoint_sdiff (θ τ))
      (fun σ τ => commute_subsystemPerm_of_disjoint k ι
        Finset.disjoint_sdiff (θ σ) (θ τ))
      (IrrepLabel.centralIdem_mem_center ell) (MonoidAlgebra.single σ (1 : ℂ))

/-- The signed subgroup label operator is nonnegative on its actual
simultaneous symmetric subspace. Ambient positivity is not asserted.
Source: `07-comparators.tex`, lines 454--480. -/
theorem subgroup_signedLabelEntropy_symProj_nonneg
    {r k : ℕ} (θ : Equiv.Perm (Fin r) →* Equiv.Perm (Fin k))
    (P Y F : Finset V) (hPY : Disjoint P Y) (hPF : Disjoint P F)
    (hYF : Disjoint Y F) (hcover : Y ∪ (P ∪ F) = Finset.univ) :
    let L := fun S => labelEntropy ((subsystemPerm k ι S).comp θ)
    let Q := symProj ((subsystemPerm k ι Finset.univ).comp θ)
    let G := L P + L F - L Y
    Commute G Q ∧ 0 ≤ Q * G * Q := by
  intro L Q G
  have hc (S : Finset V) : Commute (L S) Q :=
    commute_subgroup_labelObservable_symProj_of_subset ι θ S Finset.univ
      (Finset.subset_univ S) (fun ell => Real.log ell.dim)
  have hGQ : Commute G Q := ((hc P).add_left (hc F)).sub_left (hc Y)
  have hYPF : Disjoint Y (P ∪ F) := Finset.disjoint_union_right.mpr ⟨hPY.symm, hYF⟩
  have hY : L Y * Q = L (P ∪ F) * Q := by
    apply labelEntropy_mul_symProj_of_eq_mul
    intro σ
    change subsystemPerm k ι Finset.univ (θ σ) = _
    rw [← hcover]
    exact subsystemPerm_union k ι hYPF (θ σ)
  let D := L P + L F - L (P ∪ F)
  have hD : D.PosSemidef := posSemidef_mergeDeficit
    (fun σ τ => commute_subsystemPerm_of_disjoint k ι hPF (θ σ) (θ τ))
    (fun σ => subsystemPerm_union k ι hPF (θ σ))
  have hGQ' : G * Q = D * Q := by
    simp only [G, D, sub_mul, add_mul, hY]
  have hQH : Q.IsHermitian := (isStarProjection_symProj _).isSelfAdjoint.isHermitian
  refine ⟨hGQ, ?_⟩
  apply Matrix.le_iff.mpr
  rw [sub_zero, mul_assoc, hGQ', ← mul_assoc]
  simpa only [hQH.eq] using hD.conjTranspose_mul_mul_same Q

/-- Label observables from the two disjoint groups of copies commute for
arbitrary choices of physical regions. Source: `07-comparators.tex`,
lines 454--480. -/
theorem commute_grouped_labelObservables
    {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k) (S T : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ)
    (g : IrrepLabel (Equiv.Perm (Fin r)) → ℝ) :
    Commute (labelObservable ((subsystemPerm k ι S).comp (groupHom₁ e)) f)
      (labelObservable ((subsystemPerm k ι T).comp (groupHom₂ e)) g) :=
  commute_labelObservable_of_commute
    ((subsystemPerm k ι S).comp (groupHom₁ e))
    ((subsystemPerm k ι T).comp (groupHom₂ e))
    (fun σ τ => commute_subsystemPerm_of_commute ι k S T (groupHom_commute e σ τ)) f g

/-- Every good-copy label observable preserves the simultaneous symmetric
subspace of the bad copies. Source: `07-comparators.tex`, lines 454--480. -/
theorem commute_good_labelObservable_bad_symProj
    {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k) (S : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    Commute (labelObservable ((subsystemPerm k ι S).comp (groupHom₁ e)) f)
      (symProj ((subsystemPerm k ι Finset.univ).comp (groupHom₂ e))) := by
  unfold labelObservable symProj
  refine Commute.sum_left _ _ _ fun ell _ => ?_
  refine ((Commute.sum_right _ _ _ (fun τ _ => ?_)).smul_left _).smul_right _
  simpa only [labelProj, groupAlgebraRep_single, one_smul] using
    commute_groupAlgebraRep_of_commute
      ((subsystemPerm k ι S).comp (groupHom₁ e))
      ((subsystemPerm k ι Finset.univ).comp (groupHom₂ e))
      (fun σ τ => commute_subsystemPerm_of_commute ι k S Finset.univ
        (groupHom_commute e σ τ))
      (IrrepLabel.centralIdem ell) (MonoidAlgebra.single τ (1 : ℂ))

end TensorPower

end

end GroupedLabelSymmetricSupport

section SubsystemLabelCommutation

/-!
## Central observables of nested subsystems after restricting the copy action

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

end

end SubsystemLabelCommutation

section SymmetricSupport

/-!
## Nonnegative label support for a partition of arbitrary finite factors

The conclusion concerns simultaneous symmetry of all coordinate factors.
It requires neither nonempty coordinate factors nor a cutoff or a vector.

### References

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

end SymmetricSupport
