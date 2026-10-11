/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaSimilarity
import QICLean.Analysis.OperatorMean.MatrixPowers

/-!
# Positive disjoint replica metric products for arbitrary local spaces

The replica metrics on three pairwise disjoint subsystems commute and
are positive definite. Their inverses remain central label observables
with the same original full-system weights. The product with two inverse
factors, and its square, are therefore positive definite.

The local coordinate spaces are arbitrary finite nonempty types. No
identification with a particular finite ordinal or symmetric-subspace
restriction is required.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `05-replicas.tex`, `replicas:leaf-metric`, lines 459--473, and
`07-comparators.tex`, `comparator:whole-inverse`, lines 441--453, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped ComplexOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
variable [∀ v, Nonempty (ι v)]

local instance replicaDisjointMetricPositivity_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The literal product of the two inverse metrics and the third metric
is positive definite on the full configuration space when the three
subsystems are pairwise disjoint. The weights are those of the original
full local family. Source: `05-replicas.tex`, `replicas:leaf-metric`,
lines 459--473. -/
theorem posDef_replicaMetric_disjoint_inv_mul_inv_mul
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P F Y : Finset V}
    (hPF : Disjoint P F) (hPY : Disjoint P Y) (hFY : Disjoint F Y) :
    ((replicaMetric ι t k P)⁻¹ * (replicaMetric ι t k F)⁻¹ *
      replicaMetric ι t k Y).PosDef := by
  let w : IrrepLabel (Equiv.Perm (Fin k)) → ℝ := replicaLabelWeight ι t
  have hinv (S : Finset V) : (replicaMetric ι t k S)⁻¹ =
      labelObservable (subsystemPerm k ι S) (fun ell => (w ell)⁻¹) :=
    labelObservable_inv _ (fun ell => (replicaLabelWeight_pos ι ht ell).ne')
  have hPF' : Commute (replicaMetric ι t k P)⁻¹ (replicaMetric ι t k F)⁻¹ := by
    rw [hinv, hinv]
    exact commute_labelObservable_of_commute _ _
      (commute_subsystemPerm_of_disjoint k ι hPF) _ _
  have hPY' : Commute (replicaMetric ι t k P)⁻¹ (replicaMetric ι t k Y) := by
    rw [hinv]
    exact commute_labelObservable_of_commute _ _
      (commute_subsystemPerm_of_disjoint k ι hPY) _ w
  have hFY' : Commute (replicaMetric ι t k F)⁻¹ (replicaMetric ι t k Y) := by
    rw [hinv]
    exact commute_labelObservable_of_commute _ _
      (commute_subsystemPerm_of_disjoint k ι hFY) _ w
  exact ((posDef_replicaMetric ι ht k P).inv.mul_of_commute
    (posDef_replicaMetric ι ht k F).inv hPF').mul_of_commute
      (posDef_replicaMetric ι ht k Y) (hPY'.mul_left hFY')

/-- The actual squared disjoint metric is positive definite for arbitrary
finite nonempty local coordinate spaces. Consequently its inverse is
positive definite as well. Source: `05-replicas.tex`, `replicas:leaf-metric`,
lines 459--473, and `07-comparators.tex`, lines 441--453. -/
theorem posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P F Y : Finset V}
    (hPF : Disjoint P F) (hPY : Disjoint P Y) (hFY : Disjoint F Y) :
    (((replicaMetric ι t k P)⁻¹ * (replicaMetric ι t k F)⁻¹ *
      replicaMetric ι t k Y) ^ 2).PosDef := by
  have h := posDef_replicaMetric_disjoint_inv_mul_inv_mul ι ht k hPF hPY hFY
  exact (h.posSemidef.pow 2).posDef_iff_isUnit.mpr (h.isUnit.pow 2)

end TensorPower
