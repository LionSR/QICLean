/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.BandMetric.Setup
import QICLean.ManyBody.Entropy.MovementEtaRegional
import QICLean.ManyBody.Entropy.RegionStrongSubadditivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# The entropy of a move of a partition

A move of a partition `(P, Y, F)` of the tensor factors transfers a subsystem `x ⊆ Y` to `P`
or to `F`. Its entropy `moveEta` is the conditional mutual information `I(x : F | P)` for a
move to `P` and `I(x : P | F)` for a move to `F` (area-law paper, `06-transport.tex`, display
`transport:move-eta`, lines 321–330). This file proves:

* the entropy of a valid move is nonnegative, by strong subadditivity;
* a move of the empty subsystem has entropy zero;
* since complementary regions of a pure vector have equal entropy, the entropy of a move to
  `P` is the sum `S(x ∪ P) - S(P) + S(Y) - S(Y ∖ x)` of two conditional entropy differences,
  and the same holds for a move to `F` with `F` in place of `P`.

These are balanced entropy identities and inequalities, so the vector need not be normalized.

## Main statements

* `TensorPower.ReplicaTransport.moveEta_nonneg`
* `TensorPower.ReplicaTransport.moveEta_toP_eq_entropy_difference`,
  `TensorPower.ReplicaTransport.moveEta_toF_eq_entropy_difference`

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `06-transport.tex`, display `transport:move-eta`, lines 321–330; `05-replicas.tex`,
  lines 490–492.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ)

/-- The entropy of a valid move is nonnegative: it is a conditional mutual information of
pairwise disjoint regions, the moved subsystem `x ⊆ Y` and the two outer parts of the
partition. -/
theorem moveEta_nonneg (π : PYF V) (hπ : π.IsPartition) (m : Move V)
    (hm : m.IsValid π) (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    0 ≤ moveEta n π m θ := by
  cases m with
  | stay => exact le_rfl
  | toP x =>
    exact ManyBody.conditionalMutualInformation_nonneg _ θ x π.F π.P
      (hπ.2.2.1.mono_left hm) (hπ.1.symm.mono_left hm) hπ.2.1.symm
  | toF x =>
    exact ManyBody.conditionalMutualInformation_nonneg _ θ x π.P π.F
      (hπ.1.symm.mono_left hm) (hπ.2.2.1.mono_left hm) hπ.2.1

/-- Moving the empty subsystem to `P` has entropy zero. The move `toP ∅` is a different
move from `stay`. -/
@[simp] theorem moveEta_toP_empty (π : PYF V)
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) : moveEta n π (.toP ∅) θ = 0 := by
  simp only [moveEta, ManyBody.conditionalMutualInformation, Finset.empty_union]
  ring

/-- Moving the empty subsystem to `F` has entropy zero. -/
@[simp] theorem moveEta_toF_empty (π : PYF V)
    (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) : moveEta n π (.toF ∅) θ = 0 := by
  simp only [moveEta, ManyBody.conditionalMutualInformation, Finset.empty_union]
  ring

/-- For a partition `(P, Y, F)` and `x ⊆ Y`, the entropy of the move of `x` to `P` is
`S(x ∪ P) - S(P) + S(Y) - S(Y ∖ x)`: the conditional mutual information `I(x : F | P)` is
the sum of the two conditional entropies `S(x | P)` and `S(x | Y ∖ x)`, because the vector
is pure on the four regions `P, x, Y ∖ x, F`. -/
theorem moveEta_toP_eq_entropy_difference (π : PYF V) (hπ : π.IsPartition)
    (x : Finset V) (hx : x ⊆ π.Y) (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    moveEta n π (.toP x) θ =
      ManyBody.regionEntropy θ (x ∪ π.P) -
        ManyBody.regionEntropy θ π.P +
      ManyBody.regionEntropy θ π.Y -
        ManyBody.regionEntropy θ (π.Y \ x) := by
  have h4 : Entropy.FourPartition π.P x (π.Y \ x) π.F :=
    { Px := hπ.1.mono_right hx
      PY := hπ.1.mono_right Finset.sdiff_subset
      PF := hπ.2.1
      xY := Finset.disjoint_sdiff
      xF := hπ.2.2.1.mono_left hx
      YF := hπ.2.2.1.mono_left Finset.sdiff_subset
      cover := fun v => by
        have hv : v ∈ π.P ∪ π.Y ∪ π.F := by rw [hπ.2.2.2]; exact Finset.mem_univ v
        simp only [Finset.mem_union, Finset.mem_sdiff] at hv ⊢
        tauto }
  have h := Entropy.regionalMovementEta_eq_cmi_left h4 θ
  simp only [moveEta, ← h, Entropy.regionalMovementEta, Finset.union_sdiff_of_subset hx,
    Finset.union_comm π.P x]
  ring

/-- For a partition `(P, Y, F)` and `x ⊆ Y`, the entropy of the move of `x` to `F` is
`S(x ∪ F) - S(F) + S(Y) - S(Y ∖ x)`. The conditional entropy difference is taken on the side
`F`; it is not the entropy of the move of `x` to `P`. -/
theorem moveEta_toF_eq_entropy_difference (π : PYF V) (hπ : π.IsPartition)
    (x : Finset V) (hx : x ⊆ π.Y) (θ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    moveEta n π (.toF x) θ =
      ManyBody.regionEntropy θ (x ∪ π.F) -
        ManyBody.regionEntropy θ π.F +
      ManyBody.regionEntropy θ π.Y -
        ManyBody.regionEntropy θ (π.Y \ x) := by
  have hswap : (⟨π.F, π.Y, π.P⟩ : PYF V).IsPartition := by
    refine ⟨hπ.2.2.1.symm, hπ.2.1.symm, hπ.1.symm, ?_⟩
    simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]
      using hπ.2.2.2
  exact moveEta_toP_eq_entropy_difference n ⟨π.F, π.Y, π.P⟩ hswap x hx θ

end TensorPower.ReplicaTransport
