/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RelativePinCompensator
import QICLean.Representation.RelativePinAlgebra
import QICLean.Representation.MergeMoment
import QICLean.Entropy.FilterStationarity

/-!
# Label functions commute with tensor powers of local operators

Let `Q` be a region of `V = ⨂_v ℂ^{n_v}`. The copy permutations of `Q` commute with
`(M ⊗ 1)^{⊗k}` for every operator `M` supported on a region `R ⊆ Q` (they permute the copies
of `Q`, on which `M^{⊗k}` is symmetric) and for every `M` supported on a region disjoint from `Q`
(write the copy permutation of `Q` as a full copy permutation times the inverse copy permutation
of `Qᶜ`). Hence every label function of `Q` commutes with such tensor powers. This is the
commutation used for the compensators in the proof of Lemma 6.3 (*A two-dimensional area law
from a global spectral gap*, `05-replicas.tex`, lines 541–546).

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `TensorPower.commute_permOp_subsystemPerm_tensorPow_localLift`.
* `TensorPower.commute_labelObservable_tensorPow_of_subset`,
  `TensorPower.commute_labelObservable_tensorPow_of_disjoint`.
-/

open Matrix PermutationRepresentation Entropy
open scoped Kronecker MatrixOrder ComplexOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

theorem reindex_permOp_subsystemPerm (k : ℕ) (Q : Finset V) (π : Equiv.Perm (Fin k)) :
    reindex (splitEquiv (fun v => Fin (n v)) k Q) (splitEquiv (fun v => Fin (n v)) k Q)
        (permOp (subsystemPerm k (fun v => Fin (n v)) Q) π) =
      permOp (copyPerm (RegionConfig n Q) k) π ⊗ₖ
        (1 : Matrix (Fin k → (v : {v // v ∉ Q}) → Fin (n v))
          (Fin k → (v : {v // v ∉ Q}) → Fin (n v)) ℂ) := by
  rw [← permOp_prodLeft, permOp_of_intertwine (splitEquiv (fun v => Fin (n v)) k Q)
    (fun g x => splitEquiv_subsystemPerm (fun v => Fin (n v)) k Q g x) π]

/-- The copy permutations of `Q` commute with tensor powers of operators on `Q`. -/
theorem commute_permOp_subsystemPerm_tensorPow_localLift {k : ℕ} (Q : Finset V)
    (M : Matrix (RegionConfig n Q) (RegionConfig n Q) ℂ) (π : Equiv.Perm (Fin k)) :
    Commute (permOp (subsystemPerm k (fun v => Fin (n v)) Q) π)
      (tensorPow (k := k) (localLift Q M)) := by
  set e := splitEquiv (fun v => Fin (n v)) k Q
  have hmul : ∀ A B : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ,
      reindex e e (A * B) = reindex e e A * reindex e e B := fun A B => by
    simp [reindex_apply, submatrix_mul_equiv]
  apply (reindex e e).injective
  rw [hmul, hmul, reindex_permOp_subsystemPerm, reindex_tensorPow_localLift,
    ← mul_kronecker_mul, ← mul_kronecker_mul, (commute_permOp_copyPerm_tensorPow M π).eq]

theorem commute_permOp_subsystemPerm_tensorPow_of_subset {k : ℕ} {Q R : Finset V}
    (hRQ : R ⊆ Q) (σ₀ : SiteConfig n) (M : Matrix (RegionConfig n R) (RegionConfig n R) ℂ)
    (π : Equiv.Perm (Fin k)) :
    Commute (permOp (subsystemPerm k (fun v => Fin (n v)) Q) π)
      (tensorPow (k := k) (localLift R M)) := by
  obtain ⟨K, hK⟩ := ((isSupportedOn_localLift M).mono hRQ).exists_localLift σ₀
  rw [hK]
  exact commute_permOp_subsystemPerm_tensorPow_localLift Q K π

theorem commute_permOp_subsystemPerm_tensorPow_of_disjoint {k : ℕ} {Q R : Finset V}
    (hRQ : Disjoint R Q) (σ₀ : SiteConfig n) (M : Matrix (RegionConfig n R) (RegionConfig n R) ℂ)
    (π : Equiv.Perm (Fin k)) :
    Commute (permOp (subsystemPerm k (fun v => Fin (n v)) Q) π)
      (tensorPow (k := k) (localLift R M)) := by
  have hsub : R ⊆ Qᶜ := fun v hv => Finset.mem_compl.mpr (Finset.disjoint_left.mp hRQ hv)
  have hc := commute_permOp_subsystemPerm_tensorPow_of_subset hsub σ₀ M π (k := k)
  have hfull := commute_permOp_copyPerm_tensorPow (k := k) (localLift R M) π
  have hsplit : permOp (copyPerm (SiteConfig n) k) π =
      permOp (subsystemPerm k (fun v => Fin (n v)) Q) π *
        permOp (subsystemPerm k (fun v => Fin (n v)) Qᶜ) π :=
    permOp_of_eq_mul _ _ _ (fun g => copyPerm_eq_mul_compl (ι := fun v => Fin (n v)) Q g) π
  have hinv : permOp (subsystemPerm k (fun v => Fin (n v)) Q) π =
      permOp (copyPerm (SiteConfig n) k) π *
        permOp (subsystemPerm k (fun v => Fin (n v)) Qᶜ) π⁻¹ := by
    rw [hsplit, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  rw [hinv]
  exact hfull.mul_left (commute_permOp_subsystemPerm_tensorPow_of_subset hsub σ₀ M π⁻¹)

/-- A label function of `Q` commutes with tensor powers of operators on `R ⊆ Q`. -/
theorem commute_labelObservable_tensorPow_of_subset {k : ℕ} {Q R : Finset V} (hRQ : R ⊆ Q)
    (σ₀ : SiteConfig n) (M : Matrix (RegionConfig n R) (RegionConfig n R) ℂ)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f)
      (tensorPow (k := k) (localLift R M)) :=
  commute_labelObservable_of_forall_commute _
    (fun π => commute_permOp_subsystemPerm_tensorPow_of_subset hRQ σ₀ M π) f

/-- A label function of `Q` commutes with tensor powers of operators on regions disjoint from
`Q`. -/
theorem commute_labelObservable_tensorPow_of_disjoint {k : ℕ} {Q R : Finset V}
    (hRQ : Disjoint R Q) (σ₀ : SiteConfig n) (M : Matrix (RegionConfig n R) (RegionConfig n R) ℂ)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f)
      (tensorPow (k := k) (localLift R M)) :=
  commute_labelObservable_of_forall_commute _
    (fun π => commute_permOp_subsystemPerm_tensorPow_of_disjoint hRQ σ₀ M π) f

end TensorPower
