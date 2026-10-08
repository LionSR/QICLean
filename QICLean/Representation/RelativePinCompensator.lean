/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.TensorPowerRpow
import QICLean.Representation.ReplicaLift
import QICLean.Representation.ReplicaSimilarity
import QICLean.Analysis.RootChannel
import QICLean.Algebra.L2OpNormReindex

/-!
# The compensators of a move

For a region `R` and a density matrix `ρ_R` on it, the compensator is
`T_R = W_{R,k}^{-1} (ρ_R^t)^{⊗k}` on `V^{⊗k}` (*A two-dimensional area law from a global spectral
gap*, `05-replicas.tex`, proof of Lemma 6.3, lines 535–551). The paper bounds it by
`‖T_R‖ ≤ poly(k)` uniformly in `ρ_R`, including marginals of deficient rank: in the `λ` block
the eigenvalues of `ρ_R^{⊗k}` are at most `d_λ^{-1}`, and `W_{R,k} ≥ poly(k)^{-1} e^{-t F}`.

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `TensorPower.reindex_labelObservable_subsystemPerm`.
* `TensorPower.exists_l2_opNorm_compensator_le` — `‖T_R‖ ≤ (k + 2)^C`.
-/

open Matrix PermutationRepresentation Entropy
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TensorPower

variable {F : Type*} [DecidableEq F] [Fintype F] (ι : F → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)]

/-- A label observable of a subsystem, in split coordinates. -/
theorem reindex_labelObservable_subsystemPerm (k : ℕ) (Q : Finset F)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    reindex (splitEquiv ι k Q) (splitEquiv ι k Q) (labelObservable (subsystemPerm k ι Q) f) =
      labelObservable (copyPerm (SubConfig ι Q) k) f ⊗ₖ
        (1 : Matrix (Fin k → ComplConfig ι Q) (Fin k → ComplConfig ι Q) ℂ) := by
  ext p p'
  simp only [labelObservable, reindex_apply, submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, kroneckerMap_apply, Finset.sum_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h := congrFun (congrFun (labelProj_subsystemPerm_eq ι k Q l) p) p'
  simp only [reindex_apply, submatrix_apply, kroneckerMap_apply] at h
  rw [h, mul_assoc]

theorem labelProj_subsystemPerm_ne_zero [∀ f, Nonempty (ι f)] {k : ℕ} {Q : Finset F}
    {l : IrrepLabel (Equiv.Perm (Fin k))} (hl : labelProj (copyPerm (SubConfig ι Q) k) l ≠ 0) :
    labelProj (subsystemPerm k ι Q) l ≠ 0 := by
  intro h0
  apply hl
  have h := labelProj_subsystemPerm_eq ι k Q l
  rw [h0] at h
  ext a b
  obtain ⟨c⟩ : Nonempty (Fin k → ComplConfig ι Q) := inferInstance
  have := congrFun (congrFun h (a, c)) (b, c)
  simpa [kroneckerMap_apply] using this.symm

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- **The compensator bound** (`05-replicas.tex`, equation `replicas:compensator`): there is
`C` such that `‖W_{R,k}^{-1} ((ρ_R^t ⊗ 1)^{⊗k})‖ ≤ (k + 2)^C` for every `k`, every region `R`
and every density matrix `ρ_R` on `R`. -/
theorem exists_l2_opNorm_compensator_le [∀ v, NeZero (n v)] {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (R : Finset V)
      (ρ : Matrix (RegionConfig n R) (RegionConfig n R) ℂ), ρ.PosSemidef → ρ.trace = 1 →
        ‖(replicaMetric (fun v => Fin (n v)) t k R)⁻¹ * tensorPow (k := k) (localLift R (ρ ^ t))‖
          ≤ ((k : ℝ) + 2) ^ C := by
  set ι : V → Type := fun v => Fin (n v)
  have : ∀ v, Nonempty (ι v) := fun v => ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨C, hC0, hC⟩ := exists_abs_log_replicaLabelWeight_add_le ι ht
  refine ⟨C, hC0, fun k R ρ hρ htr => ?_⟩
  set w := fun l : IrrepLabel (Equiv.Perm (Fin k)) => replicaLabelWeight ι t l
  have hw : ∀ l, 0 < w l := fun l => replicaLabelWeight_pos ι ht.le l
  have hM : (0 : ℝ) ≤ ((k : ℝ) + 2) ^ C := by positivity
  have hinv := replicaMetric_inv_eq (n := n) ht.le k R
  set A := labelObservable (copyPerm (SubConfig ι R) k) fun l => (w l)⁻¹
  have hre : reindex (splitEquiv ι k R) (splitEquiv ι k R)
      ((replicaMetric ι t k R)⁻¹ * tensorPow (k := k) (localLift R (ρ ^ t))) =
      (A * tensorPow (k := k) (ρ ^ t)) ⊗ₖ
        (1 : Matrix (Fin k → ComplConfig ι R) (Fin k → ComplConfig ι R) ℂ) := by
    rw [reindex_apply, ← submatrix_mul_equiv _ _ _ (splitEquiv ι k R).symm, ← reindex_apply,
      ← reindex_apply, hinv, reindex_labelObservable_subsystemPerm, reindex_tensorPow_localLift,
      ← mul_kronecker_mul, Matrix.one_mul]
  rw [← l2_opNorm_reindex_equiv (splitEquiv ι k R), hre]
  refine (l2_opNorm_kronecker_one_le _).trans ?_
  refine l2_opNorm_labelObservable_mul_tensorPow_rpow_le hρ htr ht.le hw hM fun l hl => ?_
  have hl' := labelProj_subsystemPerm_ne_zero ι hl
  have h := hC k R l hl'
  have hd : (0 : ℝ) < l.dim := by exact_mod_cast l.dim_pos
  have hlog : -Real.log (w l) ≤ C * Real.log ((k : ℝ) + 2) + t * Real.log l.dim := by
    have := (abs_le.mp h).1
    simp only [w]
    linarith
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  calc (w l)⁻¹ = Real.exp (-Real.log (w l)) := by
        rw [Real.exp_neg, Real.exp_log (hw l)]
    _ ≤ Real.exp (C * Real.log ((k : ℝ) + 2) + t * Real.log l.dim) := Real.exp_le_exp.mpr hlog
    _ = ((k : ℝ) + 2) ^ C * (l.dim : ℝ) ^ t := by
        rw [Real.exp_add, Real.rpow_def_of_pos hk, Real.rpow_def_of_pos hd, mul_comm C,
          mul_comm t]

end TensorPower
