/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaMetric
import QICLean.Representation.ReplicaRatio

/-!
# The marked ratio of the replica metrics

Let `k = m + 1`. The area-law paper (*A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, Lemma 6.2, lines 320–323) extends `W_{Q,k-1}` by the identity on the last
copy and puts `R_{Q,k} = W_{Q,k} W_{Q,k-1}^{-1}`. This file proves the forward assertion
`‖R_{Q,k} - (J_{Q,k})_+^t‖ → 0` on the entire tensor space (equation `replicas:R-forward`),
with the explicit uniform rate `O(k^{-t})`, together with the uniform bound on `‖R_{Q,k}‖`
(lines 416–417). Here `J_{Q,k}` is the normalized star operator of `Q`, and the operator norm
is the `L²` operator norm.

The proof follows lines 402–417: `R_{Q,k}` and `J_{Q,k}` are both diagonal in the joint
decomposition by the label `λ` of all copies and the label `ν` of the first `k - 1` copies;
on a removable branch `ν = λ - e_i` they act by the marked ratio `r_{λ,i}` and by
`(l_i - d)/k`, and `Partition.exists_abs_replicaRatio_sub_le` compares the two.

## Main declarations

* `TensorPower.snocEquiv`, `TensorPower.replicaMetricFirst`,
  `TensorPower.replicaMetricFirst_eq` — the extension of `W_{Q,k-1}` by the identity.
* `TensorPower.markedRatio` — `R_{Q,k}`.
* `TensorPower.starOp_subsystemPerm_eq_hom`, `TensorPower.markedRatio_eq_hom` — the joint
  diagonal forms.
* `TensorPower.exists_l2_opNorm_markedRatio_sub_le` — `‖R_{Q,k} - (J_{Q,k})_+^t‖ ≤ C k^{-t}`.
* `TensorPower.exists_l2_opNorm_markedRatio_le` — `‖R_{Q,k}‖ ≤ C`.
-/

open Matrix PermutationRepresentation
open scoped Kronecker Matrix.Norms.L2Operator

namespace TensorPower

variable {F : Type*} [DecidableEq F] [Fintype F] (ι : F → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)]

/-! ### The extension of `W_{Q,k-1}` by the identity on the last copy -/

/-- `V^{⊗(m+1)} ≅ V^{⊗m} ⊗ V`, splitting off the last copy. -/
def snocEquiv (m : ℕ) : Config (m + 1) ι ≃ Config m ι × ((f : F) → ι f) where
  toFun x := (fun j => x (Fin.castSucc j), x (Fin.last m))
  invFun p := Fin.snoc p.1 p.2
  left_inv x := Fin.snoc_init_self x
  right_inv p := by simp

omit [DecidableEq F] [Fintype F] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
@[simp]
theorem snocEquiv_apply (m : ℕ) (x : Config (m + 1) ι) :
    snocEquiv ι m x = (fun j => x (Fin.castSucc j), x (Fin.last m)) := rfl

omit [Fintype F] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
theorem snocEquiv_subsystemPerm (m : ℕ) (Q : Finset F) (σ : Equiv.Perm (Fin m))
    (x : Config (m + 1) ι) :
    prodLeft ((f : F) → ι f) (subsystemPerm m ι Q) σ (snocEquiv ι m x) =
      snocEquiv ι m ((subsystemPerm (m + 1) ι Q).comp (firstCopies m) σ x) := by
  have hc : ∀ j : Fin m, (firstCopies m σ)⁻¹ (Fin.castSucc j) = Fin.castSucc (σ⁻¹ j) := by
    intro j
    rw [Equiv.Perm.inv_eq_iff_eq, firstCopies_castSucc]
    simp
  have hl : (firstCopies m σ)⁻¹ (Fin.last m) = Fin.last m := by
    rw [Equiv.Perm.inv_eq_iff_eq, firstCopies_last]
  ext j f
  · simp only [snocEquiv_apply, prodLeft_apply, MonoidHom.comp_apply, subsystemPerm_apply, hc]
  · simp only [snocEquiv_apply, prodLeft_apply, MonoidHom.comp_apply, subsystemPerm_apply, hl,
      ite_self]

/-- `W_{Q,k-1}` extended by the identity on the last copy, written as the central label
function of the copy permutations of `Q` that fix the last copy. -/
noncomputable def replicaMetricFirst (t : ℝ) (m : ℕ) (Q : Finset F) :
    Matrix (Config (m + 1) ι) (Config (m + 1) ι) ℂ :=
  labelObservable ((subsystemPerm (m + 1) ι Q).comp (firstCopies m)) (replicaLabelWeight ι t)

/-- `replicaMetricFirst` is the extension of `W_{Q,k-1}` by the identity on the last copy
(`05-replicas.tex`, line 320). -/
theorem replicaMetricFirst_eq (t : ℝ) (m : ℕ) (Q : Finset F) :
    reindex (snocEquiv ι m) (snocEquiv ι m) (replicaMetricFirst ι t m Q) =
      replicaMetric ι t m Q ⊗ₖ (1 : Matrix ((f : F) → ι f) ((f : F) → ι f) ℂ) := by
  have hl : ∀ l, reindex (snocEquiv ι m) (snocEquiv ι m)
      (labelProj ((subsystemPerm (m + 1) ι Q).comp (firstCopies m)) l) =
        labelProj (subsystemPerm m ι Q) l ⊗ₖ (1 : Matrix ((f : F) → ι f) ((f : F) → ι f) ℂ) :=
    fun l => (labelProj_of_intertwine (snocEquiv ι m)
      (fun σ x => snocEquiv_subsystemPerm ι m Q σ x) l).symm.trans (labelProj_prodLeft _ l)
  rw [replicaMetricFirst, replicaMetric, labelObservable, labelObservable]
  rw [show ∀ A : Matrix (Config (m + 1) ι) (Config (m + 1) ι) ℂ,
      reindex (snocEquiv ι m) (snocEquiv ι m) A =
        reindexLinearEquiv ℂ ℂ (snocEquiv ι m) (snocEquiv ι m) A from fun _ => rfl, map_sum]
  have hk : ∀ A : Matrix (Config m ι) (Config m ι) ℂ,
      A ⊗ₖ (1 : Matrix ((f : F) → ι f) ((f : F) → ι f) ℂ) =
        (kroneckerBilinear (R := ℂ) : Matrix (Config m ι) (Config m ι) ℂ →ₗ[ℂ]
          Matrix ((f : F) → ι f) ((f : F) → ι f) ℂ →ₗ[ℂ] _).flip
          (1 : Matrix ((f : F) → ι f) ((f : F) → ι f) ℂ) A :=
    fun _ => rfl
  rw [hk, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_smul, ← hk, coe_reindexLinearEquiv, hl]

/-- The marked ratio `R_{Q,k} = W_{Q,k} W_{Q,k-1}^{-1}`, `k = m + 1`
(`05-replicas.tex`, line 321). -/
noncomputable def markedRatio (t : ℝ) (m : ℕ) (Q : Finset F) :
    Matrix (Config (m + 1) ι) (Config (m + 1) ι) ℂ :=
  replicaMetric ι t (m + 1) Q * (replicaMetricFirst ι t m Q)⁻¹

/-! ### The joint branch decomposition -/

variable {ι} in
theorem isOrthogonalResolution_branch (m : ℕ) (Q : Finset F) :
    IsOrthogonalResolution fun p : IrrepLabel (Equiv.Perm (Fin (m + 1))) ×
        IrrepLabel (Equiv.Perm (Fin m)) =>
      labelProj (subsystemPerm (m + 1) ι Q) p.1 *
        labelProj ((subsystemPerm (m + 1) ι Q).comp (firstCopies m)) p.2 :=
  (isOrthogonalResolution_labelProj _).prod (isOrthogonalResolution_labelProj _)
    fun l n => (commute_labelProj_comp _ (firstCopies m) n l).symm

theorem isHermitian_branch (m : ℕ) (Q : Finset F)
    (p : IrrepLabel (Equiv.Perm (Fin (m + 1))) × IrrepLabel (Equiv.Perm (Fin m))) :
    (labelProj (subsystemPerm (m + 1) ι Q) p.1 *
      labelProj ((subsystemPerm (m + 1) ι Q).comp (firstCopies m)) p.2).IsHermitian :=
  ((isHermitian_labelProj _ _).commute_iff (isHermitian_labelProj _ _)).mp
    (commute_labelProj_comp _ (firstCopies m) p.2 p.1).symm

/-- The row of a removable branch `ν = λ - e_i` (zero off the branches). -/
noncomputable def markedRow {m : ℕ}
    (p : IrrepLabel (Equiv.Perm (Fin (m + 1))) × IrrepLabel (Equiv.Perm (Fin m))) : ℕ :=
  open Classical in
  if h : ∃ i, labelPart p.1 = Function.update (labelPart p.2) i (labelPart p.2 i + 1) then
    Classical.choose h else 0

theorem markedRow_spec {m : ℕ}
    {p : IrrepLabel (Equiv.Perm (Fin (m + 1))) × IrrepLabel (Equiv.Perm (Fin m))}
    (h : ∃ i, labelPart p.1 = Function.update (labelPart p.2) i (labelPart p.2 i + 1)) :
    labelPart p.1 =
      Function.update (labelPart p.2) (markedRow p) (labelPart p.2 (markedRow p) + 1) := by
  simp only [markedRow, h, ↓reduceDIte]
  exact Classical.choose_spec h

/-- The star eigenvalue `(λ_i - 1 - i)/k` on the branch (rows from `0`). -/
noncomputable def starValue {m : ℕ}
    (p : IrrepLabel (Equiv.Perm (Fin (m + 1))) × IrrepLabel (Equiv.Perm (Fin m))) : ℝ :=
  ((labelPart p.1 (markedRow p) : ℝ) - 1 - markedRow p) / (m + 1 : ℕ)

/-- **The star operator in the branch decomposition** (`05-replicas.tex`, Lemma 6.1(6)):
`J_{Q,k} = ∑_{λ,ν} ((λ_i - 1 - i)/k) π^λ π^ν`. -/
theorem starOp_subsystemPerm_eq_hom (m : ℕ) (Q : Finset F) :
    starOp (subsystemPerm (m + 1) ι Q) =
      (isOrthogonalResolution_branch m Q).hom fun p => (starValue p : ℂ) := by
  set hJ := isOrthogonalResolution_branch (ι := ι) m Q
  rw [IsOrthogonalResolution.hom_apply]
  conv_lhs => rw [← mul_one (starOp _), ← hJ.sum_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : labelProj (subsystemPerm (m + 1) ι Q) p.1 *
      labelProj ((subsystemPerm (m + 1) ι Q).comp (firstCopies m)) p.2 = 0
  · rw [hp, mul_zero, smul_zero]
  · obtain ⟨-, hbr⟩ := (labelProj_mul_labelProj_firstCopies_ne_zero_iff _ p.1 p.2).mp hp
    rw [starOp_mul_branch _ (markedRow_spec hbr), starValue]
    congr 1
    push_cast
    ring

/-- `W_{Q,k}` in the branch decomposition. -/
theorem replicaMetric_succ_eq_hom (t : ℝ) (m : ℕ) (Q : Finset F) :
    replicaMetric ι t (m + 1) Q =
      (isOrthogonalResolution_branch m Q).hom fun p => (replicaLabelWeight ι t p.1 : ℂ) := by
  rw [IsOrthogonalResolution.hom_apply, Fintype.sum_prod_type, replicaMetric, labelObservable]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp_rw [← smul_mul_assoc]
  rw [← Finset.mul_sum, (isOrthogonalResolution_labelProj _).sum_eq, mul_one]

/-- The extended `W_{Q,k-1}` in the branch decomposition. -/
theorem replicaMetricFirst_eq_hom (t : ℝ) (m : ℕ) (Q : Finset F) :
    replicaMetricFirst ι t m Q =
      (isOrthogonalResolution_branch m Q).hom fun p => (replicaLabelWeight ι t p.2 : ℂ) := by
  rw [IsOrthogonalResolution.hom_apply, Fintype.sum_prod_type_right, replicaMetricFirst,
    labelObservable]
  refine Finset.sum_congr rfl fun n _ => ?_
  dsimp only
  rw [← Finset.smul_sum, ← Finset.sum_mul, (isOrthogonalResolution_labelProj _).sum_eq, one_mul]

/-- **The marked ratio in the branch decomposition**: `R_{Q,k} = ∑ (w_k(λ)/w_{k-1}(ν)) π^λ π^ν`
(`05-replicas.tex`, lines 402–409). -/
theorem markedRatio_eq_hom [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t) (m : ℕ)
    (Q : Finset F) :
    markedRatio ι t m Q = (isOrthogonalResolution_branch m Q).hom
      fun p => ((replicaLabelWeight ι t p.1 / replicaLabelWeight ι t p.2 : ℝ) : ℂ) := by
  set hJ := isOrthogonalResolution_branch (ι := ι) m Q
  have hinv : (replicaMetricFirst ι t m Q)⁻¹ =
      hJ.hom fun p => (((replicaLabelWeight ι t p.2)⁻¹ : ℝ) : ℂ) := by
    rw [replicaMetricFirst_eq_hom]
    refine Matrix.inv_eq_left_inv ?_
    rw [← map_mul, ← map_one hJ.hom]
    congr 1
    ext p
    have := (replicaLabelWeight_pos ι ht p.2).ne'
    simp [this]
  rw [markedRatio, hinv, replicaMetric_succ_eq_hom, ← map_mul]
  congr 1
  ext p
  simp [div_eq_mul_inv]

/-- The scalar data on a nonzero branch: the ratio of the label functions is the marked ratio
`r(k, L)` and the star eigenvalue is `(L - d)/k`, for a shifted part `1 ≤ L ≤ k + d`. -/
theorem exists_branch_scalars [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t) (m : ℕ)
    (Q : Finset F)
    (p : IrrepLabel (Equiv.Perm (Fin (m + 1))) × IrrepLabel (Equiv.Perm (Fin m)))
    (hp : labelProj (subsystemPerm (m + 1) ι Q) p.1 *
      labelProj ((subsystemPerm (m + 1) ι Q).comp (firstCopies m)) p.2 ≠ 0) :
    ∃ L : ℕ, 1 ≤ L ∧ L ≤ (m + 1) + replicaDim ι ∧
      replicaLabelWeight ι t p.1 / replicaLabelWeight ι t p.2 =
        Partition.replicaRatio (replicaDim ι) t (m + 1 : ℕ) L ∧
      starValue p = ((L : ℝ) - replicaDim ι) / (m + 1 : ℕ) ∧
      (p.2.dim : ℝ) / p.1.dim ≤ 2 ^ replicaDim ι * ((L : ℝ) / (m + 1 : ℕ)) := by
  set d := replicaDim ι
  obtain ⟨hl, hbr⟩ := (labelProj_mul_labelProj_firstCopies_ne_zero_iff _ p.1 p.2).mp hp
  have hspec := markedRow_spec hbr
  set i := markedRow p
  have hrows : ∀ a, d ≤ a → labelPart p.1 a = 0 := fun a ha =>
    labelPart_eq_zero_of_subsystemPerm ι (m + 1) Q hl a ((card_subConfig_le ι Q).trans ha)
  have hli : labelPart p.1 i = labelPart p.2 i + 1 := by rw [hspec, Function.update_self]
  have hid : i < d := by
    by_contra h
    have := hrows i (not_lt.mp h)
    omega
  have hle : ∀ a, labelPart p.2 a ≤ labelPart p.1 a := by
    intro a
    rw [hspec]
    by_cases ha : a = i
    · subst ha; simp
    · simp [Function.update_of_ne ha]
  have hrows2 : ∀ a, d ≤ a → labelPart p.2 a = 0 := fun a ha =>
    Nat.eq_zero_of_le_zero ((hle a).trans (hrows a ha).le)
  have hsum2 : ∑ a : Fin d, part d p.2 a = m := sum_labelPart_of_rows p.2 hrows2
  have hsum1 : ∑ a : Fin d, part d p.1 a = m + 1 := sum_labelPart_of_rows p.1 hrows
  set i' : Fin d := ⟨i, hid⟩
  have hpart : part d p.1 = Function.update (part d p.2) i' (part d p.2 i' + 1) := by
    funext a
    by_cases ha : a = i'
    · subst ha; simp [part, hli, i']
    · have ha' : (a : ℕ) ≠ i := fun h => ha (Fin.ext h)
      simp only [part, Function.update_of_ne ha]
      rw [hspec, Function.update_of_ne ha']
  have hupd := Partition.replicaWeight_update_succ (replicaDim_pos ι) ht (part d p.2) i'
  rw [← hpart, hsum2] at hupd
  set L := Partition.shiftedPart (part d p.2) i' + 1
  have hL : (L : ℝ) = labelPart p.1 i + (d - 1 - i : ℕ) := by
    simp only [L, Partition.shiftedPart, part, hli, i']
    push_cast
    ring
  have hlam : labelPart p.1 i ≤ m + 1 :=
    calc labelPart p.1 i = part d p.1 i' := rfl
      _ ≤ ∑ a, part d p.1 a :=
        Finset.single_le_sum (f := part d p.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i')
      _ = m + 1 := hsum1
  have hLlam : Partition.shiftedPart (part d p.1) i' = L := by
    simp only [L, Partition.shiftedPart, part, i', hli]
    omega
  refine ⟨L, by simp [L], ?_, ?_, ?_, ?_⟩
  · simp only [L, Partition.shiftedPart, part, i']
    have := hli
    omega
  · rw [replicaLabelWeight, replicaLabelWeight, hupd,
      mul_div_assoc, div_self (Partition.replicaWeight_pos (replicaDim_pos ι) ht _).ne', mul_one]
  · rw [starValue, hL]
    congr 1
    have : ((d - 1 - i : ℕ) : ℝ) = d - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [this]
    ring
  · have := dim_div_dim_le hspec hrows hid
    rwa [hLlam] at this

/-- **Lemma 6.2, forward marked ratio** (`05-replicas.tex`, equation `replicas:R-forward`): on
the entire tensor space, `‖R_{Q,k} - (J_{Q,k})_+^t‖ ≤ C k^{-t}` with `k = m + 1`, uniformly in
the subsystem `Q`. In particular `‖R_{Q,k} - (J_{Q,k})_+^t‖ → 0`. -/
theorem exists_l2_opNorm_markedRatio_sub_le [∀ f, Nonempty (ι f)] {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    ∃ C, ∀ (m : ℕ) (Q : Finset F),
      ‖markedRatio ι t m Q -
          cfc (fun x : ℝ => (max x 0) ^ t) (starOp (subsystemPerm (m + 1) ι Q))‖ ≤
        C * ((m + 1 : ℕ) : ℝ) ^ (-t) := by
  obtain ⟨C, hC⟩ := Partition.exists_abs_replicaRatio_sub_le (replicaDim_pos ι) ht0 ht1
  refine ⟨max C 0, fun m Q => ?_⟩
  set hJ := isOrthogonalResolution_branch (ι := ι) m Q
  rw [starOp_subsystemPerm_eq_hom, IsOrthogonalResolution.cfc_hom _ (isHermitian_branch ι m Q),
    markedRatio_eq_hom ι ht0.le, ← map_sub]
  refine hJ.l2_opNorm_hom_le (isHermitian_branch ι m Q) (by positivity) fun p hp => ?_
  obtain ⟨L, hL1, hL2, hr, hs, -⟩ := exists_branch_scalars ι ht0.le m Q p hp
  simp only [Pi.sub_apply]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hr, hs]
  exact (hC (m + 1) L (by omega) hL1 hL2).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- **Lemma 6.2, uniform bound on the marked ratio** (`05-replicas.tex`, lines 416–417):
`‖R_{Q,k}‖ ≤ C` uniformly in `k` and `Q`. -/
theorem exists_l2_opNorm_markedRatio_le [∀ f, Nonempty (ι f)] {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    ∃ C, ∀ (m : ℕ) (Q : Finset F), ‖markedRatio ι t m Q‖ ≤ C := by
  obtain ⟨C, hC1, hC⟩ := Partition.exists_replicaRatio_bounds (replicaDim_pos ι) ht0 ht1
  refine ⟨C, fun m Q => ?_⟩
  rw [markedRatio_eq_hom ι ht0.le]
  refine (isOrthogonalResolution_branch m Q).l2_opNorm_hom_le (isHermitian_branch ι m Q)
    (by linarith) fun p hp => ?_
  obtain ⟨L, hL1, hL2, hr, -, -⟩ := exists_branch_scalars ι ht0.le m Q p hp
  have hpos : 0 < replicaLabelWeight ι t p.1 / replicaLabelWeight ι t p.2 :=
    div_pos (replicaLabelWeight_pos ι ht0.le _) (replicaLabelWeight_pos ι ht0.le _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, hr]
  exact (hC (m + 1) L (by omega) hL1 hL2).2

end TensorPower
