/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SplitCopies
import QICLean.Representation.BranchingPieri

/-!
# Highest-weight vectors in `V_μ ⊗ Λ^r ℂ^q`

Let `μ` be a label of `S_m` and `A_r` the antisymmetrizer of the last `r` of `m + r` copies.
The idempotent `e^μ_{00} ⊗ A_r` of `ℂ[S_{m+r}]` cuts out `V_μ ⊗ Λ^r ℂ^q` inside
`(ℂ^q)^{⊗(m + r)}`. A highest-weight vector of weight `λ` fixed by it has components
`w_z ∈ V_μ`, indexed by configurations `z` of the last `r` copies, which are antisymmetric in
`z`; the component with the largest `∑_j z_j` among the nonzero ones is a highest-weight vector
of `V_μ`. Hence `λ = μ + 1_S` for a set `S` of `r` rows, and such vectors form a space of
dimension at most one.

This is the highest-weight half of the vertical-strip Pieri rule
`V_μ ⊗ Λ^r ℂ^q = ⊕_{λ/μ vertical strip} V_λ`, used for the Weyl character formula in the
proof of Lemma 6.2 of the area-law paper (*A two-dimensional area law from a global spectral
gap*, `05-replicas.tex`, lines 336–364). The argument is the one of `BranchingPieri.lean`
with `ℂ^q` replaced by `Λ^r ℂ^q`.

The proofs are written from the standard theory; no Lean source was adapted.

## Main declarations

* `TensorPower.pieriElem μ r` — the idempotent `e^μ_{00} ⊗ A_r`.
* `TensorPower.sliceR z w` — the component of `w` along the configuration `z` of the last
  `r` copies.
* `TensorPower.finrank_hwSpace_pieri_le_one` — the highest-weight bound.
* `TensorPower.pieriRank_le_one_and` — the multiplicity of `λ` in `V_μ ⊗ Λ^r` is at most one,
  and nonzero only for `λ = μ + 1_S`.
-/

open Finset Matrix PermutationRepresentation MonoidAlgebra

namespace TensorPower

variable {q m r : ℕ}

/-! ### The idempotent `e^μ_{00} ⊗ A_r` -/

theorem restrictHom_left_mul_right (b : MonoidAlgebra ℂ (Equiv.Perm (Fin m)))
    (c : MonoidAlgebra ℂ (Equiv.Perm (Fin r))) :
    IrrepLabel.restrictHom (leftCopies m r) b * IrrepLabel.restrictHom (rightCopies m r) c =
      IrrepLabel.restrictHom (rightCopies m r) c * IrrepLabel.restrictHom (leftCopies m r) b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b b' hb hb' => rw [map_add, add_mul, mul_add, hb, hb']
  | single σ s =>
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add c c' hc hc' => rw [map_add, mul_add, add_mul, hc, hc']
    | single τ t =>
      simp only [IrrepLabel.restrictHom, mapDomainAlgHom_apply, mapDomain_single,
        single_mul_single, leftCopies_mul_rightCopies, mul_comm s t]

/-- The idempotent `e^μ_{00} ⊗ A_r ∈ ℂ[S_{m+r}]`. -/
noncomputable def pieriElem (μ : IrrepLabel (Equiv.Perm (Fin m))) (r : ℕ) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin (m + r))) :=
  IrrepLabel.restrictHom (leftCopies m r)
      (IrrepLabel.matrixUnit μ ⟨0, μ.dim_pos⟩ ⟨0, μ.dim_pos⟩) *
    IrrepLabel.restrictHom (rightCopies m r) (antisym r)

theorem leftUnit_mul_self (μ : IrrepLabel (Equiv.Perm (Fin m))) :
    IrrepLabel.restrictHom (leftCopies m r)
        (IrrepLabel.matrixUnit μ ⟨0, μ.dim_pos⟩ ⟨0, μ.dim_pos⟩) *
      IrrepLabel.restrictHom (leftCopies m r)
        (IrrepLabel.matrixUnit μ ⟨0, μ.dim_pos⟩ ⟨0, μ.dim_pos⟩) =
      IrrepLabel.restrictHom (leftCopies m r)
        (IrrepLabel.matrixUnit μ ⟨0, μ.dim_pos⟩ ⟨0, μ.dim_pos⟩) := by
  rw [← map_mul, IrrepLabel.matrixUnit_mul_matrixUnit, ite_eq_left rfl]

theorem rightAntisym_mul_self :
    IrrepLabel.restrictHom (rightCopies m r) (antisym r) *
      IrrepLabel.restrictHom (rightCopies m r) (antisym r) =
      IrrepLabel.restrictHom (rightCopies m r) (antisym r) := by
  rw [← map_mul, antisym_mul_antisym]

theorem pieriElem_mul_self (μ : IrrepLabel (Equiv.Perm (Fin m))) :
    pieriElem μ r * pieriElem μ r = pieriElem μ r := by
  simp only [pieriElem]
  rw [mul_assoc, ← mul_assoc (IrrepLabel.restrictHom (rightCopies m r) (antisym r)),
    ← restrictHom_left_mul_right, mul_assoc, rightAntisym_mul_self, ← mul_assoc,
    leftUnit_mul_self]

theorem groupAlgebraRep_pieriElem (μ : IrrepLabel (Equiv.Perm (Fin m))) :
    groupAlgebraRep (copyPerm (Fin q) (m + r)) (pieriElem μ r) =
      splitOp (unitOp q μ) (groupAlgebraRep (copyPerm (Fin q) r) (antisym r)) := by
  rw [pieriElem, map_mul, groupAlgebraRep_leftCopies, groupAlgebraRep_rightCopies,
    splitOp_mul, Matrix.mul_one, Matrix.one_mul]
  rfl

/-! ### Components along the last copies -/

/-- The component of a vector along the configuration `z` of the last `r` copies. -/
def sliceR (z : Fin r → Fin q) (w : (Fin (m + r) → Fin q) → ℂ) : (Fin m → Fin q) → ℂ :=
  fun x => w (Fin.append x z)

theorem sliceR_add (z : Fin r → Fin q) (w w' : (Fin (m + r) → Fin q) → ℂ) :
    sliceR z (w + w') = sliceR z w + sliceR z w' := rfl

theorem sliceR_smul (z : Fin r → Fin q) (c : ℂ) (w : (Fin (m + r) → Fin q) → ℂ) :
    sliceR z (c • w) = c • sliceR z w := rfl

theorem sliceR_splitOp_one (z : Fin r → Fin q) (A : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ)
    (w : (Fin (m + r) → Fin q) → ℂ) :
    sliceR z (splitOp A 1 *ᵥ w) = A *ᵥ sliceR z w := by
  funext x
  simp only [sliceR, mulVec, dotProduct]
  rw [sum_append]
  refine sum_congr rfl fun x' _ => ?_
  rw [sum_eq_single z]
  · rw [splitOp_append, Matrix.one_apply_eq, mul_one]
  · intro z' _ hz'
    rw [splitOp_append, Matrix.one_apply_ne (Ne.symm hz'), mul_zero, zero_mul]
  · simp

theorem sliceR_permOp_rightCopies (z : Fin r → Fin q) (τ : Equiv.Perm (Fin r))
    (w : (Fin (m + r) → Fin q) → ℂ) :
    sliceR z (permOp (copyPerm (Fin q) (m + r)) (rightCopies m r τ) *ᵥ w) =
      sliceR (copyPerm (Fin q) r τ⁻¹ z) w := by
  funext x
  simp only [sliceR, permOp_mulVec, Function.comp_apply, ← map_inv]
  rw [copyPerm_rightCopies_append]

theorem castAdd_ne_natAdd (i : Fin m) (j : Fin r) : Fin.castAdd r i ≠ Fin.natAdd m j := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem update_append_castAdd (x : Fin m → Fin q) (z : Fin r → Fin q) (i : Fin m)
    (b : Fin q) :
    Function.update (Fin.append x z) (Fin.castAdd r i) b =
      Fin.append (Function.update x i b) z := by
  funext j
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) j
  · by_cases h : i' = i
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.castAdd_inj.mp e)), Fin.append_left,
        Fin.append_left, Function.update_of_ne h]
  · rw [Function.update_of_ne (castAdd_ne_natAdd i j').symm, Fin.append_right,
      Fin.append_right]

theorem update_append_natAdd (x : Fin m → Fin q) (z : Fin r → Fin q) (j : Fin r)
    (b : Fin q) :
    Function.update (Fin.append x z) (Fin.natAdd m j) b =
      Fin.append x (Function.update z j b) := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun j' => ?_) i
  · rw [Function.update_of_ne (castAdd_ne_natAdd i' j), Fin.append_left, Fin.append_left]
  · by_cases h : j' = j
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (Fin.ext (by
        have := congrArg Fin.val e; simp only [Fin.val_natAdd] at this; omega))), Fin.append_right,
        Fin.append_right, Function.update_of_ne h]

theorem sliceR_gen (z : Fin r → Fin q) (a b : Fin q) (w : (Fin (m + r) → Fin q) → ℂ) :
    sliceR z (gen a b *ᵥ w) = gen a b *ᵥ sliceR z w +
      ∑ j, if z j = a then sliceR (Function.update z j b) w else 0 := by
  funext x
  simp only [sliceR, gen_mulVec_apply, Pi.add_apply, Finset.sum_apply]
  rw [Fin.sum_univ_add]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    rw [Fin.append_left, update_append_castAdd]
  · refine sum_congr rfl fun j _ => ?_
    rw [Fin.append_right, update_append_natAdd]
    split_ifs <;> rfl

theorem weight_append (x : Fin m → Fin q) (z : Fin r → Fin q) :
    weight (Fin.append x z) = weight x + weight z := by
  funext a
  simp only [weight, Pi.add_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem IsWeightVector.sliceR {ν : Fin q → ℤ} {w : (Fin (m + r) → Fin q) → ℂ}
    (hw : IsWeightVector ν w) (z : Fin r → Fin q) :
    IsWeightVector (ν - weight z) (TensorPower.sliceR z w) := by
  intro x hx
  have := hw _ hx
  rw [weight_append] at this
  rw [← this]
  abel

/-! ### Antisymmetry of the components -/

theorem single_rightCopies_mul_antisym (τ : Equiv.Perm (Fin r)) :
    IrrepLabel.restrictHom (rightCopies m r) (single τ (1 : ℂ)) *
        IrrepLabel.restrictHom (rightCopies m r) (antisym r) =
      (Equiv.Perm.sign τ : ℂ) • IrrepLabel.restrictHom (rightCopies m r) (antisym r) := by
  rw [← map_mul, single_mul_antisym, map_smul]

/-- A vector fixed by `e^μ_{00} ⊗ A_r` is fixed by both factors. -/
theorem fixed_left_right {μ : IrrepLabel (Equiv.Perm (Fin m))} {w : (Fin (m + r) → Fin q) → ℂ}
    (hw : groupAlgebraRep (copyPerm (Fin q) (m + r)) (pieriElem μ r) *ᵥ w = w) :
    splitOp (unitOp q μ) 1 *ᵥ w = w ∧
      groupAlgebraRep (copyPerm (Fin q) (m + r))
        (IrrepLabel.restrictHom (rightCopies m r) (antisym r)) *ᵥ w = w := by
  set L := IrrepLabel.restrictHom (leftCopies m r)
    (IrrepLabel.matrixUnit μ ⟨0, μ.dim_pos⟩ ⟨0, μ.dim_pos⟩)
  set R := IrrepLabel.restrictHom (rightCopies m r) (antisym r)
  have hL : groupAlgebraRep (copyPerm (Fin q) (m + r)) L = splitOp (unitOp q μ) 1 :=
    groupAlgebraRep_leftCopies _
  constructor
  · rw [← hL, ← hw, mulVec_mulVec, ← map_mul, pieriElem, ← mul_assoc, leftUnit_mul_self]
  · rw [← hw, mulVec_mulVec, ← map_mul, pieriElem]
    change groupAlgebraRep _ (R * (L * R)) *ᵥ w = groupAlgebraRep _ (L * R) *ᵥ w
    rw [← mul_assoc, ← restrictHom_left_mul_right, mul_assoc, rightAntisym_mul_self]

theorem sliceR_copyPerm_of_fixed {w : (Fin (m + r) → Fin q) → ℂ}
    (hw : groupAlgebraRep (copyPerm (Fin q) (m + r))
      (IrrepLabel.restrictHom (rightCopies m r) (antisym r)) *ᵥ w = w)
    (z : Fin r → Fin q) (τ : Equiv.Perm (Fin r)) :
    sliceR (copyPerm (Fin q) r τ⁻¹ z) w = (Equiv.Perm.sign τ : ℂ) • sliceR z w := by
  have h : permOp (copyPerm (Fin q) (m + r)) (rightCopies m r τ) *ᵥ w =
      (Equiv.Perm.sign τ : ℂ) • w := by
    have e := single_rightCopies_mul_antisym (m := m) τ
    rw [← hw, mulVec_mulVec]
    have h1 : permOp (copyPerm (Fin q) (m + r)) (rightCopies m r τ) =
        groupAlgebraRep (copyPerm (Fin q) (m + r))
          (IrrepLabel.restrictHom (rightCopies m r) (single τ 1)) := by
      rw [← groupAlgebraRep_comp, groupAlgebraRep_single, one_smul, permOp_comp]
    rw [h1, ← map_mul, e, map_smul, smul_mulVec, hw]
  rw [← sliceR_permOp_rightCopies, h, sliceR_smul]

theorem sliceR_eq_zero_of_not_injective {w : (Fin (m + r) → Fin q) → ℂ}
    (hw : groupAlgebraRep (copyPerm (Fin q) (m + r))
      (IrrepLabel.restrictHom (rightCopies m r) (antisym r)) *ᵥ w = w)
    {z : Fin r → Fin q} (hz : ¬Function.Injective z) : sliceR z w = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, z i = z j ∧ i ≠ j := by
    by_contra h
    push Not at h
    exact hz fun a b hab => h a b hab
  have hswap : copyPerm (Fin q) r (Equiv.swap i j)⁻¹ z = z := by
    funext a
    simp only [copyPerm_apply, Equiv.swap_inv]
    rcases eq_or_ne a i with rfl | hai
    · simp [hij]
    rcases eq_or_ne a j with rfl | haj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hai haj]
  have h := sliceR_copyPerm_of_fixed hw z (Equiv.swap i j)
  rw [hswap, Equiv.Perm.sign_swap hne] at h
  have h2 : (2 : ℂ) • sliceR z w = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-! ### The highest-weight bound -/

/-- The hypotheses on a vector `w` used below: a highest-weight vector of weight `ν` whose
components lie in `V_μ` and are antisymmetric in the last copies. -/
structure IsPieriVector (μ : IrrepLabel (Equiv.Perm (Fin m))) (ν : Fin q → ℤ)
    (w : (Fin (m + r) → Fin q) → ℂ) : Prop where
  hw : w ∈ hwSpace ν
  mem : ∀ z, sliceR z w ∈ multSpace q μ
  zero : ∀ z, ¬Function.Injective z → sliceR z w = 0
  perm : ∀ z τ, sliceR (copyPerm (Fin q) r τ⁻¹ z) w = (Equiv.Perm.sign τ : ℂ) • sliceR z w

theorem isPieriVector_of_fixed {μ : IrrepLabel (Equiv.Perm (Fin m))} {ν : Fin q → ℤ}
    {w : (Fin (m + r) → Fin q) → ℂ} (hhw : w ∈ hwSpace ν)
    (hfix : groupAlgebraRep (copyPerm (Fin q) (m + r)) (pieriElem μ r) *ᵥ w = w) :
    IsPieriVector μ ν w := by
  obtain ⟨hL, hR⟩ := fixed_left_right hfix
  refine ⟨hhw, fun z => ?_, fun z hz => sliceR_eq_zero_of_not_injective hR hz,
    sliceR_copyPerm_of_fixed hR⟩
  rw [← hL, sliceR_splitOp_one]
  exact unitOp_mulVec_mem μ _

/-- The sum `∑_j z_j` used to order the configurations of the last copies. -/
def zSum (z : Fin r → Fin q) : ℕ := ∑ j, (z j : ℕ)

theorem zSum_update_lt {z : Fin r → Fin q} {j : Fin r} {b : Fin q} (h : z j < b) :
    zSum z < zSum (Function.update z j b) := by
  simp only [zSum]
  rw [← add_sum_erase _ _ (mem_univ j), ← add_sum_erase _ _ (mem_univ j)]
  simp only [Function.update_self]
  have : ∑ x ∈ univ.erase j, ((Function.update z j b x : Fin q) : ℕ) =
      ∑ x ∈ univ.erase j, (z x : ℕ) :=
    sum_congr rfl fun x hx => by rw [Function.update_of_ne (mem_erase.mp hx).1]
  rw [this]
  have : (z j : ℕ) < b := h
  omega

/-- The component with the largest `∑_j z_j` among the nonzero components of a Pieri vector is
a highest-weight vector of `V_μ`. -/
theorem exists_sliceR_isHighestWeight {μ : IrrepLabel (Equiv.Perm (Fin m))} {ν : Fin q → ℤ}
    {w : (Fin (m + r) → Fin q) → ℂ} (hw : IsPieriVector μ ν w) (h0 : w ≠ 0) :
    ∃ z, Function.Injective z ∧ IsHighestWeight (ν - weight z) (sliceR z w) := by
  classical
  have hS : (univ.filter fun z : Fin r → Fin q => sliceR z w ≠ 0).Nonempty := by
    obtain ⟨v, hv⟩ := Function.ne_iff.mp h0
    refine ⟨fun j => v (Fin.natAdd m j), mem_filter.mpr ⟨mem_univ _, fun h => hv ?_⟩⟩
    have := congrFun h (fun i => v (Fin.castAdd r i))
    simpa [sliceR, Fin.append_castAdd_natAdd] using this
  obtain ⟨z, hzS, hmax⟩ := exists_max_image _ zSum hS
  have hz0 : sliceR z w ≠ 0 := (mem_filter.mp hzS).2
  have hinj : Function.Injective z := by
    by_contra h
    exact hz0 (hw.zero z h)
  refine ⟨z, hinj, hz0, hw.hw.1.sliceR z, fun a b hab => ?_⟩
  have h := sliceR_gen z a b w
  rw [hw.hw.2 a b hab] at h
  have hzero : ∀ j, (if z j = a then sliceR (Function.update z j b) w else 0) = 0 := by
    intro j
    split_ifs with hj
    · by_contra hne
      have := hmax _ (mem_filter.mpr ⟨mem_univ _, hne⟩)
      have hlt := zSum_update_lt (z := z) (j := j) (b := b) (hj ▸ hab)
      omega
    · rfl
  rw [sum_eq_zero fun j _ => hzero j, add_zero] at h
  exact h.symm

theorem weight_pos_iff (z : Fin r → Fin q) (a : Fin q) : 0 < weight z a ↔ ∃ j, z j = a := by
  simp only [weight]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    rw [sum_eq_zero fun i _ => by simp [hne i]] at h
    exact lt_irrefl _ h
  · rintro ⟨j, hj⟩
    exact lt_of_lt_of_le (by simp [hj])
      (single_le_sum (f := fun i => if z i = a then (1 : ℤ) else 0)
        (fun i _ => by split_ifs <;> norm_num) (mem_univ j))

/-- Injective configurations with the same weight differ by a permutation of the copies. -/
theorem exists_copyPerm_of_weight_eq {z z' : Fin r → Fin q} (hz : Function.Injective z)
    (h : weight z = weight z') :
    ∃ τ : Equiv.Perm (Fin r), copyPerm (Fin q) r τ⁻¹ z' = z := by
  classical
  have hrange : ∀ a, (∃ j, z j = a) ↔ ∃ j, z' j = a := fun a => by
    rw [← weight_pos_iff, ← weight_pos_iff, h]
  choose g hg using fun j => (hrange (z j)).mp ⟨j, rfl⟩
  have hginj : Function.Injective g := fun a b hab => hz (by rw [← hg a, ← hg b, hab])
  set τ := Equiv.ofBijective g hginj.bijective_of_finite
  refine ⟨τ, funext fun j => ?_⟩
  simp only [copyPerm_apply, inv_inv]
  exact hg j

/-- **The highest-weight bound for `V_μ ⊗ Λ^r`.** Pieri vectors of weight `ν` form a space of
dimension at most one, and exist only for `ν = μ + 1_S` with `|S| = r`. -/
theorem finrank_hwSpace_pieri_le_one (μ : IrrepLabel (Equiv.Perm (Fin m)))
    (hμ : multSpace q μ ≠ ⊥) (ν : Fin q → ℤ) (W : Submodule ℂ ((Fin (m + r) → Fin q) → ℂ))
    (hW : ∀ w ∈ W, IsPieriVector μ ν w) :
    Module.finrank ℂ W ≤ 1 ∧
      (W ≠ ⊥ → ∃ z : Fin r → Fin q, Function.Injective z ∧ ν = shape q μ hμ + weight z) := by
  classical
  have key : ∀ w ∈ W, w ≠ 0 → ∃ z, Function.Injective z ∧ ν = shape q μ hμ + weight z ∧
      sliceR z w ≠ 0 := by
    intro w hwW h0
    obtain ⟨z, hinj, hhw⟩ := exists_sliceR_isHighestWeight (hW w hwW) h0
    refine ⟨z, hinj, ?_, hhw.ne_zero⟩
    have := shape_eq_of_isHighestWeight hμ hhw ((hW w hwW).mem z)
    rw [this]
    abel
  by_cases hbot : W = ⊥
  · subst hbot; simp
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨z₀, hz₀, hν, -⟩ := key w₀ hw₀ hw₀0
  refine ⟨?_, fun _ => ⟨z₀, hz₀, hν⟩⟩
  obtain ⟨v, hvV, hv⟩ := exists_isHighestWeight_shape hμ
  let Φ : W →ₗ[ℂ] (Fin m → Fin q) → ℂ :=
    { toFun := fun w => sliceR z₀ (w : (Fin (m + r) → Fin q) → ℂ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have hne' : (w : (Fin (m + r) → Fin q) → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨z, hz, hν', hzw⟩ := key w w.2 hne'
    have hwt : weight z = weight z₀ := by
      rw [hν] at hν'
      exact (add_left_cancel hν').symm
    obtain ⟨τ, hτ⟩ := exists_copyPerm_of_weight_eq hz hwt
    apply hzw
    rw [← hτ, (hW w w.2).perm z₀ τ]
    change (Equiv.Perm.sign τ : ℂ) • Φ w = 0
    rw [hw, smul_zero]
  have hrange : LinearMap.range Φ ≤ ℂ ∙ v := by
    rintro _ ⟨w, rfl⟩
    have hwt : IsWeightVector (shape q μ hμ) (sliceR z₀ (w : (Fin (m + r) → Fin q) → ℂ)) := by
      have := (hW w w.2).hw.1.sliceR z₀
      rwa [hν, add_sub_cancel_right] at this
    exact (isIrreducible_multSpace hμ).mem_span_of_isWeightVector hv hvV ((hW w w.2).mem z₀) hwt
  calc Module.finrank ℂ W = Module.finrank ℂ (LinearMap.range Φ) :=
        (LinearMap.finrank_range_of_inj hΦ).symm
    _ ≤ Module.finrank ℂ (ℂ ∙ v) := Submodule.finrank_mono hrange
    _ = 1 := finrank_span_singleton hv.ne_zero
    _ ≤ 1 := le_rfl

/-! ### The multiplicity of `λ` in `V_μ ⊗ Λ^r` -/

/-- The multiplicity of `λ` in `V_μ ⊗ Λ^r`: the rank of the `λ` block of `e^μ_{00} ⊗ A_r`. -/
noncomputable def pieriRank (μ : IrrepLabel (Equiv.Perm (Fin m)))
    (l : IrrepLabel (Equiv.Perm (Fin (m + r)))) : ℕ :=
  Module.finrank ℂ (LinearMap.range (toLin' (IrrepLabel.block l (pieriElem μ r))))

theorem trace_block_pieriElem (μ : IrrepLabel (Equiv.Perm (Fin m)))
    (l : IrrepLabel (Equiv.Perm (Fin (m + r)))) :
    (IrrepLabel.block l (pieriElem μ r)).trace = pieriRank μ l :=
  trace_eq_finrank_range_of_mul_self (by rw [← IrrepLabel.block_mul, pieriElem_mul_self])

/-- **The multiplicity bound** for `V_μ ⊗ Λ^r`, in any dimension `q` in which `λ` and `μ`
occur: the multiplicity is at most one, and nonzero only when `λ = μ + 1_S`. -/
theorem pieriRank_le_one_and (μ : IrrepLabel (Equiv.Perm (Fin m)))
    (l : IrrepLabel (Equiv.Perm (Fin (m + r)))) (hμ : multSpace q μ ≠ ⊥)
    (hl : multSpace q l ≠ ⊥) :
    pieriRank μ l ≤ 1 ∧ (pieriRank μ l ≠ 0 →
      ∃ z : Fin r → Fin q, Function.Injective z ∧ shape q l hl = shape q μ hμ + weight z) := by
  classical
  obtain ⟨v, hvV, hv⟩ := exists_isHighestWeight_shape hl
  set φ := copyPerm (Fin q) (m + r)
  set o : Fin l.dim := ⟨0, l.dim_pos⟩
  set B := IrrepLabel.block l (pieriElem μ r)
  set a := pieriElem μ r
  have hidem : groupAlgebraRep φ a * groupAlgebraRep φ a = groupAlgebraRep φ a := by
    rw [← map_mul, pieriElem_mul_self]
  let Ψ : (Fin l.dim → ℂ) →ₗ[ℂ] (Fin (m + r) → Fin q) → ℂ :=
    { toFun := fun c => ∑ p, c p • (matrixUnitOp φ l p o *ᵥ v)
      map_add' := fun c c' => by simp [add_smul, sum_add_distrib]
      map_smul' := fun z c => by simp [smul_sum, smul_smul] }
  have hvhw : v ∈ hwSpace (shape q l hl) := ⟨hv.isWeightVector, hv.raising⟩
  have hΨhw : ∀ c, Ψ c ∈ hwSpace (shape q l hl) := fun c => by
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _
      (groupAlgebraRep_mulVec_mem_hwSpace hvhw (IrrepLabel.matrixUnit l p o))
  have hΨB : ∀ c, Ψ (B *ᵥ c) = groupAlgebraRep φ a *ᵥ Ψ c := by
    intro c
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, mulVec_sum, mulVec_smul, mulVec_mulVec,
      groupAlgebraRep_mul_matrixUnitOp, sum_mulVec, smul_mulVec, smul_sum, smul_smul]
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    simp only [mulVec, dotProduct, sum_smul, B]
    exact sum_congr rfl fun j _ => by rw [mul_comm]
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    funext s
    have := congrArg (matrixUnitOp φ l o s *ᵥ ·) hc
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, mulVec_sum, mulVec_smul, mulVec_mulVec,
      mulVec_zero] at this
    rw [sum_eq_single s] at this
    · rw [matrixUnitOp_mul_matrixUnitOp_self] at this
      change c s • (unitOp q l *ᵥ v) = 0 at this
      rw [unitOp_mulVec_of_mem hvV] at this
      exact (smul_eq_zero.mp this).resolve_right hv.ne_zero
    · intro p _ hp
      rw [matrixUnitOp_mul_matrixUnitOp_of_ne_index _ _ (Ne.symm hp), zero_mulVec, smul_zero]
    · simp
  set W := (LinearMap.range (toLin' B)).map Ψ
  have hW : ∀ w ∈ W, IsPieriVector μ (shape q l hl) w := by
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    refine isPieriVector_of_fixed (hΨhw _) ?_
    simp only [toLin'_apply]
    rw [hΨB, mulVec_mulVec, hidem]
  have hfin : Module.finrank ℂ W = pieriRank μ l :=
    ((Submodule.equivMapOfInjective Ψ hΨinj _).finrank_eq).symm
  obtain ⟨hle, hex⟩ := finrank_hwSpace_pieri_le_one μ hμ _ W hW
  refine ⟨hfin ▸ hle, fun hne => hex fun h => ?_⟩
  rw [h, finrank_bot] at hfin
  exact hne hfin.symm

end TensorPower
