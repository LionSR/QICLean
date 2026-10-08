/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.Alternant
import QICLean.Representation.UnitaryTwirl
import QICLean.Representation.Branching

/-!
# Splitting `m + r` copies into the first `m` and the last `r`

On `(ℂ^q)^{⊗(m + r)} = (ℂ^q)^{⊗m} ⊗ (ℂ^q)^{⊗r}` the permutations of the first `m` copies act on
the first factor and those of the last `r` copies on the second. This file records the
operators of this splitting and computes the trace of a diagonal tensor power against the
antisymmetrizer of the last `r` copies: on `Λ^r ℂ^q` the operator `diag(y)^{⊗r}` has trace
`e_r(y)`. These are the ingredients of the vertical-strip Pieri rule for the characters of
the multiplicity spaces, used for the Weyl character formula in the proof of Lemma 6.2 of
the area-law paper (*A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, lines 336–364).

The proofs are written from the standard theory; no Lean source was adapted.

## Main declarations

* `TensorPower.leftCopies`, `TensorPower.rightCopies` — `S_m, S_r ⊆ S_{m+r}`.
* `TensorPower.splitOp A B` — the operator `A ⊗ B` on `(ℂ^q)^{⊗(m + r)}`.
* `TensorPower.groupAlgebraRep_leftCopies`, `TensorPower.groupAlgebraRep_rightCopies`,
  `TensorPower.tensorPow_eq_splitOp`, `TensorPower.trace_splitOp`.
* `TensorPower.antisym r` — the antisymmetrizer `(1/r!) ∑_τ sgn(τ) τ`.
* `TensorPower.trace_antisym_mul_tensorPow` — `Tr(A_r diag(y)^{⊗r}) = e_r(y)`.
-/

open Finset Matrix PermutationRepresentation MonoidAlgebra

namespace TensorPower

variable {q m r : ℕ}

/-! ### The two subgroups -/

variable (m r) in
/-- The permutations of the first `m` of `m + r` copies. -/
def leftCopies : Equiv.Perm (Fin m) →* Equiv.Perm (Fin (m + r)) :=
  (finSumFinEquiv.permCongrHom.toMonoidHom).comp
    ((Equiv.Perm.sumCongrHom (Fin m) (Fin r)).comp (MonoidHom.inl _ _))

variable (m r) in
/-- The permutations of the last `r` of `m + r` copies. -/
def rightCopies : Equiv.Perm (Fin r) →* Equiv.Perm (Fin (m + r)) :=
  (finSumFinEquiv.permCongrHom.toMonoidHom).comp
    ((Equiv.Perm.sumCongrHom (Fin m) (Fin r)).comp (MonoidHom.inr _ _))

@[simp]
theorem leftCopies_castAdd (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    leftCopies m r σ (Fin.castAdd r i) = Fin.castAdd r (σ i) := by
  simp [leftCopies, Equiv.permCongrHom, Equiv.permCongr_apply]

@[simp]
theorem leftCopies_natAdd (σ : Equiv.Perm (Fin m)) (j : Fin r) :
    leftCopies m r σ (Fin.natAdd m j) = Fin.natAdd m j := by
  simp [leftCopies, Equiv.permCongrHom, Equiv.permCongr_apply]

@[simp]
theorem rightCopies_castAdd (τ : Equiv.Perm (Fin r)) (i : Fin m) :
    rightCopies m r τ (Fin.castAdd r i) = Fin.castAdd r i := by
  simp [rightCopies, Equiv.permCongrHom, Equiv.permCongr_apply]

@[simp]
theorem rightCopies_natAdd (τ : Equiv.Perm (Fin r)) (j : Fin r) :
    rightCopies m r τ (Fin.natAdd m j) = Fin.natAdd m (τ j) := by
  simp [rightCopies, Equiv.permCongrHom, Equiv.permCongr_apply]

@[simp]
theorem leftCopies_symm_castAdd (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (leftCopies m r σ).symm (Fin.castAdd r i) = Fin.castAdd r (σ.symm i) :=
  (leftCopies m r σ).injective (by simp)

@[simp]
theorem leftCopies_symm_natAdd (σ : Equiv.Perm (Fin m)) (j : Fin r) :
    (leftCopies m r σ).symm (Fin.natAdd m j) = Fin.natAdd m j :=
  (leftCopies m r σ).injective (by simp)

@[simp]
theorem rightCopies_symm_castAdd (τ : Equiv.Perm (Fin r)) (i : Fin m) :
    (rightCopies m r τ).symm (Fin.castAdd r i) = Fin.castAdd r i :=
  (rightCopies m r τ).injective (by simp)

@[simp]
theorem rightCopies_symm_natAdd (τ : Equiv.Perm (Fin r)) (j : Fin r) :
    (rightCopies m r τ).symm (Fin.natAdd m j) = Fin.natAdd m (τ.symm j) :=
  (rightCopies m r τ).injective (by simp)

theorem leftCopies_mul_rightCopies (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin r)) :
    leftCopies m r σ * rightCopies m r τ = rightCopies m r τ * leftCopies m r σ := by
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

theorem copyPerm_leftCopies_append (σ : Equiv.Perm (Fin m)) (x : Fin m → Fin q)
    (z : Fin r → Fin q) :
    copyPerm (Fin q) (m + r) (leftCopies m r σ) (Fin.append x z) =
      Fin.append (copyPerm (Fin q) m σ x) z := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [Equiv.Perm.inv_def]

theorem copyPerm_rightCopies_append (τ : Equiv.Perm (Fin r)) (x : Fin m → Fin q)
    (z : Fin r → Fin q) :
    copyPerm (Fin q) (m + r) (rightCopies m r τ) (Fin.append x z) =
      Fin.append x (copyPerm (Fin q) r τ z) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [Equiv.Perm.inv_def]

/-! ### Split operators -/

/-- The operator `A ⊗ B` on `(ℂ^q)^{⊗(m + r)}`, with `A` on the first `m` and `B` on the last
`r` copies. -/
def splitOp (A : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ)
    (B : Matrix (Fin r → Fin q) (Fin r → Fin q) ℂ) :
    Matrix (Fin (m + r) → Fin q) (Fin (m + r) → Fin q) ℂ :=
  fun x y => A (fun i => x (Fin.castAdd r i)) (fun i => y (Fin.castAdd r i)) *
    B (fun i => x (Fin.natAdd m i)) (fun i => y (Fin.natAdd m i))

theorem splitOp_append (A : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ)
    (B : Matrix (Fin r → Fin q) (Fin r → Fin q) ℂ) (x x' : Fin m → Fin q) (z z' : Fin r → Fin q) :
    splitOp A B (Fin.append x z) (Fin.append x' z') = A x x' * B z z' := by
  simp [splitOp]

/-- Sums over configurations of `m + r` copies split into the two groups of copies. -/
theorem sum_append {M : Type*} [AddCommMonoid M] (f : (Fin (m + r) → Fin q) → M) :
    ∑ x, f x = ∑ x : Fin m → Fin q, ∑ z : Fin r → Fin q, f (Fin.append x z) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.appendEquiv m r) _ _ fun p => rfl).symm

/-- Matrices on `m + r` copies agree when they agree on split configurations. -/
theorem ext_append {M N : Matrix (Fin (m + r) → Fin q) (Fin (m + r) → Fin q) ℂ}
    (h : ∀ x x' z z', M (Fin.append x z) (Fin.append x' z') =
      N (Fin.append x z) (Fin.append x' z')) : M = N := by
  ext a b
  have := h (fun i => a (Fin.castAdd r i)) (fun i => b (Fin.castAdd r i))
    (fun i => a (Fin.natAdd m i)) (fun i => b (Fin.natAdd m i))
  simpa only [Fin.append_castAdd_natAdd] using this

theorem splitOp_mul (A C : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ)
    (B D : Matrix (Fin r → Fin q) (Fin r → Fin q) ℂ) :
    splitOp A B * splitOp C D = splitOp (A * C) (B * D) := by
  refine ext_append fun x x' z z' => ?_
  rw [Matrix.mul_apply, sum_append, splitOp_append, Matrix.mul_apply, Matrix.mul_apply,
    sum_mul_sum]
  refine sum_congr rfl fun x'' _ => sum_congr rfl fun z'' _ => ?_
  rw [splitOp_append, splitOp_append]
  ring

theorem trace_splitOp (A : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ)
    (B : Matrix (Fin r → Fin q) (Fin r → Fin q) ℂ) :
    (splitOp A B).trace = A.trace * B.trace := by
  simp only [trace, diag_apply]
  rw [sum_append, sum_mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun z _ => splitOp_append A B x x z z

theorem splitOp_add_left (A A' : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ)
    (B : Matrix (Fin r → Fin q) (Fin r → Fin q) ℂ) :
    splitOp (A + A') B = splitOp A B + splitOp A' B := by
  ext x y; simp [splitOp, add_mul]

theorem splitOp_add_right (A : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ)
    (B B' : Matrix (Fin r → Fin q) (Fin r → Fin q) ℂ) :
    splitOp A (B + B') = splitOp A B + splitOp A B' := by
  ext x y; simp [splitOp, mul_add]

theorem splitOp_smul_left (c : ℂ) (A : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ)
    (B : Matrix (Fin r → Fin q) (Fin r → Fin q) ℂ) :
    splitOp (c • A) B = c • splitOp A B := by
  ext x y; simp [splitOp, mul_assoc]

theorem splitOp_smul_right (c : ℂ) (A : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ)
    (B : Matrix (Fin r → Fin q) (Fin r → Fin q) ℂ) :
    splitOp A (c • B) = c • splitOp A B := by
  ext x y; simp [splitOp, mul_left_comm]

theorem splitOp_zero_left (B : Matrix (Fin r → Fin q) (Fin r → Fin q) ℂ) :
    splitOp (0 : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ) B = 0 := by
  ext x y; simp [splitOp]

theorem splitOp_zero_right (A : Matrix (Fin m → Fin q) (Fin m → Fin q) ℂ) :
    splitOp A (0 : Matrix (Fin r → Fin q) (Fin r → Fin q) ℂ) = 0 := by
  ext x y; simp [splitOp]

theorem append_eq_append_iff {x x' : Fin m → Fin q} {z z' : Fin r → Fin q} :
    Fin.append x z = Fin.append x' z' ↔ x = x' ∧ z = z' := by
  constructor
  · intro h
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · simpa using congrFun h (Fin.castAdd r i)
    · simpa using congrFun h (Fin.natAdd m i)
  · rintro ⟨rfl, rfl⟩; rfl

theorem permOp_leftCopies (σ : Equiv.Perm (Fin m)) :
    permOp (copyPerm (Fin q) (m + r)) (leftCopies m r σ) =
      splitOp (permOp (copyPerm (Fin q) m) σ) 1 := by
  refine ext_append fun x x' z z' => ?_
  simp only [splitOp_append, permOp_apply_apply, copyPerm_leftCopies_append,
    append_eq_append_iff, one_apply]
  by_cases h1 : copyPerm (Fin q) m σ x' = x <;> by_cases h2 : z' = z <;>
  simp [h1, h2, eq_comm (a := z)]

theorem permOp_rightCopies (τ : Equiv.Perm (Fin r)) :
    permOp (copyPerm (Fin q) (m + r)) (rightCopies m r τ) =
      splitOp 1 (permOp (copyPerm (Fin q) r) τ) := by
  refine ext_append fun x x' z z' => ?_
  simp only [splitOp_append, permOp_apply_apply, copyPerm_rightCopies_append,
    append_eq_append_iff, one_apply]
  by_cases h1 : x' = x <;> by_cases h2 : copyPerm (Fin q) r τ z' = z <;>
  simp [h1, h2, eq_comm (a := x)]

theorem groupAlgebraRep_leftCopies (b : MonoidAlgebra ℂ (Equiv.Perm (Fin m))) :
    groupAlgebraRep (copyPerm (Fin q) (m + r)) (IrrepLabel.restrictHom (leftCopies m r) b) =
      splitOp (groupAlgebraRep (copyPerm (Fin q) m) b) 1 := by
  rw [← groupAlgebraRep_comp]
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp [splitOp_zero_left]
  | add a b ha hb => rw [map_add, map_add, ha, hb, splitOp_add_left]
  | single σ c =>
    rw [groupAlgebraRep_single, groupAlgebraRep_single, splitOp_smul_left, permOp_comp,
      permOp_leftCopies]

theorem groupAlgebraRep_rightCopies (b : MonoidAlgebra ℂ (Equiv.Perm (Fin r))) :
    groupAlgebraRep (copyPerm (Fin q) (m + r)) (IrrepLabel.restrictHom (rightCopies m r) b) =
      splitOp 1 (groupAlgebraRep (copyPerm (Fin q) r) b) := by
  rw [← groupAlgebraRep_comp]
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp [splitOp_zero_right]
  | add a b ha hb => rw [map_add, map_add, ha, hb, splitOp_add_right]
  | single τ c =>
    rw [groupAlgebraRep_single, groupAlgebraRep_single, splitOp_smul_right, permOp_comp,
      permOp_rightCopies]

theorem tensorPow_eq_splitOp (A : Matrix (Fin q) (Fin q) ℂ) :
    tensorPow (k := m + r) A = splitOp (tensorPow A) (tensorPow A) := by
  refine ext_append fun x x' z z' => ?_
  rw [splitOp_append, tensorPow_apply, tensorPow_apply, tensorPow_apply, Fin.prod_univ_add]
  simp

/-! ### The antisymmetrizer -/

variable (r) in
/-- The antisymmetrizer `A_r = (1/r!) ∑_τ sgn(τ) τ ∈ ℂ[S_r]`. -/
noncomputable def antisym : MonoidAlgebra ℂ (Equiv.Perm (Fin r)) :=
  ∑ τ : Equiv.Perm (Fin r), ((Equiv.Perm.sign τ : ℂ) / r.factorial) • single τ 1

theorem sign_mul_sign (τ : Equiv.Perm (Fin r)) :
    (Equiv.Perm.sign τ : ℂ) * Equiv.Perm.sign τ = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem single_mul_antisym (τ : Equiv.Perm (Fin r)) :
    single τ (1 : ℂ) * antisym r = (Equiv.Perm.sign τ : ℂ) • antisym r := by
  rw [antisym, mul_sum, smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => ?_
  simp only [Equiv.coe_mulLeft, mul_smul_comm, single_mul_single, one_mul, smul_smul]
  congr 1
  rw [Equiv.Perm.sign_mul]
  push_cast
  linear_combination (-((Equiv.Perm.sign σ : ℂ) / r.factorial)) * sign_mul_sign τ

theorem antisym_mul_antisym : antisym r * antisym r = antisym r := by
  conv_lhs => arg 1; rw [antisym]
  rw [sum_mul]
  simp only [smul_mul_assoc, single_mul_antisym, smul_smul]
  rw [← sum_smul]
  have h : ∀ τ : Equiv.Perm (Fin r),
      (Equiv.Perm.sign τ : ℂ) / r.factorial * Equiv.Perm.sign τ = 1 / r.factorial := by
    intro τ
    rw [div_mul_eq_mul_div, sign_mul_sign]
  simp only [h, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_one_div_cancel (by exact_mod_cast r.factorial_ne_zero), one_smul]

/-- The signed count of the permutations fixing a configuration is `1` when its entries are
distinct and `0` otherwise. -/
theorem sum_sign_fix (z : Fin r → Fin q) :
    ∑ τ : Equiv.Perm (Fin r), (if copyPerm (Fin q) r τ z = z then
      (Equiv.Perm.sign τ : ℂ) else 0) = if Function.Injective z then 1 else 0 := by
  let F : Equiv.Perm (Fin r) → ℂ := fun τ =>
    if copyPerm (Fin q) r τ z = z then (Equiv.Perm.sign τ : ℂ) else 0
  change ∑ τ, F τ = _
  split_ifs with hz
  · rw [sum_eq_single 1]
    · simp [F]
    · intro τ _ hτ
      change (if _ then _ else _) = _
      rw [ite_eq_right]
      intro h
      apply hτ
      have key : ∀ j, τ⁻¹ j = j := fun j => by
        have : z (τ⁻¹ j) = z j := congrFun h j
        exact hz this
      have : τ⁻¹ = 1 := Equiv.ext key
      exact inv_eq_one.mp this
    · simp
  · obtain ⟨i, j, hij, hne⟩ : ∃ i j, z i = z j ∧ i ≠ j := by
      by_contra h
      push Not at h
      exact hz fun a b hab => h a b hab
    have hswap : copyPerm (Fin q) r (Equiv.swap i j) z = z := by
      funext a
      simp only [copyPerm_apply, Equiv.swap_inv]
      rcases eq_or_ne a i with rfl | hai
      · simp [hij]
      rcases eq_or_ne a j with rfl | haj
      · simp [hij]
      · rw [Equiv.swap_apply_of_ne_of_ne hai haj]
    have hFs : ∀ τ, F (Equiv.swap i j * τ) = -F τ := by
      intro τ
      have e : copyPerm (Fin q) r (Equiv.swap i j * τ) z = z ↔
          copyPerm (Fin q) r τ z = z := by
        rw [map_mul, Equiv.Perm.mul_apply]
        constructor
        · intro h
          have := congrArg (copyPerm (Fin q) r (Equiv.swap i j)) h
          rwa [← Equiv.Perm.mul_apply, ← map_mul, Equiv.swap_mul_self, map_one,
            Equiv.Perm.one_apply, hswap] at this
        · intro h; rw [h, hswap]
      simp only [F]
      by_cases h : copyPerm (Fin q) r τ z = z
      · rw [ite_eq_left (e.mpr h), ite_eq_left h, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
        push_cast; ring
      · rw [ite_eq_right (fun h' => h (e.mp h')), ite_eq_right h, neg_zero]
    have hS : ∑ τ, F τ = -∑ τ, F τ := by
      calc ∑ τ, F τ = ∑ τ, F (Equiv.swap i j * τ) :=
            (Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap i j)) _ _ fun _ => rfl).symm
        _ = -∑ τ, F τ := by rw [← sum_neg_distrib]; exact sum_congr rfl fun τ _ => hFs τ
    linear_combination hS / 2

theorem trace_permOp_mul_tensorPow_diagonal (τ : Equiv.Perm (Fin r)) (y : Fin q → ℂ) :
    (permOp (copyPerm (Fin q) r) τ * tensorPow (diagonal y)).trace =
      ∑ z : Fin r → Fin q, if copyPerm (Fin q) r τ z = z then ∏ j, y (z j) else 0 := by
  simp only [trace, diag_apply, Matrix.mul_apply, permOp_apply_apply, tensorPow_apply,
    diagonal_apply]
  refine sum_congr rfl fun z _ => ?_
  rw [sum_eq_single z]
  · split_ifs with h <;> simp
  · intro w _ hw
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
    rw [prod_eq_zero (mem_univ j) (ite_eq_right hj), mul_zero]
  · simp

/-- The number of injective configurations with a given image of size `r` is `r!`. -/
theorem card_injective_image_eq {S : Finset (Fin q)} (hS : S.card = r) :
    #(univ.filter fun z : Fin r → Fin q => Function.Injective z ∧ univ.image z = S) =
      r.factorial := by
  classical
  have e : {z : Fin r → Fin q // Function.Injective z ∧ univ.image z = S} ≃ (Fin r ↪ S) :=
    { toFun := fun z => ⟨fun j => ⟨z.1 j, by
          have h := mem_image_of_mem z.1 (mem_univ j)
          rwa [z.2.2] at h⟩,
        fun a b h => z.2.1 (congrArg Subtype.val h)⟩
      invFun := fun f => ⟨fun j => (f j : Fin q),
        fun a b h => f.injective (Subtype.ext h), by
          apply eq_of_subset_of_card_le
          · intro x hx
            obtain ⟨j, -, rfl⟩ := mem_image.mp hx
            exact (f j).2
          · rw [hS, card_image_of_injective _ fun a b h => f.injective (Subtype.ext h)]
            simp⟩
      left_inv := fun z => rfl
      right_inv := fun f => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_embedding_eq]
  simp [hS, Nat.descFactorial_self]

/-- The sum over injective configurations of `∏_j y_{z_j}` is `r! e_r(y)`. -/
theorem sum_injective_prod (y : Fin q → ℂ) :
    ∑ z : Fin r → Fin q, (if Function.Injective z then ∏ j, y (z j) else 0) =
      r.factorial * Partition.elemSymm r y := by
  classical
  rw [← sum_filter, Partition.elemSymm, mul_sum]
  rw [← sum_fiberwise_of_maps_to (g := fun z => univ.image z)
    (t := powersetCard r (univ : Finset (Fin q)))]
  · refine sum_congr rfl fun S hS => ?_
    have hS' : S.card = r := (mem_powersetCard.mp hS).2
    rw [filter_filter]
    have : ∀ z ∈ univ.filter (fun z : Fin r → Fin q => Function.Injective z ∧ univ.image z = S),
        ∏ j, y (z j) = ∏ i ∈ S, y i := by
      intro z hz
      obtain ⟨hinj, himg⟩ := (mem_filter.mp hz).2
      rw [← himg, prod_image fun a _ b _ h => hinj h]
    rw [sum_congr rfl this, sum_const, card_injective_image_eq hS', nsmul_eq_mul]
  · intro z hz
    rw [mem_powersetCard]
    exact ⟨subset_univ _, by rw [card_image_of_injective _ (mem_filter.mp hz).2]; simp⟩

/-- **The exterior power character**: `Tr(A_r diag(y)^{⊗r}) = e_r(y)`. -/
theorem trace_antisym_mul_tensorPow (y : Fin q → ℂ) :
    (groupAlgebraRep (copyPerm (Fin q) r) (antisym r) * tensorPow (diagonal y)).trace =
      Partition.elemSymm r y := by
  rw [antisym, map_sum, sum_mul, trace_sum]
  simp only [map_smul, groupAlgebraRep_single, one_smul, smul_mul_assoc, trace_smul,
    trace_permOp_mul_tensorPow_diagonal, smul_eq_mul, mul_sum]
  rw [sum_comm]
  have h : ∀ z : Fin r → Fin q, ∑ τ : Equiv.Perm (Fin r),
      (Equiv.Perm.sign τ : ℂ) / r.factorial *
        (if copyPerm (Fin q) r τ z = z then ∏ j, y (z j) else 0) =
      (1 / r.factorial) * (if Function.Injective z then ∏ j, y (z j) else 0) := by
    intro z
    rw [show (if Function.Injective z then ∏ j, y (z j) else 0) =
        (if Function.Injective z then 1 else 0) * ∏ j, y (z j) by split_ifs <;> simp,
      ← sum_sign_fix z, sum_mul, mul_sum]
    refine sum_congr rfl fun τ _ => ?_
    split_ifs <;> ring
  rw [sum_congr rfl fun z _ => h z, ← mul_sum, sum_injective_prod, one_div,
    inv_mul_cancel_left₀ (by exact_mod_cast r.factorial_ne_zero)]

end TensorPower
