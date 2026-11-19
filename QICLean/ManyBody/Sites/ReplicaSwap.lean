/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Relabel
import QICLean.ManyBody.Sites.SumSites

/-!
# Two replicas and the exchange of replicas on a region

Two replicas of a system of sites `V` with alphabet `α` are the sites `V ⊕ V`. Pairing the two
copies of every site identifies their configurations with the configurations of `V` with the
alphabet `α × α`, and an operator supported on `S ⊔ S` is an operator on paired sites supported
on `S`. The exchange of the two replicas on a region `R` is a permutation of `V ⊕ V`; its
operator is supported on `R ⊔ R`. Conjugating the doubled operator `A ⊗ 1 + 1 ⊗ A` of an
operator `A` supported on `S` by this exchange only depends on `R ∩ S`: it is unchanged when
`S` lies inside `R` or is disjoint from it, and it stays supported on `S ⊔ S`.

Moved from TNLean, `TNLean/Lattice/ReplicaSwap.lean` and `TNLean/Lattice/RegionalSwapSupport.lean`
at commit `e41c3b63`, restated on the sites `V ⊕ V`; the paired sites with alphabet
`Fin (q * q)` there are the sites `V` with alphabet `α × α` here.

## Main definitions

* `ManyBody.replicaSwap` — the exchange of the two replicas on a region.
* `ManyBody.replicaPairEquiv`, `ManyBody.replicaPairRegionEquiv` — pairing the two replicas.

## Main results

* `ManyBody.reindex_replicaPairEquiv_mem_supportedOperators_iff` — the support transfer.
* `ManyBody.reindex_replicaPairEquiv_place` — the placement transfer.
* `ManyBody.sitePermOp_replicaSwap_mem_supportedOperators`.
* `ManyBody.sitePermOp_replicaSwap_conj_doubled`,
  `ManyBody.sitePermOp_replicaSwap_conj_doubled_of_subset`,
  `ManyBody.sitePermOp_replicaSwap_conj_doubled_of_disjoint`,
  `ManyBody.sitePermOp_replicaSwap_conj_doubled_mem_supportedOperators` — the conjugated
  doubled operator.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 355–365, 416–424 and
  513–524, and `05-frames.tex`, lines 516–520.
-/

open Matrix

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The exchange of replicas -/

/-- The exchange of the two replicas at the sites of `R`. -/
private def replicaSwapFun (R : Finset V) : V ⊕ V → V ⊕ V
  | .inl v => if v ∈ R then .inr v else .inl v
  | .inr v => if v ∈ R then .inl v else .inr v

omit [Fintype V] in
private theorem replicaSwapFun_involutive (R : Finset V) : Function.Involutive (replicaSwapFun R) := by
  rintro (v | v) <;> by_cases hv : v ∈ R <;> simp [replicaSwapFun, hv]

/-- The exchange of the two replicas at the sites of `R`, as a permutation of `V ⊕ V`. -/
def replicaSwap (R : Finset V) : Equiv.Perm (V ⊕ V) :=
  (replicaSwapFun_involutive R).toPerm _

omit [Fintype V] in
@[simp]
theorem replicaSwap_inl (R : Finset V) (v : V) :
    replicaSwap R (.inl v) = if v ∈ R then .inr v else .inl v :=
  rfl

omit [Fintype V] in
@[simp]
theorem replicaSwap_inr (R : Finset V) (v : V) :
    replicaSwap R (.inr v) = if v ∈ R then .inl v else .inr v :=
  rfl

omit [Fintype V] in
theorem replicaSwap_inl_of_mem {R : Finset V} {v : V} (hv : v ∈ R) :
    replicaSwap R (.inl v) = .inr v := by
  simp [hv]

omit [Fintype V] in
theorem replicaSwap_inl_of_notMem {R : Finset V} {v : V} (hv : v ∉ R) :
    replicaSwap R (.inl v) = .inl v := by
  simp [hv]

omit [Fintype V] in
theorem replicaSwap_inr_of_mem {R : Finset V} {v : V} (hv : v ∈ R) :
    replicaSwap R (.inr v) = .inl v := by
  simp [hv]

omit [Fintype V] in
theorem replicaSwap_inr_of_notMem {R : Finset V} {v : V} (hv : v ∉ R) :
    replicaSwap R (.inr v) = .inr v := by
  simp [hv]

omit [Fintype V] in
theorem replicaSwap_mul_self (R : Finset V) : replicaSwap R * replicaSwap R = 1 :=
  Equiv.ext (replicaSwapFun_involutive R)

omit [Fintype V] in
/-- The exchange on `R` is the exchange on `R ∩ S` followed by the exchange on `R \ S`. -/
theorem replicaSwap_eq_mul (R S : Finset V) :
    replicaSwap R = replicaSwap (R ∩ S) * replicaSwap (R \ S) := by
  ext (v | v) <;> by_cases hR : v ∈ R <;> by_cases hS : v ∈ S <;> simp [hR, hS]

omit [Fintype V] in
theorem replicaSwap_empty : replicaSwap (∅ : Finset V) = 1 := by
  ext (v | v) <;> simp

/-- The operator exchanging the two replicas on `R` is supported on `R ⊔ R`. -/
theorem sitePermOp_replicaSwap_mem_supportedOperators (R : Finset V) :
    sitePermOp (α := α) (replicaSwap R) ∈ supportedOperators (fun _ : V ⊕ V ↦ α) (R.disjSum R) :=
  sitePermOp_mem_supportedOperators fun w hw ↦ by
    rcases w with v | v <;>
      simp_all [Finset.inl_mem_disjSum, Finset.inr_mem_disjSum]

/-! ### Pairing the two replicas -/

variable (V α) in
/-- Pairing the two replicas of every site: a configuration of `V ⊕ V` with alphabet `α` is a
configuration of `V` with alphabet `α × α`. -/
def replicaPairEquiv : Config (fun _ : V ⊕ V ↦ α) ≃ Config (fun _ : V ↦ α × α) where
  toFun σ v := (σ (.inl v), σ (.inr v))
  invFun τ := Sum.elim (fun v ↦ (τ v).1) fun v ↦ (τ v).2
  left_inv σ := by
    funext w
    cases w <;> rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α] in
@[simp]
theorem replicaPairEquiv_apply (σ : Config fun _ : V ⊕ V ↦ α) (v : V) :
    replicaPairEquiv V α σ v = (σ (.inl v), σ (.inr v)) :=
  rfl

/-- Pairing the two replicas of the sites of a region `S`. -/
def replicaPairRegionEquiv (S : Finset V) :
    RegionConfig (fun _ : V ⊕ V ↦ α) (S.disjSum S) ≃ RegionConfig (fun _ : V ↦ α × α) S where
  toFun c v := (c ⟨.inl v, Finset.inl_mem_disjSum.mpr v.2⟩,
    c ⟨.inr v, Finset.inr_mem_disjSum.mpr v.2⟩)
  invFun d w := match w with
    | ⟨.inl v, h⟩ => (d ⟨v, Finset.inl_mem_disjSum.mp h⟩).1
    | ⟨.inr v, h⟩ => (d ⟨v, Finset.inr_mem_disjSum.mp h⟩).2
  left_inv c := by
    funext ⟨w, h⟩
    cases w <;> rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α] in
private theorem mem_disjSum_self {S : Finset V} {w : V ⊕ V} :
    w ∈ S.disjSum S ↔ Sum.elim id id w ∈ S := by
  rcases w with v | v <;> simp

omit [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α] in
private theorem replicaPair_agree (p : V → Prop) (ρ ρ' : Config fun _ : V ⊕ V ↦ α) :
    (∀ v, p v → replicaPairEquiv V α ρ v = replicaPairEquiv V α ρ' v) ↔
      ∀ w : V ⊕ V, p (Sum.elim id id w) → ρ w = ρ' w := by
  constructor
  · rintro h (v | v) hv
    · exact (Prod.ext_iff.mp (h v hv)).1
    · exact (Prod.ext_iff.mp (h v hv)).2
  · intro h v hv
    exact Prod.ext (h (.inl v) hv) (h (.inr v) hv)

omit [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α] in
private theorem replicaPair_agree_mem (S : Finset V) (ρ ρ' : Config fun _ : V ⊕ V ↦ α) :
    (∀ v ∈ S, replicaPairEquiv V α ρ v = replicaPairEquiv V α ρ' v) ↔
      ∀ w ∈ S.disjSum S, ρ w = ρ' w := by
  simpa only [mem_disjSum_self] using replicaPair_agree (· ∈ S) ρ ρ'

omit [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α] in
private theorem replicaPair_agree_notMem (S : Finset V) (ρ ρ' : Config fun _ : V ⊕ V ↦ α) :
    (∀ v ∉ S, replicaPairEquiv V α ρ v = replicaPairEquiv V α ρ' v) ↔
      ∀ w ∉ S.disjSum S, ρ w = ρ' w := by
  simpa only [mem_disjSum_self] using replicaPair_agree (· ∉ S) ρ ρ'

omit [Fintype V] [DecidableEq V] [Fintype α] [DecidableEq α] in
private theorem replicaPair_exists_ne (S : Finset V) (ρ ρ' : Config fun _ : V ⊕ V ↦ α) :
    (∃ v ∉ S, replicaPairEquiv V α ρ v ≠ replicaPairEquiv V α ρ' v) ↔
      ∃ w ∉ S.disjSum S, ρ w ≠ ρ' w := by
  have h := replicaPair_agree_notMem S ρ ρ'
  constructor
  · rintro ⟨v, hv, hne⟩
    by_contra hall
    push Not at hall
    exact hne (h.mpr hall v hv)
  · rintro ⟨w, hw, hne⟩
    by_contra hall
    push Not at hall
    exact hne (h.mp hall w hw)

/-- **The support transfer.** An operator on two replicas is supported on `S ⊔ S` exactly when,
on paired sites, it is supported on `S`. -/
theorem reindex_replicaPairEquiv_mem_supportedOperators_iff {S : Finset V}
    {A : Matrix (Config fun _ : V ⊕ V ↦ α) (Config fun _ : V ⊕ V ↦ α) ℂ} :
    reindex (replicaPairEquiv V α) (replicaPairEquiv V α) A ∈
        supportedOperators (fun _ : V ↦ α × α) S ↔
      A ∈ supportedOperators (fun _ : V ⊕ V ↦ α) (S.disjSum S) := by
  set e := replicaPairEquiv V α
  have happ (σ τ : Config fun _ : V ⊕ V ↦ α) : reindex e e A (e σ) (e τ) = A σ τ := by
    simp
  rw [mem_supportedOperators_iff, mem_supportedOperators_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun σ τ hne ↦ ?_, fun σ τ σ' τ' k₁ k₂ k₃ k₄ ↦ ?_⟩
    · rw [← happ]
      exact h₁ _ _ ((replicaPair_exists_ne S σ τ).mpr hne)
    · rw [← happ, ← happ]
      exact h₂ _ _ _ _ ((replicaPair_agree_mem S σ σ').mpr k₁)
        ((replicaPair_agree_mem S τ τ').mpr k₂) ((replicaPair_agree_notMem S σ τ).mpr k₃)
        ((replicaPair_agree_notMem S σ' τ').mpr k₄)
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun σ τ hne ↦ ?_, fun σ τ σ' τ' k₁ k₂ k₃ k₄ ↦ ?_⟩
    · obtain ⟨σ, rfl⟩ := e.surjective σ
      obtain ⟨τ, rfl⟩ := e.surjective τ
      rw [happ]
      exact h₁ _ _ ((replicaPair_exists_ne S σ τ).mp hne)
    · obtain ⟨σ, rfl⟩ := e.surjective σ
      obtain ⟨τ, rfl⟩ := e.surjective τ
      obtain ⟨σ', rfl⟩ := e.surjective σ'
      obtain ⟨τ', rfl⟩ := e.surjective τ'
      rw [happ, happ]
      exact h₂ _ _ _ _ ((replicaPair_agree_mem S σ σ').mp k₁)
        ((replicaPair_agree_mem S τ τ').mp k₂) ((replicaPair_agree_notMem S σ τ).mp k₃)
        ((replicaPair_agree_notMem S σ' τ').mp k₄)

omit [Fintype α] in
/-- **The placement transfer.** On paired sites, the placement of a matrix `K` on the two
replicas of a region `S` is the placement on `S` of `K` with the replicas paired. -/
theorem reindex_replicaPairEquiv_place (S : Finset V)
    (K : Matrix (RegionConfig (fun _ : V ⊕ V ↦ α) (S.disjSum S))
      (RegionConfig (fun _ : V ⊕ V ↦ α) (S.disjSum S)) ℂ) :
    reindex (replicaPairEquiv V α) (replicaPairEquiv V α) (place (S.disjSum S) K) =
      place S (reindex (replicaPairRegionEquiv S) (replicaPairRegionEquiv S) K) := by
  set e := replicaPairEquiv V α
  ext σ τ
  obtain ⟨σ, rfl⟩ := e.surjective σ
  obtain ⟨τ, rfl⟩ := e.surjective τ
  have hreg (ρ : Config fun _ : V ⊕ V ↦ α) :
      (replicaPairRegionEquiv S).symm (fun v : S ↦ e ρ v) = fun w : S.disjSum S ↦ ρ w := by
    funext ⟨w, h⟩
    cases w <;> rfl
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, place_apply, hreg]
  exact if_congr (replicaPair_agree_notMem S σ τ).symm rfl rfl

/-! ### The doubled operator under the exchange -/

/-- The doubled operator `A ⊗ 1 + 1 ⊗ A` on the two replicas. -/
local notation "doubled" A => inlOp (Z := fun _ : V ⊕ V ↦ α) A + inrOp (Z := fun _ : V ⊕ V ↦ α) A

private theorem sitePermOp_replicaSwap_mul_self (R : Finset V) :
    sitePermOp (α := α) (replicaSwap R) * sitePermOp (replicaSwap R) = 1 := by
  rw [sitePermOp_mul, replicaSwap_mul_self, sitePermOp_one]

omit [Fintype α] in
private theorem conjTranspose_sitePermOp_replicaSwap (R : Finset V) :
    (sitePermOp (α := α) (replicaSwap R))ᴴ = sitePermOp (replicaSwap R) := by
  rw [conjTranspose_sitePermOp]
  exact congrArg _ (inv_eq_of_mul_eq_one_right (replicaSwap_mul_self R))

/-- Exchanging the replicas on the whole support of `A` exchanges `A ⊗ 1` and `1 ⊗ A`. -/
private theorem sitePermOp_replicaSwap_conj_inlOp {S : Finset V}
    {A : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ}
    (hA : A ∈ supportedOperators (fun _ : V ↦ α) S) :
    sitePermOp (replicaSwap S) * inlOp (Z := fun _ : V ⊕ V ↦ α) A *
        (sitePermOp (replicaSwap S))ᴴ = inrOp (Z := fun _ : V ⊕ V ↦ α) A := by
  rw [mem_supportedOperators_iff] at hA
  rw [sitePermOp_mul_mul_conjTranspose]
  ext σ τ
  have hsymm (ρ : Config fun _ : V ⊕ V ↦ α) :
      (siteConfigurationEquiv (X := fun _ : V ⊕ V ↦ α) (X' := fun _ : V ⊕ V ↦ α)
        (replicaSwap S) fun _ ↦ Equiv.refl α).symm ρ = ρ ∘ replicaSwap S := by
    rw [Equiv.symm_apply_eq, siteConfigurationEquiv_refl_apply]
    funext w
    exact congrArg ρ (Equiv.apply_symm_apply _ w).symm
  rw [reindex_apply, submatrix_apply, hsymm, hsymm, inlOp_apply, inrOp_apply]
  simp only [Function.comp_apply]
  set π := replicaSwap S
  by_cases h₁ : (fun b ↦ σ (π (.inr b))) = fun b ↦ τ (π (.inr b)) <;>
    by_cases h₂ : (fun a ↦ σ (Sum.inl a)) = fun a ↦ τ (Sum.inl a) <;>
    simp only [h₁, h₂, ite_true, ite_false]
  · refine hA.2 (fun a ↦ σ (π (.inl a))) (fun a ↦ τ (π (.inl a))) (fun b ↦ σ (.inr b))
      (fun b ↦ τ (.inr b)) (fun v hv ↦ ?_) (fun v hv ↦ ?_) (fun v hv ↦ ?_) fun v hv ↦ ?_
    · change σ (π (.inl v)) = σ (.inr v)
      rw [replicaSwap_inl_of_mem hv]
    · change τ (π (.inl v)) = τ (.inr v)
      rw [replicaSwap_inl_of_mem hv]
    · change σ (π (.inl v)) = τ (π (.inl v))
      rw [replicaSwap_inl_of_notMem hv]
      exact congrFun h₂ v
    · have h := congrFun h₁ v
      simp only at h
      rwa [replicaSwap_inr_of_notMem hv] at h
  · obtain ⟨a, hne⟩ := Function.ne_iff.mp h₂
    by_cases ha : a ∈ S
    · have h := congrFun h₁ a
      simp only at h
      rw [replicaSwap_inr_of_mem ha] at h
      exact absurd h hne
    · refine hA.1 (fun a ↦ σ (π (.inl a))) (fun a ↦ τ (π (.inl a))) ⟨a, ha, ?_⟩
      change σ (π (.inl a)) ≠ τ (π (.inl a))
      rwa [replicaSwap_inl_of_notMem ha]
  · obtain ⟨b, hne⟩ := Function.ne_iff.mp h₁
    simp only at hne
    by_cases hb : b ∈ S
    · rw [replicaSwap_inr_of_mem hb] at hne
      exact absurd (congrFun h₂ b) hne
    · rw [replicaSwap_inr_of_notMem hb] at hne
      exact (hA.1 (fun b ↦ σ (.inr b)) (fun b ↦ τ (.inr b)) ⟨b, hb, hne⟩).symm

private theorem sitePermOp_replicaSwap_conj_doubled_self {S : Finset V}
    {A : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ}
    (hA : A ∈ supportedOperators (fun _ : V ↦ α) S) :
    sitePermOp (replicaSwap S) * (doubled A) * (sitePermOp (replicaSwap S))ᴴ = doubled A := by
  have hl := sitePermOp_replicaSwap_conj_inlOp hA
  have hr : sitePermOp (replicaSwap S) * inrOp (Z := fun _ : V ⊕ V ↦ α) A *
      (sitePermOp (replicaSwap S))ᴴ = inlOp (Z := fun _ : V ⊕ V ↦ α) A := by
    rw [← hl, conjTranspose_sitePermOp_replicaSwap, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      sitePermOp_replicaSwap_mul_self, Matrix.one_mul, Matrix.mul_assoc,
      sitePermOp_replicaSwap_mul_self, Matrix.mul_one]
  rw [Matrix.mul_add, Matrix.add_mul, hl, hr, add_comm]

/-- The doubled operator of an operator supported on `S` is supported on `S ⊔ S`. -/
theorem doubled_mem_supportedOperators {S : Finset V}
    {A : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ}
    (hA : A ∈ supportedOperators (fun _ : V ↦ α) S) :
    (doubled A) ∈ supportedOperators (fun _ : V ⊕ V ↦ α) (S.disjSum S) :=
  add_mem (supportedOperators_mono (Finset.disjSum_mono subset_rfl (Finset.empty_subset _))
      (inlOp_mem_supportedOperators hA))
    (supportedOperators_mono (Finset.disjSum_mono (Finset.empty_subset _) subset_rfl)
      (inrOp_mem_supportedOperators hA))

/-- **Exchanging replicas on a region acts on a doubled operator through its support.** For `A`
supported on `S`, conjugating `A ⊗ 1 + 1 ⊗ A` by the exchange on `R` equals conjugating it by
the exchange on `R ∩ S`. Polynomial PEPS approximation, `02-information.tex`,
lines 513–524. -/
theorem sitePermOp_replicaSwap_conj_doubled (R : Finset V) {S : Finset V}
    {A : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ}
    (hA : A ∈ supportedOperators (fun _ : V ↦ α) S) :
    sitePermOp (replicaSwap R) * (doubled A) * (sitePermOp (replicaSwap R))ᴴ =
      sitePermOp (replicaSwap (R ∩ S)) * (doubled A) *
        (sitePermOp (replicaSwap (R ∩ S)))ᴴ := by
  have hc : Commute (sitePermOp (α := α) (replicaSwap (R \ S))) (doubled A) :=
    commute_of_mem_supportedOperators_of_disjoint
      (sitePermOp_replicaSwap_mem_supportedOperators (R \ S))
      (doubled_mem_supportedOperators hA)
      (Finset.disjoint_left.mpr fun w hw hw' ↦ by
        rcases w with v | v <;> simp_all [Finset.mem_sdiff])
  have hb : sitePermOp (replicaSwap (R \ S)) * (doubled A) *
      (sitePermOp (α := α) (replicaSwap (R \ S)))ᴴ = doubled A := by
    rw [hc.eq, Matrix.mul_assoc, conjTranspose_sitePermOp_replicaSwap,
      sitePermOp_replicaSwap_mul_self, Matrix.mul_one]
  rw [replicaSwap_eq_mul R S, ← sitePermOp_mul, conjTranspose_mul]
  calc _ = sitePermOp (replicaSwap (R ∩ S)) * (sitePermOp (replicaSwap (R \ S)) * (doubled A) *
        (sitePermOp (α := α) (replicaSwap (R \ S)))ᴴ) * (sitePermOp (replicaSwap (R ∩ S)))ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hb]

/-- Exchanging the replicas on a region containing the support of `A` leaves its doubled
operator unchanged. -/
theorem sitePermOp_replicaSwap_conj_doubled_of_subset {R S : Finset V} (hSR : S ⊆ R)
    {A : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ}
    (hA : A ∈ supportedOperators (fun _ : V ↦ α) S) :
    sitePermOp (replicaSwap R) * (doubled A) * (sitePermOp (replicaSwap R))ᴴ = doubled A := by
  rw [sitePermOp_replicaSwap_conj_doubled R hA, Finset.inter_eq_right.mpr hSR,
    sitePermOp_replicaSwap_conj_doubled_self hA]

/-- Exchanging the replicas on a region disjoint from the support of `A` leaves its doubled
operator unchanged. -/
theorem sitePermOp_replicaSwap_conj_doubled_of_disjoint {R S : Finset V} (hSR : Disjoint S R)
    {A : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ}
    (hA : A ∈ supportedOperators (fun _ : V ↦ α) S) :
    sitePermOp (replicaSwap R) * (doubled A) * (sitePermOp (replicaSwap R))ᴴ = doubled A := by
  rw [sitePermOp_replicaSwap_conj_doubled R hA,
    Finset.disjoint_iff_inter_eq_empty.mp hSR.symm, replicaSwap_empty, sitePermOp_one,
    conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- The conjugated doubled operator stays supported on `S ⊔ S`. -/
theorem sitePermOp_replicaSwap_conj_doubled_mem_supportedOperators (R : Finset V)
    {S : Finset V} {A : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ}
    (hA : A ∈ supportedOperators (fun _ : V ↦ α) S) :
    sitePermOp (replicaSwap R) * (doubled A) * (sitePermOp (replicaSwap R))ᴴ ∈
      supportedOperators (fun _ : V ⊕ V ↦ α) (S.disjSum S) := by
  have h := sitePermOp_mul_mul_conjTranspose_mem_supportedOperators (replicaSwap R)
    (doubled_mem_supportedOperators hA)
  have himage : (S.disjSum S).image (replicaSwap R) = S.disjSum S := by
    ext w
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨w', hw', rfl⟩
      rcases w' with v | v <;> by_cases hv : v ∈ R <;> simp_all
    · intro hw
      refine ⟨replicaSwap R w, ?_, ?_⟩
      · rcases w with v | v <;> by_cases hv : v ∈ R <;> simp_all
      · exact replicaSwapFun_involutive R w
  rwa [himage] at h

end ManyBody
