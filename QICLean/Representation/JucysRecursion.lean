/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.StarOperator
import QICLean.Representation.RegularTrace

/-!
# The fixed-point sum of the copy permutations

Let `Z_k = ∑_{τ ∈ S_k} f(τ) τ ∈ ℂ[S_k]`, where `f(τ)` is the number of configurations
`x : Fin k → Fin q` fixed by `τ`, the trace of `τ` on `(ℂ^q)^{⊗k}`. Every permutation of
`m + 1` copies is uniquely either a permutation `σ` of the first `m` copies or `(j, m+1) σ`,
and the fixed configurations of these are `q f(σ)` and `f(σ)` in number. Hence

`Z_{m+1} = (q + X_{m+1}) Z_m`,

with `X_{m+1}` the Jucys–Murphy element. This is Jucys' factorization of the fixed-point
sum, used with the character projection to compute the multiplicity spaces of Lemma 6.1(1)
of the area-law paper (*A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, equation `replicas:dimensions`).

## Main declarations

* `TensorPower.fixCount q τ`, `TensorPower.fixSum q k`.
* `TensorPower.fixSum_succ` — `Z_{m+1} = (q + X_{m+1}) Z_m`.
-/

open Finset PermutationRepresentation MonoidAlgebra

namespace TensorPower

variable {q m k : ℕ}

variable (q) in
/-- The number of configurations fixed by a permutation of the copies. -/
def fixCount (τ : Equiv.Perm (Fin k)) : ℕ := #(univ.filter fun x : Fin k → Fin q => x ∘ τ = x)

variable (q k) in
/-- The fixed-point sum `Z_k = ∑_τ f(τ) τ`. -/
noncomputable def fixSum : MonoidAlgebra ℂ (Equiv.Perm (Fin k)) :=
  ∑ τ, (fixCount q τ : ℂ) • single τ 1

theorem trace_permOp_inv (τ : Equiv.Perm (Fin k)) :
    (groupAlgebraRep (copyPerm (Fin q) k) (single τ⁻¹ 1)).trace = fixCount q τ := by
  rw [groupAlgebraRep_single, one_smul, Matrix.trace, fixCount, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, permOp_apply_apply]
  have e : (copyPerm (Fin q) k τ⁻¹) x = x ∘ τ := by
    funext j; rw [copyPerm_apply, inv_inv]; rfl
  rw [e]
  split_ifs <;> simp

/-- The fixed-point sum is the character sum of `(ℂ^q)^{⊗k}`. -/
theorem fixSum_eq_characterSum :
    fixSum q k = ∑ τ, (groupAlgebraRep (copyPerm (Fin q) k) (single τ⁻¹ 1)).trace •
      single τ (1 : ℂ) := by
  simp only [fixSum, trace_permOp_inv]

/-- Permutations of `m + 1` copies as `σ` or `(j, m+1) σ` with `σ` a permutation of the
first `m` copies. -/
def decomp (p : Option (Fin m)) (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  p.elim 1 (fun j => Equiv.swap (Fin.castSucc j) (Fin.last m)) * firstCopies m σ

theorem decomp_last (p : Option (Fin m)) (σ : Equiv.Perm (Fin m)) :
    decomp p σ (Fin.last m) = p.elim (Fin.last m) Fin.castSucc := by
  cases p <;> simp [decomp, firstCopies_last]

theorem firstCopies_injective : Function.Injective (firstCopies m) := by
  intro σ τ h
  have := youngHom_injective (finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)) h
  simpa using this

theorem decomp_injective :
    Function.Injective fun x : Option (Fin m) × Equiv.Perm (Fin m) => decomp x.1 x.2 := by
  rintro ⟨p, σ⟩ ⟨p', σ'⟩ h
  simp only at h
  have hp : p = p' := by
    have := congrArg (fun τ : Equiv.Perm (Fin (m + 1)) => τ (Fin.last m)) h
    simp only [decomp_last] at this
    cases p <;> cases p' <;> simp_all [Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  subst hp
  simp only [decomp, mul_right_inj] at h
  rw [firstCopies_injective h]

theorem decomp_bijective :
    Function.Bijective fun x : Option (Fin m) × Equiv.Perm (Fin m) => decomp x.1 x.2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨decomp_injective, ?_⟩
  simp [Fintype.card_perm, Nat.factorial_succ]

theorem card_filter_snoc (P : (Fin (m + 1) → Fin q) → Prop) [DecidablePred P] :
    #(univ.filter P) = ∑ c : Fin q, #(univ.filter fun y : Fin m → Fin q => P (Fin.snoc y c)) := by
  rw [card_filter, ← (Fin.snocEquiv fun _ => Fin q).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun c _ => ?_
  rw [card_filter]
  rfl

theorem snoc_comp_firstCopies (y : Fin m → Fin q) (c : Fin q) (σ : Equiv.Perm (Fin m)) :
    (Fin.snoc y c : Fin (m + 1) → Fin q) ∘ firstCopies m σ = Fin.snoc (y ∘ σ) c := by
  funext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [firstCopies_last]
  · simp [firstCopies_castSucc]

theorem snoc_comp_decomp_some (y : Fin m → Fin q) (c : Fin q) (j : Fin m)
    (σ : Equiv.Perm (Fin m)) :
    (Fin.snoc y c : Fin (m + 1) → Fin q) ∘ decomp (some j) σ =
      Fin.snoc (Function.update y j c ∘ σ) (y j) := by
  funext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [decomp, firstCopies_last]
  · simp only [decomp, Option.elim_some, Function.comp_apply, Equiv.Perm.mul_apply,
      firstCopies_castSucc, Fin.snoc_castSucc]
    by_cases h : σ i' = j
    · rw [h, Equiv.swap_apply_left]; simp
    · rw [Equiv.swap_apply_of_ne_of_ne (fun e => h (Fin.castSucc_injective m e))
        (Fin.castSucc_ne_last _), Fin.snoc_castSucc, Function.update_of_ne h]

theorem snoc_eq_snoc_iff {a b : Fin m → Fin q} {c d : Fin q} :
    (Fin.snoc a c : Fin (m + 1) → Fin q) = Fin.snoc b d ↔ a = b ∧ c = d := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg Fin.init h, by simpa using congrFun h (Fin.last m)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem fixCount_decomp_none (σ : Equiv.Perm (Fin m)) :
    fixCount q (decomp none σ) = q * fixCount q σ := by
  rw [fixCount, card_filter_snoc]
  simp only [decomp, Option.elim_none, one_mul, snoc_comp_firstCopies, snoc_eq_snoc_iff,
    and_true]
  simp [fixCount]

theorem fixCount_decomp_some (j : Fin m) (σ : Equiv.Perm (Fin m)) :
    fixCount q (decomp (some j) σ) = fixCount q σ := by
  rw [fixCount, card_filter_snoc]
  simp only [snoc_comp_decomp_some, snoc_eq_snoc_iff]
  have : ∀ c : Fin q, (univ.filter fun y : Fin m → Fin q =>
      Function.update y j c ∘ σ = y ∧ y j = c) =
      (univ.filter fun y : Fin m → Fin q => y ∘ σ = y ∧ y j = c) := by
    intro c
    ext y
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨by simpa using h1, rfl⟩
    · rintro ⟨h1, rfl⟩; exact ⟨by simpa using h1, rfl⟩
  simp only [this]
  rw [fixCount, ← card_biUnion]
  · congr 1
    ext y
    simp
  · intro c _ d _ hcd
    simp only [Function.onFun, disjoint_left, mem_filter, mem_univ, true_and]
    rintro y ⟨-, rfl⟩ ⟨-, h⟩
    exact hcd h

/-- **Jucys factorization of the fixed-point sum**: `Z_{m+1} = (q + X_{m+1}) Z_m`, with `Z_m`
embedded through the permutations of the first `m` copies. -/
theorem fixSum_succ :
    fixSum q (m + 1) = ((q : ℂ) • 1 + IrrepLabel.starElement m) *
      IrrepLabel.restrictHom (firstCopies m) (fixSum q m) := by
  have hL : fixSum q (m + 1) = ∑ x : Option (Fin m) × Equiv.Perm (Fin m),
      (fixCount q (decomp x.1 x.2) : ℂ) • single (decomp x.1 x.2) 1 :=
    (Function.Bijective.sum_comp decomp_bijective
      (fun τ => (fixCount q τ : ℂ) • single τ (1 : ℂ))).symm
  rw [hL, Fintype.sum_prod_type, Fintype.sum_option]
  simp only [fixCount_decomp_none, fixCount_decomp_some, fixSum, map_sum, map_smul,
    IrrepLabel.restrictHom, mapDomainAlgHom_apply, mapDomain_single, mul_sum, add_mul,
    smul_mul_assoc, one_mul, IrrepLabel.starElement, sum_mul, single_mul_single, mul_one,
    mul_smul_comm]
  simp only [smul_add, smul_sum, sum_add_distrib]
  congr 1
  · refine sum_congr rfl fun σ _ => ?_
    rw [smul_smul]
    simp [decomp, mul_comm]
  · rw [sum_comm]
    refine sum_congr rfl fun j _ => sum_congr rfl fun σ _ => ?_
    simp [decomp]

end TensorPower
