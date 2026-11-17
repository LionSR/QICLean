/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.RegionExpectation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NoncommRing

/-!
# Localization error of the region expectation

If an operator `B` almost commutes with every unitary acting on a single site `y` outside a
region `K`, with commutator norm at most `ε y`, then `B` is close to its expectation onto `K`:
`‖B - E_K(B)‖ ≤ ∑_{y ∉ K} ε y`. Nothing depends on the local dimensions.

The proof writes the region expectation as an average of conjugations by products of on-site
unitaries, and telescopes the product. The on-site unitaries are the signed translations of a
basis: for a finite type `n` enumerated as `Fin N`, the operators `|i⟩ ↦ ±|i + k⟩`, with an
independent sign at every basis vector. Averaging the conjugation by them sends a matrix to its
normalized trace (a unitary 1-design), so it needs no arithmetic on the basis type itself.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, proof of Lemma 4.1
(`03-quasilocal.tex`, lines 117–124), where the expectation is written as a product of
commuting on-site twirls and the product is telescoped.

TNLean's `TNLean/Circuit/SiteExpectation.lean` (commit
`71c1185e9352a3b5237b37a6840640751da6ca2d`) proves the same bound for one local dimension
`Fin q` with Weyl operators on `ZMod q`; here the basis types are arbitrary, so the twirl is
over signed translations, and the expectation is `ManyBody.regionExpectation`.

## Main results

* `ManyBody.regionExpectation_eq_average` — the region expectation is an average of
  conjugations by products of on-site unitaries.
* `ManyBody.norm_sub_regionExpectation_le` — the localization error through on-site
  commutators.
* `ManyBody.mem_supportedOperators_iff_forall_commute` — the operators supported on a region
  are exactly those commuting with every operator supported on its complement.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace ManyBody

/-! ### Signed translations of a finite basis -/

section Design

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The labels of the signed translations of the basis `n`: a sign at every basis vector and a
translation of the enumeration of `n`. -/
private abbrev Label (n : Type*) [Fintype n] := (n → Bool) × Fin (Fintype.card n)

/-- The sign `±1` of a Boolean. -/
private def sgn (b : Bool) : ℂ := if b then -1 else 1

private theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

private theorem star_sgn (b : Bool) : star (sgn b) = sgn b := by
  cases b <;> simp [sgn]

/-- The signed translation with label `l`: it maps the basis vector `j` to `± i`, where `i` is
`j` translated by `l.2` in the enumeration of `n`, with the sign `l.1 i`. -/
private noncomputable def signedShift (l : Label n) : Matrix n n ℂ :=
  Matrix.of fun i j ↦
    if Fintype.equivFin n i = Fintype.equivFin n j + l.2 then sgn (l.1 i) else 0

omit [DecidableEq n] in
/-- Translating the enumeration is injective: `i` is the translate of at most one `j`. -/
private theorem eq_of_shift_eq {i j j' : n} {k : Fin (Fintype.card n)}
    (h : Fintype.equivFin n i = Fintype.equivFin n j + k)
    (h' : Fintype.equivFin n i = Fintype.equivFin n j' + k) : j = j' := by
  have : Nonempty n := ⟨i⟩
  have : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  exact (Fintype.equivFin n).injective (add_right_cancel (h.symm.trans h'))

omit [DecidableEq n] in
/-- Each basis vector `i` is the translate of exactly one `j`. -/
private theorem exists_shift_eq (i : n) (k : Fin (Fintype.card n)) :
    ∃ j, Fintype.equivFin n i = Fintype.equivFin n j + k := by
  have : Nonempty n := ⟨i⟩
  have : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
  exact ⟨(Fintype.equivFin n).symm (Fintype.equivFin n i - k), by simp⟩

/-- A signed translation is unitary. -/
private theorem signedShift_mul_star (l : Label n) : signedShift l * star (signedShift l) = 1 := by
  ext i i'
  rw [Matrix.mul_apply, Matrix.one_apply]
  obtain ⟨j₀, hj₀⟩ := exists_shift_eq i l.2
  rw [Finset.sum_eq_single j₀ (fun j _ hj ↦ ?_) (fun h ↦ absurd (Finset.mem_univ _) h)]
  · simp only [signedShift, Matrix.star_apply, Matrix.of_apply, ite_eq_left hj₀]
    by_cases hii' : i = i'
    · subst hii'
      rw [ite_eq_left hj₀, ite_eq_left rfl, star_sgn, sgn_mul_self]
    · rw [ite_eq_right hii']
      split_ifs with h'
      · exact absurd ((Fintype.equivFin n).injective (hj₀.trans h'.symm)) hii'
      · simp
  · simp only [signedShift, Matrix.star_apply, Matrix.of_apply]
    rw [ite_eq_right (fun h ↦ hj (eq_of_shift_eq h hj₀)), zero_mul]

private theorem signedShift_mem_unitary (l : Label n) :
    signedShift l ∈ unitary (Matrix n n ℂ) :=
  Matrix.mem_unitaryGroup_iff.mpr (signedShift_mul_star l)

/-- A sum of products of two signs over all sign vectors vanishes unless the two positions
coincide. -/
private theorem sum_sgn_mul_sgn (i i' : n) :
    ∑ s : n → Bool, sgn (s i) * sgn (s i') =
      if i = i' then (Fintype.card (n → Bool) : ℂ) else 0 := by
  split_ifs with h
  · subst h
    simp [sgn_mul_self]
  · -- Flipping the sign at `i` negates every term.
    let e : (n → Bool) ≃ (n → Bool) :=
      { toFun := fun s ↦ Function.update s i (!s i)
        invFun := fun s ↦ Function.update s i (!s i)
        left_inv := fun s ↦ by ext x; by_cases hx : x = i <;> simp [hx]
        right_inv := fun s ↦ by ext x; by_cases hx : x = i <;> simp [hx] }
    have hneg : ∀ s, sgn (e s i) * sgn (e s i') = -(sgn (s i) * sgn (s i')) := by
      intro s
      simp only [e, Equiv.coe_fn_mk, Function.update_self,
        Function.update_of_ne (Ne.symm h)]
      generalize s i = a
      generalize s i' = b
      cases a <;> cases b <;> simp [sgn]
    have hsum := e.sum_comp fun s ↦ sgn (s i) * sgn (s i')
    simp only [hneg, Finset.sum_neg_distrib] at hsum
    linear_combination (-(1 : ℂ) / 2) * hsum

/-- The signed translations form a unitary 1-design: the average of
`U_{ij} conj(U_{i'j'})` over all labels is `δ_{ii'} δ_{jj'} / N`. -/
private theorem sum_signedShift_mul_star (i j i' j' : n) :
    ∑ l : Label n, signedShift l i j * star (signedShift l i' j') =
      if i = i' ∧ j = j' then (Fintype.card (n → Bool) : ℂ) else 0 := by
  have hterm (s : n → Bool) (k : Fin (Fintype.card n)) :
      signedShift (s, k) i j * star (signedShift (s, k) i' j') =
        (if Fintype.equivFin n i = Fintype.equivFin n j + k ∧
            Fintype.equivFin n i' = Fintype.equivFin n j' + k then 1 else 0) *
          (sgn (s i) * sgn (s i')) := by
    simp only [signedShift, Matrix.of_apply]
    split_ifs <;> simp_all [star_sgn]
  rw [Fintype.sum_prod_type]
  simp only [hterm]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, sum_sgn_mul_sgn]
  by_cases hii' : i = i'
  · subst hii'
    have : Nonempty n := ⟨i⟩
    have : NeZero (Fintype.card n) := ⟨Fintype.card_ne_zero⟩
    by_cases hjj' : j = j'
    · subst hjj'
      simp only [and_self, ← sub_eq_iff_eq_add', Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, one_mul]
    · have hzero : ∀ k : Fin (Fintype.card n),
          ¬(Fintype.equivFin n i = Fintype.equivFin n j + k ∧
            Fintype.equivFin n i = Fintype.equivFin n j' + k) :=
        fun k h ↦ hjj' (eq_of_shift_eq h.1 h.2)
      simp [hzero, hjj']
  · simp [hii']

end Design

/-! ### Products of on-site matrices -/

section Product

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- The signed translation with label `l` at a site `v` of `M`, the identity elsewhere. -/
private noncomputable def siteFactor (M : Finset V) (v : V) (l : Label (X v)) :
    Matrix (X v) (X v) ℂ :=
  if v ∈ M then signedShift l else 1

/-- The product of the signed translations `g v` at the sites `v` of `M`, and of the identity
at the other sites. -/
private noncomputable def shiftOp (M : Finset V) (g : (v : V) → Label (X v)) :
    Matrix (Config X) (Config X) ℂ :=
  prodOp fun v ↦ siteFactor M v (g v)

private theorem shiftOp_mem_unitary (M : Finset V) (g : (v : V) → Label (X v)) :
    shiftOp M g ∈ unitary (Matrix (Config X) (Config X) ℂ) := by
  refine prodOp_mem_unitary fun v ↦ ?_
  unfold siteFactor
  split_ifs
  · exact signedShift_mem_unitary _
  · exact one_mem _

private theorem shiftOp_singleton_mem_supportedOperators (y : V) (g : (v : V) → Label (X v)) :
    shiftOp {y} g ∈ supportedOperators X {y} :=
  prodOp_mem_supportedOperators fun _ hv ↦ ite_eq_right hv

private theorem shiftOp_insert {M : Finset V} {y : V} (hy : y ∉ M)
    (g : (v : V) → Label (X v)) :
    shiftOp (insert y M) g = shiftOp {y} g * shiftOp M g := by
  rw [shiftOp, shiftOp, shiftOp, prodOp_mul]
  congr 1
  funext v
  unfold siteFactor
  by_cases hvy : v = y
  · subst hvy
    simp [hy]
  · by_cases hvM : v ∈ M <;> simp [hvy, hvM]

private theorem shiftOp_empty (g : (v : V) → Label (X v)) : shiftOp ∅ g = 1 := by
  simp [shiftOp, siteFactor]

/-- The commutator with a product of two unitaries is at most the sum of the commutators. -/
private theorem norm_commutator_mul_le (B U W : Matrix (Config X) (Config X) ℂ)
    (hU : U ∈ unitary (Matrix (Config X) (Config X) ℂ))
    (hW : W ∈ unitary (Matrix (Config X) (Config X) ℂ)) :
    ‖B * (U * W) - U * W * B‖ ≤ ‖B * U - U * B‖ + ‖B * W - W * B‖ := by
  have h : B * (U * W) - U * W * B = (B * U - U * B) * W + U * (B * W - W * B) := by
    noncomm_ring
  rw [h]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [CStarRing.norm_mul_mem_unitary _ hW, CStarRing.norm_mem_unitary_mul _ hU]

/-- Telescoping: the commutator with a product of on-site unitaries over `M` is at most the
sum of the on-site commutators. -/
private theorem norm_commutator_shiftOp_le (B : Matrix (Config X) (Config X) ℂ) (ε : V → ℝ)
    (g : (v : V) → Label (X v)) (M : Finset V)
    (hε : ∀ y ∈ M, ∀ U ∈ supportedOperators X {y},
      U ∈ unitary (Matrix (Config X) (Config X) ℂ) → ‖B * U - U * B‖ ≤ ε y) :
    ‖B * shiftOp M g - shiftOp M g * B‖ ≤ ∑ y ∈ M, ε y := by
  induction M using Finset.induction_on with
  | empty => simp [shiftOp_empty]
  | insert y M hy ih =>
    rw [shiftOp_insert hy, Finset.sum_insert hy]
    refine (norm_commutator_mul_le B _ _ (shiftOp_mem_unitary _ g)
      (shiftOp_mem_unitary _ g)).trans (add_le_add ?_ ?_)
    · exact hε y (Finset.mem_insert_self y M) _ (shiftOp_singleton_mem_supportedOperators y g)
        (shiftOp_mem_unitary _ g)
    · exact ih fun z hz ↦ hε z (Finset.mem_insert_of_mem hz)

end Product

/-! ### The region expectation as an average of conjugations -/

section Average

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- The constant of the average over one site. -/
private noncomputable def siteWeight (M : Finset V) (v : V) : ℂ :=
  if v ∈ M then (Fintype.card (X v → Bool) : ℂ) else (Fintype.card (Label (X v)) : ℂ)

/-- The constraint of the average over one site: at a site of `M` the two rows and the two
columns agree; elsewhere each row agrees with its column. -/
private def SiteConstraint (M : Finset V) (v : V) (a b c d : X v) : Prop :=
  if v ∈ M then a = c ∧ b = d else a = b ∧ c = d

private instance (M : Finset V) (v : V) (a b c d : X v) :
    Decidable (SiteConstraint M v a b c d) := by
  unfold SiteConstraint; infer_instance

omit [Fintype V] in
/-- The average over one site. -/
private theorem sum_siteFactor (M : Finset V) (v : V) (a b c d : X v) :
    ∑ l : Label (X v), siteFactor M v l a b * star (siteFactor M v l c d) =
      siteWeight (X := X) M v * if SiteConstraint M v a b c d then 1 else 0 := by
  unfold siteFactor siteWeight SiteConstraint
  by_cases hv : v ∈ M
  · simp only [hv, ite_true]
    rw [sum_signedShift_mul_star]
    split_ifs <;> simp
  · simp only [hv, ite_false, Matrix.one_apply, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    by_cases hab : a = b <;> by_cases hcd : c = d <;> simp [hab, hcd]

/-- The average over all labels of a product of entries of the on-site products. -/
private theorem sum_shiftOp_mul_star (M : Finset V) (σ ρ τ ρ' : Config X) :
    ∑ g : (v : V) → Label (X v), shiftOp M g σ ρ * star (shiftOp M g τ ρ') =
      (∏ v, siteWeight (X := X) M v) *
        if ∀ v, SiteConstraint M v (σ v) (ρ v) (τ v) (ρ' v) then 1 else 0 := by
  calc
    _ = ∑ g : (v : V) → Label (X v), ∏ v,
          siteFactor M v (g v) (σ v) (ρ v) * star (siteFactor M v (g v) (τ v) (ρ' v)) := by
      refine Finset.sum_congr rfl fun g _ ↦ ?_
      simp only [shiftOp, prodOp, Matrix.of_apply, star_prod, Finset.prod_mul_distrib]
    _ = ∏ v, ∑ l : Label (X v),
          siteFactor M v l (σ v) (ρ v) * star (siteFactor M v l (τ v) (ρ' v)) :=
      (Fintype.prod_sum fun (v : V) (l : Label (X v)) ↦
        siteFactor M v l (σ v) (ρ v) * star (siteFactor M v l (τ v) (ρ' v))).symm
    _ = _ := by simp only [sum_siteFactor, Finset.prod_mul_distrib, Fintype.prod_boole]

omit [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- The constraint of the average over all sites outside `K`: it fixes the column `ρ'` in terms
of `ρ`, and fixes `ρ` up to its part outside `K`. -/
private theorem forall_siteConstraint_iff (K : Finset V) (σ ρ τ ρ' : Config X) :
    (∀ v, SiteConstraint Kᶜ v (σ v) (ρ v) (τ v) (ρ' v)) ↔
      (∀ v ∉ K, σ v = τ v) ∧ (cutEquiv X K ρ).1 = (cutEquiv X K σ).1 ∧
        ρ' = (cutEquiv X K).symm ((cutEquiv X K τ).1, (cutEquiv X K ρ).2) := by
  simp only [SiteConstraint, Finset.mem_compl]
  constructor
  · intro h
    have hin (v : V) (hv : v ∈ K) : σ v = ρ v ∧ τ v = ρ' v := by
      simpa [hv] using h v
    have hout (v : V) (hv : v ∉ K) : σ v = τ v ∧ ρ v = ρ' v := by
      simpa [hv] using h v
    refine ⟨fun v hv ↦ (hout v hv).1, ?_, funext fun v ↦ ?_⟩
    · exact cutEquiv_fst_eq_iff.mpr fun v hv ↦ (hin v hv).1.symm
    · by_cases hv : v ∈ K
      · rw [cutEquiv_symm_apply_mem _ _ hv]
        exact (hin v hv).2.symm
      · rw [cutEquiv_symm_apply_not_mem _ _ hv]
        exact (hout v hv).2.symm
  · rintro ⟨h₁, h₂, rfl⟩ v
    by_cases hv : v ∈ K
    · simp only [hv, not_true_eq_false, ite_false]
      refine ⟨(cutEquiv_fst_eq_iff.mp h₂ v hv).symm, ?_⟩
      rw [cutEquiv_symm_apply_mem _ _ hv]
      rfl
    · simp only [hv, not_false_eq_true, ite_true]
      refine ⟨h₁ v hv, ?_⟩
      rw [cutEquiv_symm_apply_not_mem _ _ hv]
      rfl

private theorem sum_shiftOp_compl_mul_star (K : Finset V) (σ ρ τ ρ' : Config X) :
    ∑ g : (v : V) → Label (X v), shiftOp Kᶜ g σ ρ * star (shiftOp Kᶜ g τ ρ') =
      (∏ v, siteWeight (X := X) Kᶜ v) *
        if (∀ v ∉ K, σ v = τ v) ∧ (cutEquiv X K ρ).1 = (cutEquiv X K σ).1 ∧
          ρ' = (cutEquiv X K).symm ((cutEquiv X K τ).1, (cutEquiv X K ρ).2) then 1 else 0 := by
  rw [sum_shiftOp_mul_star]
  exact congrArg _ (if_congr (forall_siteConstraint_iff K σ ρ τ ρ') rfl rfl)

/-- The average of the conjugations, entrywise: up to a constant, the entries of the region
expectation. -/
private theorem sum_shiftOp_conj_apply (K : Finset V) (B : Matrix (Config X) (Config X) ℂ)
    (σ τ : Config X) :
    (∑ g : (v : V) → Label (X v), shiftOp Kᶜ g * B * star (shiftOp Kᶜ g)) σ τ =
      (∏ v, siteWeight (X := X) Kᶜ v) *
        if ∀ v ∉ K, σ v = τ v then
          ∑ y : ComplConfig X K, B ((cutEquiv X K).symm ((cutEquiv X K σ).1, y))
            ((cutEquiv X K).symm ((cutEquiv X K τ).1, y))
        else 0 := by
  -- Exchange the average with the two matrix sums.
  have hexpand : (∑ g : (v : V) → Label (X v), shiftOp Kᶜ g * B * star (shiftOp Kᶜ g)) σ τ =
      ∑ ρ : Config X, ∑ ρ' : Config X, B ρ ρ' *
        ∑ g : (v : V) → Label (X v), shiftOp Kᶜ g σ ρ * star (shiftOp Kᶜ g τ ρ') := by
    rw [Matrix.sum_apply]
    calc
      _ = ∑ g : (v : V) → Label (X v), ∑ ρ : Config X, ∑ ρ' : Config X,
            B ρ ρ' * (shiftOp Kᶜ g σ ρ * star (shiftOp Kᶜ g τ ρ')) := by
        refine Finset.sum_congr rfl fun g _ ↦ ?_
        simp only [Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ρ _ ↦ Finset.sum_congr rfl fun ρ' _ ↦ by ring
      _ = ∑ ρ : Config X, ∑ ρ' : Config X, ∑ g : (v : V) → Label (X v),
            B ρ ρ' * (shiftOp Kᶜ g σ ρ * star (shiftOp Kᶜ g τ ρ')) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ρ _ ↦ Finset.sum_comm
      _ = _ := by simp only [Finset.mul_sum]
  rw [hexpand]
  refine (Finset.sum_congr rfl fun ρ _ ↦ Finset.sum_congr rfl fun ρ' _ ↦
    congrArg (B ρ ρ' * ·) (sum_shiftOp_compl_mul_star K σ ρ τ ρ')).trans ?_
  by_cases hστ : ∀ v ∉ K, σ v = τ v
  · simp only [eq_true hστ, true_and, ite_true]
    rw [Finset.mul_sum]
    -- Sum out `ρ'`, then reindex `ρ` by its cut.
    have hinner (ρ : Config X) :
        ∑ ρ' : Config X, B ρ ρ' * ((∏ v, siteWeight (X := X) Kᶜ v) *
          if (cutEquiv X K ρ).1 = (cutEquiv X K σ).1 ∧
            ρ' = (cutEquiv X K).symm ((cutEquiv X K τ).1, (cutEquiv X K ρ).2) then 1 else 0) =
        if (cutEquiv X K ρ).1 = (cutEquiv X K σ).1 then
          (∏ v, siteWeight (X := X) Kᶜ v) *
            B ρ ((cutEquiv X K).symm ((cutEquiv X K τ).1, (cutEquiv X K ρ).2))
        else 0 := by
      split_ifs with hρ
      · simp only [hρ, true_and, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ite_true]
        ring
      · simp only [eq_false hρ, false_and, ite_false, mul_zero, Finset.sum_const_zero]
    simp only [hinner]
    rw [← (cutEquiv X K).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.apply_symm_apply]
    rw [Finset.sum_eq_single (cutEquiv X K σ).1 (fun a _ ha ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ _) h)]
    · simp
    · exact Finset.sum_eq_zero fun y _ ↦ ite_eq_right ha
  · simp [eq_false hστ]

/-- The region expectation is the average of the conjugations by the products of signed
translations at the sites outside the region. -/
private theorem regionExpectation_eq_average [Nonempty (Config X)] (K : Finset V)
    (B : Matrix (Config X) (Config X) ℂ) :
    regionExpectation K B = (Fintype.card ((v : V) → Label (X v)) : ℂ)⁻¹ •
      ∑ g : (v : V) → Label (X v), shiftOp Kᶜ g * B * star (shiftOp Kᶜ g) := by
  obtain ⟨σ₀⟩ := ‹Nonempty (Config X)›
  have : Nonempty (ComplConfig X K) := ⟨fun v ↦ σ₀ v⟩
  have hd : (Fintype.card (ComplConfig X K) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  set c : ℂ := ∏ v, siteWeight (X := X) Kᶜ v
  -- Up to the constant `c |X_{V∖K}|`, the average is the region expectation.
  have hsum (A : Matrix (Config X) (Config X) ℂ) :
      ∑ g : (v : V) → Label (X v), shiftOp Kᶜ g * A * star (shiftOp Kᶜ g) =
        (c * Fintype.card (ComplConfig X K)) • regionExpectation K A := by
    ext σ τ
    rw [sum_shiftOp_conj_apply, Matrix.smul_apply, regionExpectation_apply, smul_eq_mul,
      mul_assoc, ← mul_assoc (Fintype.card (ComplConfig X K) : ℂ), mul_inv_cancel₀ hd,
      one_mul]
  -- Evaluating at the identity identifies the constant.
  have hone := hsum 1
  simp only [Matrix.mul_one, fun g ↦ Unitary.mul_star_self_of_mem (shiftOp_mem_unitary Kᶜ g),
    Finset.sum_const, Finset.card_univ, regionExpectation_one] at hone
  have hconst : (Fintype.card ((v : V) → Label (X v)) : ℂ) =
      c * Fintype.card (ComplConfig X K) := by
    have h := congrFun (congrFun hone σ₀) σ₀
    simpa [Matrix.smul_apply, Matrix.one_apply_eq, ← Nat.cast_smul_eq_nsmul ℂ] using h
  have hN : (c * Fintype.card (ComplConfig X K) : ℂ) ≠ 0 := by
    rw [← hconst]
    have : ∀ v, Nonempty (X v) := fun v ↦ ⟨σ₀ v⟩
    have : ∀ v, Nonempty (Label (X v)) := fun v ↦
      ⟨(fun _ ↦ false, ⟨0, Fintype.card_pos⟩)⟩
    exact_mod_cast Fintype.card_ne_zero
  rw [hsum, hconst, smul_smul, inv_mul_cancel₀ hN, one_smul]

/-- **Localization error through on-site commutators.** If, for every site `y` outside `K`,
the commutator of `B` with every unitary supported on `{y}` has norm at most `ε y`, then
`‖B - E_K(B)‖ ≤ ∑_{y ∉ K} ε y`. Source: OpenAI area law, proof of Lemma 4.1
(`03-quasilocal.tex`, lines 117–124), where the expectation is written as a product of
commuting on-site twirls and the product is telescoped. -/
theorem norm_sub_regionExpectation_le (K : Finset V) (B : Matrix (Config X) (Config X) ℂ)
    (ε : V → ℝ)
    (hε : ∀ y ∉ K, ∀ U ∈ supportedOperators X {y},
      U ∈ unitary (Matrix (Config X) (Config X) ℂ) → ‖B * U - U * B‖ ≤ ε y) :
    ‖B - regionExpectation K B‖ ≤ ∑ y ∈ Kᶜ, ε y := by
  rcases isEmpty_or_nonempty (Config X) with hX | hX
  · rw [Subsingleton.elim (B - regionExpectation K B) 0, norm_zero]
    refine Finset.sum_nonneg fun y hy ↦ (norm_nonneg (B * 1 - 1 * B)).trans ?_
    exact hε y (Finset.mem_compl.mp hy) 1 (one_mem _) (one_mem _)
  · have hN : (Fintype.card ((v : V) → Label (X v)) : ℂ) ≠ 0 := by
      obtain ⟨σ₀⟩ := hX
      have : ∀ v, Nonempty (X v) := fun v ↦ ⟨σ₀ v⟩
      have : ∀ v, Nonempty (Label (X v)) := fun v ↦
        ⟨(fun _ ↦ false, ⟨0, Fintype.card_pos⟩)⟩
      exact_mod_cast Fintype.card_ne_zero
    have hg (g : (v : V) → Label (X v)) :
        (B * shiftOp Kᶜ g - shiftOp Kᶜ g * B) * star (shiftOp Kᶜ g) =
          B - shiftOp Kᶜ g * B * star (shiftOp Kᶜ g) := by
      rw [sub_mul, mul_assoc B, Unitary.mul_star_self_of_mem (shiftOp_mem_unitary Kᶜ g),
        mul_one]
    have hdiff : B - regionExpectation K B =
        (Fintype.card ((v : V) → Label (X v)) : ℂ)⁻¹ • ∑ g : (v : V) → Label (X v),
          (B * shiftOp Kᶜ g - shiftOp Kᶜ g * B) * star (shiftOp Kᶜ g) := by
      rw [regionExpectation_eq_average, Finset.sum_congr rfl fun g _ ↦ hg g,
        Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]
    have hterm (g : (v : V) → Label (X v)) :
        ‖(B * shiftOp Kᶜ g - shiftOp Kᶜ g * B) * star (shiftOp Kᶜ g)‖ ≤ ∑ y ∈ Kᶜ, ε y := by
      rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (shiftOp_mem_unitary Kᶜ g))]
      exact norm_commutator_shiftOp_le B ε g Kᶜ fun y hy ↦ hε y (Finset.mem_compl.mp hy)
    rw [hdiff, norm_smul]
    calc
      _ ≤ ‖(Fintype.card ((v : V) → Label (X v)) : ℂ)⁻¹‖ *
          ∑ _g : (v : V) → Label (X v), ∑ y ∈ Kᶜ, ε y :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ ↦
          hterm g)) (norm_nonneg _)
      _ = ∑ y ∈ Kᶜ, ε y := by
        have hN' : (Fintype.card ((v : V) → Label (X v)) : ℝ) ≠ 0 := by exact_mod_cast hN
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, norm_inv,
          Complex.norm_natCast, inv_mul_cancel₀ hN', one_mul]

/-- **The commutant of the complement.** An operator is supported on `D` exactly when it
commutes with every operator supported on the complement of `D`. Source: OpenAI, *A
two-dimensional area law from a global spectral gap*, `03-quasilocal.tex`, lines 386–388,
where an operator commuting with the complementary algebra is fixed by the expectation. -/
theorem mem_supportedOperators_iff_forall_commute {D : Finset V}
    {A : Matrix (Config X) (Config X) ℂ} :
    A ∈ supportedOperators X D ↔ ∀ B ∈ supportedOperators X Dᶜ, Commute A B := by
  refine ⟨fun hA _ hB ↦ commute_of_mem_supportedOperators_of_disjoint hA hB
    disjoint_compl_right, fun h ↦ ?_⟩
  have hle := norm_sub_regionExpectation_le D A 0 fun y hy U hU _ ↦ by
    have hU' : U ∈ supportedOperators X Dᶜ :=
      supportedOperators_mono (Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr hy)) hU
    rw [(h U hU').eq, sub_self, norm_zero]
    rfl
  simp only [Pi.zero_apply, Finset.sum_const_zero, norm_le_zero_iff, sub_eq_zero] at hle
  rw [hle]
  exact regionExpectation_mem_supportedOperators D A

end Average

end ManyBody
