/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Gate.Controlled
import QICLean.Circuit.Gate.TwoLevel
import QICLean.ManyBody.Sites.Placement.PlaceAlong

/-!
# Controlled one-site operations

On a finite system of sites `X : S → Type`, the operation "apply `u` at the site `t` when the
sites of `R` are in the configuration `c`" is the controlled element `C(p, U) = p U + (1 - p)`,
where `p` is the projection onto the configurations agreeing with `c` on `R` and `U` is the
matrix `u` at the site `t`. These are the operations used to write a unitary on a
constant number of sites as a product of two-site gates: a controlled commutator at `t` is a
product of two controlled operations with one control fewer and two operations on two sites
(`QuantumCircuit.ctrlOp_insert_commutator`), and the two-level operator between two
configurations that differ at the one site `t` is a two-level operation at `t` controlled by
all other sites (`QuantumCircuit.twoLevel_update_eq_ctrlOp`).

The decomposition of gates acting on a constant number of sites into two-site gates is the
step "can be further expressed with a low-depth circuit of local gates" of arXiv:2307.01696
(caption of Fig. 1 and paragraph "The sequential-RG circuit").

The declarations restate `ctrlOp` and its lemmas of `TNLean/Circuit/Gates/Controlled.lean`,
`ctrlProj` and its lemmas of `TNLean/Circuit/SiteOperators.lean`, and
`twoLevel_update_eq_ctrlOp` of `TNLean/Circuit/Gates/ControlledProducts.lean`, at commit
`414a18fb88` (Apache-2.0). The changes: any finite basis at each site in place of one common
dimension `d`; the operator `u` at the site `t` is `ManyBody.placeAt t u` in place of a
separate definition `siteOp`; statements of unitarity use `Matrix.unitaryGroup`.

## Main definitions

* `QuantumCircuit.ctrlProj` — the projection onto the configurations agreeing with `c` on `R`.
* `QuantumCircuit.ctrlOp` — the operation `u` at `t`, controlled by the configuration `c` on
  `R`.

## Main results

* `QuantumCircuit.ctrlOp_mul`, `QuantumCircuit.ctrlOp_one`, `QuantumCircuit.ctrlOp_conjTranspose`,
  `QuantumCircuit.ctrlOp_mem_unitaryGroup`, `QuantumCircuit.ctrlOp_mem_supportedOperators`.
* `QuantumCircuit.ctrlOp_insert_commutator` — removing one control from a controlled commutator.
* `QuantumCircuit.twoLevel_update_eq_ctrlOp` — a two-level operator between configurations
  differing at one site is a controlled two-level operation at that site.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-! ### Projections onto configurations -/

/-- The projection onto the configurations `x` with `x i = c i` for every `i ∈ R`.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit" (gates with constant support
decomposed into local gates). -/
def ctrlProj (R : Finset S) (c : Config X) : Matrix (Config X) (Config X) ℂ :=
  diagonal fun x ↦ if ∀ i ∈ R, x i = c i then 1 else 0

theorem isIdempotentElem_ctrlProj (R : Finset S) (c : Config X) :
    IsIdempotentElem (ctrlProj R c) := by
  unfold IsIdempotentElem ctrlProj
  rw [diagonal_mul_diagonal]
  congr 1; funext x; split_ifs <;> simp

theorem commute_ctrlProj (R R' : Finset S) (c c' : Config X) :
    Commute (ctrlProj R c) (ctrlProj R' c') := by
  unfold Commute SemiconjBy ctrlProj
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1; funext x; ring

theorem ctrlProj_insert {s : S} (R : Finset S) (c : Config X) :
    ctrlProj (insert s R) c = ctrlProj R c * ctrlProj {s} c := by
  unfold ctrlProj
  rw [diagonal_mul_diagonal]
  congr 1; funext x
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  by_cases h1 : x s = c s <;> by_cases h2 : ∀ i ∈ R, x i = c i <;> simp [h1, h2]

omit [∀ s, Fintype (X s)] in
@[simp] theorem ctrlProj_empty (c : Config X) : ctrlProj ∅ c = 1 := by
  simp [ctrlProj]

omit [∀ s, Fintype (X s)] in
theorem ctrlProj_conjTranspose (R : Finset S) (c : Config X) :
    (ctrlProj R c)ᴴ = ctrlProj R c := by
  unfold ctrlProj
  rw [diagonal_conjTranspose]
  congr 1; funext x; simp only [Pi.star_apply]; split_ifs <;> simp

/-- The projection onto the configurations agreeing with `c` on `R` is supported on `R`. -/
theorem ctrlProj_mem_supportedOperators (R : Finset S) (c : Config X) :
    ctrlProj R c ∈ supportedOperators X R := by
  refine ⟨fun σ τ ⟨v, _, hne⟩ ↦ diagonal_apply_ne _ fun h ↦ hne (congrFun h v),
    fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  have hστ : σ = τ ↔ σ' = τ' := by
    refine ⟨fun h ↦ funext fun v ↦ ?_, fun h ↦ funext fun v ↦ ?_⟩
    · by_cases hv : v ∈ R
      · rw [← h1 v hv, ← h2 v hv, h]
      · exact h4 v hv
    · by_cases hv : v ∈ R
      · rw [h1 v hv, h2 v hv, h]
      · exact h3 v hv
  have hc : (∀ i ∈ R, σ i = c i) ↔ ∀ i ∈ R, σ' i = c i :=
    forall₂_congr fun i hi ↦ by rw [h1 i hi]
  simp only [ctrlProj, diagonal_apply, hστ, hc]

/-- The projection onto the configurations agreeing with `c` on `R` commutes with an operator at
a site outside `R`. -/
theorem commute_ctrlProj_placeAt {R : Finset S} {t : S} (ht : t ∉ R) (c : Config X)
    (u : Matrix (X t) (X t) ℂ) : Commute (ctrlProj R c) (placeAt t u) :=
  commute_of_mem_supportedOperators_of_disjoint (ctrlProj_mem_supportedOperators R c)
    (placeAt_mem_supportedOperators t u) (Finset.disjoint_singleton_right.mpr ht)

/-! ### Controlled operations -/

/-- The controlled operation: `u` at the site `t` when the sites of `R` are in the configuration
`c`, the identity otherwise.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit" (gates with constant support
decomposed into local gates). -/
noncomputable def ctrlOp (R : Finset S) (c : Config X) (t : S) (u : Matrix (X t) (X t) ℂ) :
    Matrix (Config X) (Config X) ℂ :=
  ctrlElem (ctrlProj R c) (placeAt t u)

@[simp] theorem ctrlOp_empty (c : Config X) (t : S) (u : Matrix (X t) (X t) ℂ) :
    ctrlOp ∅ c t u = placeAt t u := by
  simp [ctrlOp, ctrlElem]

theorem ctrlOp_mul {R : Finset S} {t : S} (ht : t ∉ R) (c : Config X)
    (u v : Matrix (X t) (X t) ℂ) : ctrlOp R c t u * ctrlOp R c t v = ctrlOp R c t (u * v) := by
  rw [ctrlOp, ctrlOp, ctrlElem_mul (isIdempotentElem_ctrlProj R c)
    (commute_ctrlProj_placeAt ht c u), ← placeAt_mul, ctrlOp]

@[simp] theorem ctrlOp_one (R : Finset S) (c : Config X) (t : S) : ctrlOp R c t 1 = 1 := by
  rw [ctrlOp, placeAt_one, ctrlElem_one]

theorem ctrlOp_conjTranspose {R : Finset S} {t : S} (ht : t ∉ R) (c : Config X)
    (u : Matrix (X t) (X t) ℂ) : (ctrlOp R c t u)ᴴ = ctrlOp R c t uᴴ := by
  rw [ctrlOp, ctrlOp, ctrlElem, ctrlElem, conjTranspose_add, conjTranspose_mul, conjTranspose_sub,
    conjTranspose_one, ctrlProj_conjTranspose, ← placeAt_conjTranspose,
    (commute_ctrlProj_placeAt ht c uᴴ).eq]

theorem ctrlOp_mem_unitaryGroup {R : Finset S} {t : S} (ht : t ∉ R) (c : Config X)
    {u : Matrix (X t) (X t) ℂ} (hu : u ∈ unitaryGroup (X t) ℂ) :
    ctrlOp R c t u ∈ unitaryGroup (Config X) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, ctrlOp_conjTranspose ht, ctrlOp_mul ht,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hu, ctrlOp_one]

/-- The operation at `t` controlled by the sites of `R` is supported on `R` and `t`. -/
theorem ctrlOp_mem_supportedOperators (R : Finset S) (c : Config X) (t : S)
    (u : Matrix (X t) (X t) ℂ) : ctrlOp R c t u ∈ supportedOperators X (insert t R) := by
  have hp := supportedOperators_mono (Finset.subset_insert t R)
    (ctrlProj_mem_supportedOperators R c)
  have hs := supportedOperators_mono
    (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self t R))
    (placeAt_mem_supportedOperators t u)
  exact add_mem (mul_mem hp hs) (sub_mem (one_mem _) hp)

/-- **Controlled commutator on the sites.** Removing one control site `s` from the controls of a
commutator `v w v† w†` at the site `t`. -/
theorem ctrlOp_insert_commutator {R : Finset S} {s t : S} (ht : t ∉ R) (hst : s ≠ t)
    (c : Config X) {v w : Matrix (X t) (X t) ℂ} (hv : v ∈ unitaryGroup (X t) ℂ)
    (hw : w ∈ unitaryGroup (X t) ℂ) :
    ctrlOp (insert s R) c t (v * w * star v * star w) =
      ctrlOp R c t v * ctrlOp {s} c t w * ctrlOp R c t (star v) * ctrlOp {s} c t (star w) := by
  have hts : t ∉ ({s} : Finset S) := by simpa using Ne.symm hst
  rw [ctrlOp, ctrlProj_insert, placeAt_mul, placeAt_mul, placeAt_mul, ctrlOp, ctrlOp, ctrlOp,
    ctrlOp]
  refine (ctrlElem_commutator (isIdempotentElem_ctrlProj R c) (isIdempotentElem_ctrlProj {s} c)
    (commute_ctrlProj R {s} c c) (commute_ctrlProj_placeAt ht c v)
    (commute_ctrlProj_placeAt ht c w) (commute_ctrlProj_placeAt hts c v)
    (commute_ctrlProj_placeAt hts c _) (commute_ctrlProj_placeAt hts c w)
    ?_ ?_).symm
  · rw [← placeAt_mul, mem_unitaryGroup_iff.mp hv, placeAt_one]
  · rw [← placeAt_mul, mem_unitaryGroup_iff.mp hw, placeAt_one]

/-! ### Two-level operators between neighbouring configurations -/

/-- The two-level operator between the configuration `a` and `a` with the site `t` changed to
`β` is the two-level operator between the levels `a t` and `β` at the site `t`, controlled by all
other sites being in the configuration `a`. -/
theorem twoLevel_update_eq_ctrlOp (a : Config X) (t : S) {β : X t} (hβ : β ≠ a t)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    twoLevel a (Function.update a t β) g =
      ctrlOp (Finset.univ.erase t) a t (twoLevel (a t) β g) := by
  set a' := Function.update a t β
  have ha' : ∀ i, i ≠ t → a' i = a i := fun i hi ↦ Function.update_of_ne hi _ _
  have hat : a' t = β := Function.update_self _ _ _
  have hmem : ∀ z : Config X, (z = a ∨ z = a') ↔ ((∀ i, i ≠ t → z i = a i) ∧
      (z t = a t ∨ z t = β)) := fun z ↦ by
    constructor
    · rintro (rfl | rfl)
      · exact ⟨fun _ _ ↦ rfl, Or.inl rfl⟩
      · exact ⟨ha', Or.inr hat⟩
    · rintro ⟨hz, hzt | hzt⟩
      · left; funext i; by_cases hi : i = t
        · subst hi; exact hzt
        · exact hz i hi
      · right; funext i; by_cases hi : i = t
        · subst hi; rw [hat]; exact hzt
        · rw [ha' i hi]; exact hz i hi
  have hidx : ∀ z : Config X, (∀ i, i ≠ t → z i = a i) →
      twoLevelIdx a z = twoLevelIdx (a t) (z t) := fun z hz ↦ by
    unfold twoLevelIdx
    by_cases hzt : z t = a t
    · rw [ite_eq_left hzt, ite_eq_left]; funext i; by_cases hi : i = t
      · subst hi; exact hzt
      · exact hz i hi
    · rw [ite_eq_right hzt, ite_eq_right]; rintro rfl; exact hzt rfl
  ext x y
  rw [ctrlOp, ctrlElem, Matrix.add_apply, Matrix.sub_apply, ctrlProj, diagonal_mul,
    placeAt_apply, one_apply, diagonal_apply]
  by_cases hx : ∀ i, i ∈ Finset.univ.erase t → x i = a i
  · have hx' : ∀ i, i ≠ t → x i = a i := fun i hi ↦ hx i (by simp [hi])
    rw [ite_eq_left hx, one_mul]
    have hcancel : ((if x = y then (1 : ℂ) else 0) - if x = y then 1 else 0) = 0 := sub_self _
    simp only [hcancel, add_zero]
    by_cases hy : ∀ i, i ≠ t → y i = a i
    · have hxy : ∀ v, v ≠ t → x v = y v := fun i hi ↦ (hx' i hi).trans (hy i hi).symm
      rw [ite_eq_left hxy]
      have e1 : (x = a ∨ x = a') ↔ (x t = a t ∨ x t = β) := by
        rw [hmem]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx', h⟩⟩
      have e2 : (y = a ∨ y = a') ↔ (y t = a t ∨ y t = β) := by
        rw [hmem]; exact ⟨fun h ↦ h.2, fun h ↦ ⟨hy, h⟩⟩
      have e3 : x = y ↔ x t = y t := ⟨fun h ↦ h ▸ rfl, fun h ↦ funext fun i ↦ by
        by_cases hi : i = t
        · subst hi; exact h
        · rw [hx' i hi, hy i hi]⟩
      simp only [twoLevel, of_apply, e1, e2, e3, hidx x hx', hidx y hy]
    · have hxy : ¬∀ v, v ≠ t → x v = y v := fun h ↦
        hy fun i hi ↦ (h i hi).symm.trans (hx' i hi)
      rw [ite_eq_right hxy]
      rw [twoLevel_apply_of_not_mem_right g x (fun h ↦ hy ((hmem y).1 h).1)]
      rw [ite_eq_right]; rintro rfl; exact hy hx'
  · have hx' : ¬∀ i, i ≠ t → x i = a i := fun h ↦
      hx fun i hi ↦ h i (Finset.ne_of_mem_erase hi)
    rw [ite_eq_right hx, zero_mul, zero_add]
    rw [twoLevel_apply_of_not_mem_left g (fun h ↦ hx' ((hmem x).1 h).1)]
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]

end QuantumCircuit
