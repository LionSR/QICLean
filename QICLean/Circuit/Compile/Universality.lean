/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.InformationTheory.Hamming
import QICLean.Circuit.Core.SiteControlled
import QICLean.Circuit.Gate.Givens
import QICLean.Circuit.Model.Unitary

/-!
# Universality of two-site gates, with gate counts

Let `Γ` be a geometry on a finite set of sites `S` with any finite basis at each site,
and suppose that every unitary supported on two distinct sites is a product of gates of `Γ` of
total cost at most `k`. Then every unitary on the system is a product of gates of `Γ` of total
cost at most `unitaryGateCount S X * k` (`QuantumCircuit.isGateProduct_unitaryGateCount`), where
`unitaryGateCount S X = 3 m² (2N - 1)(2^N - 2)` for `N` sites and `m` configurations. One-site
unitaries are onsite families and cost nothing. The decomposition is an exact matrix equality,
including the global phase, and uses no auxiliary sites.

The proof has three steps.

* A one-site two-level rotation or phase at `t`, controlled by the configuration of a set `R`
  of other sites, costs at most `(2^(|R| + 1) - 2) k`
  (`QuantumCircuit.isGateProduct_ctrlOp_twoLevel`): every rotation and phase is a group
  commutator `g₁ g₂ g₁† g₂†` with `g₁` of the same kind, and a controlled commutator is a product
  of two controlled operations with one control fewer and two operations on two sites
  (`QuantumCircuit.ctrlOp_insert_commutator`).
* A two-level rotation or phase between configurations differing at one site is such an
  operation with all other sites as controls (`QuantumCircuit.twoLevel_update_eq_ctrlOp`); between
  configurations at Hamming distance `h + 1` it is conjugated to one at distance `h` by a
  two-level quarter turn (`QuantumCircuit.twoLevel_conj_quarterTwo`). This gives the bound
  `(2N - 1)(2^N - 2) k` (`QuantumCircuit.isGateProduct_twoLevel`).
* The Givens decomposition writes a unitary of determinant one as a product of at most `3 m²`
  two-level rotations and phases (`QuantumCircuit.isTwoLevelWord_of_det_eq_one`), and a global
  phase is a one-site phase.

On the geometry of sites and ordered pairs the hypothesis holds with `k` the cost of a pair cell
(`QuantumCircuit.isGateProduct_sitesAndPairs`).

This is the step "can be further expressed with a low-depth circuit of local gates" of
arXiv:2307.01696 (caption of Fig. 1), for the unitaries with constant support of the paragraph
"The sequential-RG circuit"; the explicit count is the synthesis estimate of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

The declarations restate the gate-count results of `TNLean/Circuit/Gates/ControlledProducts.lean`,
`TNLean/Circuit/Gates/TwoSiteUniversality.lean` and `TNLean/Circuit/QuantitativeUnitaryGates.lean`
at commit `414a18fb88` (Apache-2.0). The changes: any geometry `Γ`, any finite set of sites and
any finite basis at each site, in place of the neighbouring pairs of an open chain of `n ≥ 2`
qudits of one dimension `d`; the cost of a two-site unitary is the hypothesis `k` in place of
`2n`; one-site unitaries cost nothing, so an uncontrolled operation and a global phase are free
and the controlled count is `2^(j + 1) - 2` in place of `4 n 3^j`; the bounds are stated with the
number of controls of the operation.

## Main definitions

* `QuantumCircuit.unitaryGateCount` — the explicit count `3 m² (2N - 1)(2^N - 2)`.

## Main results

* `QuantumCircuit.IsGateProduct.of_mem_supportedOperators_singleton` — a unitary on one site
  costs nothing.
* `QuantumCircuit.IsGateProduct.of_mem_supportedOperators_card_le_two` — a unitary on at most two
  sites costs at most `k`.
* `QuantumCircuit.isGateProduct_ctrlOp_twoLevel` — controlled two-level rotations and phases.
* `QuantumCircuit.isGateProduct_twoLevel` — two-level rotations and phases between
  configurations.
* `QuantumCircuit.isGateProduct_unitaryGateCount`, `QuantumCircuit.exists_isGateProduct` — every
  unitary.
* `QuantumCircuit.unitaryGateCount_le` — the count is at most `6 m⁴` when every site has at least
  two basis vectors.
* `QuantumCircuit.isGateProduct_sitesAndPairs` — universality on the geometry of sites and
  ordered pairs.
-/

open Matrix ManyBody
open scoped ComplexConjugate

namespace QuantumCircuit

/-! ### Moving a two-level rotation by a quarter turn -/

section Conj

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem quarterTwo_isSpecialTwo : IsSpecialTwo quarterTwo :=
  Or.inl ⟨-Complex.I, by simp, quarterTwo_eq_rotTwo⟩

/-- The quarter turn `T` on the pair `{c, b}` sends `|b⟩ ↦ |c⟩` and `|c⟩ ↦ -|b⟩`, so it
conjugates the two-level operator on `{a, b}` to the one on `{a, c}`:
`T (twoLevel a b g) = (twoLevel a c g) T`. -/
theorem twoLevel_quarterTwo_mul {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    twoLevel c b quarterTwo * twoLevel a b g = twoLevel a c g * twoLevel c b quarterTwo := by
  ext x y
  rw [twoLevel_mul_apply (Ne.symm hbc), twoLevel_mul_apply hac]
  simp only [twoLevel, of_apply, twoLevelIdx, quarterTwo, cons_val', cons_val_zero,
    cons_val_one, empty_val', cons_val_fin_one]
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    by_cases hya : y = a <;> by_cases hyb : y = b <;> by_cases hyc : y = c <;>
    simp_all [eq_comm]

/-- `twoLevel a b g = T† (twoLevel a c g) T` for the quarter turn `T` on `{c, b}`. -/
theorem twoLevel_conj_quarterTwo {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (g : Matrix (Fin 2) (Fin 2) ℂ) :
    twoLevel a b g =
      (twoLevel c b quarterTwo)ᴴ * twoLevel a c g * twoLevel c b quarterTwo := by
  have hT := twoLevel_mem_unitary (ι := ι) (Ne.symm hbc) quarterTwo_mem_unitary
  rw [Matrix.mul_assoc, ← twoLevel_quarterTwo_mul hab hac hbc, ← Matrix.mul_assoc,
    ← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hT, Matrix.one_mul]

end Conj

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-! ### One-site unitaries and unitaries on two sites -/

namespace IsGateProduct

/-- A unitary supported on one site costs nothing. -/
theorem of_mem_supportedOperators_singleton {t : S} {Z : Matrix (Config X) (Config X) ℂ}
    (hZu : Z ∈ unitaryGroup (Config X) ℂ) (hZ : Z ∈ supportedOperators X {t}) (K : ℕ) :
    IsGateProduct Γ K Z := by
  by_cases hne : ∀ s, Nonempty (X s)
  · obtain ⟨V, rfl⟩ := exists_eq_place_of_mem_supportedOperators hZ
    have hV : V ∈ unitaryGroup _ ℂ := place_mem_unitaryGroup_iff.mp hZu
    exact place_singleton t hV K
  · push Not at hne
    obtain ⟨s, hs⟩ := hne
    have : IsEmpty (Config X) := ⟨fun σ ↦ hs.false (σ s)⟩
    rw [Subsingleton.elim Z 1]
    exact one Γ X K

/-- **Unitaries on at most two sites.** If every unitary supported on two distinct sites is a
product of gates of cost at most `k`, so is every unitary supported on at most two sites. -/
theorem of_mem_supportedOperators_card_le_two {k : ℕ}
    (hpair : ∀ s t, s ≠ t → ∀ Z ∈ unitaryGroup (Config X) ℂ, Z ∈ supportedOperators X {s, t} →
      IsGateProduct Γ k Z)
    {T : Finset S} (hT : T.card ≤ 2) {Z : Matrix (Config X) (Config X) ℂ}
    (hZu : Z ∈ unitaryGroup (Config X) ℂ) (hZ : Z ∈ supportedOperators X T) :
    IsGateProduct Γ k Z := by
  obtain h | h | h : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
  · rw [Finset.card_eq_zero] at h
    subst h
    rcases isEmpty_or_nonempty S with hS | hS
    · -- With no sites, `Z` is a phase times the identity on the one configuration.
      have : Unique (Config X) := Pi.uniqueOfIsEmpty _
      set μ := Z default default
      have hZμ : Z = μ • (1 : Matrix (Config X) (Config X) ℂ) := by
        ext a b
        rw [Subsingleton.elim a default, Subsingleton.elim b default]
        simp [μ]
      have hμ : ‖μ‖ = 1 := by
        simpa [μ] using CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hZu)
      rw [hZμ]
      exact smul_one hμ k
    · exact of_mem_supportedOperators_singleton (t := Classical.arbitrary S) hZu
        (supportedOperators_mono (Finset.empty_subset _) hZ) k
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact of_mem_supportedOperators_singleton hZu hZ k
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    exact hpair a b hab Z hZu hZ

end IsGateProduct

/-! ### Controlled two-level operations -/

variable {k : ℕ}

/-- **Controlled two-level operations.** If every unitary supported on two distinct sites is a
product of gates of cost at most `k`, then a one-site two-level rotation or phase at the site `t`,
controlled by the configuration of a set `R` of other sites, is a product of gates of cost at
most `(2^(|R| + 1) - 2) k`. -/
theorem isGateProduct_ctrlOp_twoLevel
    (hpair : ∀ s t, s ≠ t → ∀ Z ∈ unitaryGroup (Config X) ℂ, Z ∈ supportedOperators X {s, t} →
      IsGateProduct Γ k Z)
    {t : S} (c : Config X) {α β : X t} (hαβ : α ≠ β) (R : Finset S) (ht : t ∉ R)
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : IsSpecialTwo g) :
    IsGateProduct Γ ((2 ^ (R.card + 1) - 2) * k) (ctrlOp R c t (twoLevel α β g)) := by
  induction R using Finset.induction_on generalizing g with
  | empty =>
    rw [ctrlOp_empty, ← place_siteEquiv_eq_placeAt]
    exact IsGateProduct.place_singleton t
      (submatrix_equiv_mem_unitary.mpr (twoLevel_mem_unitary hαβ hg.mem_unitary)) _
  | insert s R hs ih =>
    have htR : t ∉ R := fun h ↦ ht (Finset.mem_insert_of_mem h)
    have hst : s ≠ t := fun h ↦ ht (h ▸ Finset.mem_insert_self s R)
    obtain ⟨g₁, g₂, hg₁, hg₂, rfl⟩ := hg.exists_commutator
    have hV := twoLevel_mem_unitary hαβ hg₁.mem_unitary
    have hW := twoLevel_mem_unitary (ι := X t) hαβ hg₂
    have heq : twoLevel α β (g₁ * g₂ * star g₁ * star g₂) =
        twoLevel α β g₁ * twoLevel α β g₂ * star (twoLevel α β g₁) *
          star (twoLevel α β g₂) := by
      rw [star_eq_conjTranspose (twoLevel α β g₁), star_eq_conjTranspose (twoLevel α β g₂),
        twoLevel_conjTranspose, twoLevel_conjTranspose, twoLevel_mul hαβ, twoLevel_mul hαβ,
        twoLevel_mul hαβ]
      rfl
    rw [heq, ctrlOp_insert_commutator htR hst c hV hW]
    have hsingle : ∀ u ∈ unitaryGroup (X t) ℂ, IsGateProduct Γ k (ctrlOp {s} c t u) :=
      fun u hu ↦ hpair t s (Ne.symm hst) _
        (ctrlOp_mem_unitaryGroup (by simpa using Ne.symm hst) c hu)
        (ctrlOp_mem_supportedOperators {s} c t u)
    have h2 : IsGateProduct Γ ((2 ^ (R.card + 1) - 2) * k)
        (ctrlOp R c t (star (twoLevel α β g₁))) := by
      rw [star_eq_conjTranspose, twoLevel_conjTranspose]
      exact ih htR hg₁.conjTranspose
    refine ((((ih htR hg₁).mul (hsingle _ hW)).mul h2).mul
      (hsingle _ (Unitary.star_mem hW))).mono (le_of_eq ?_)
    obtain ⟨q, hq⟩ : ∃ q, 2 ^ (R.card + 1) = q + 2 :=
      ⟨2 ^ (R.card + 1) - 2, by have := Nat.one_lt_two_pow (n := R.card + 1) (by omega); omega⟩
    rw [Finset.card_insert_of_notMem hs, pow_succ 2 (R.card + 1), hq,
      show (q + 2) * 2 - 2 = 2 * q + 2 by omega, show q + 2 - 2 = q by omega]
    ring

/-! ### Two-level operators between configurations -/

/-- **Two-level rotations and phases.** If every unitary supported on two distinct sites is a
product of gates of cost at most `k`, then every two-level rotation or phase between two distinct
configurations of `N` sites is a product of gates of cost at most `(2N - 1)(2^N - 2) k`:
between configurations differing at one site it is a two-level operation at that site
controlled by the `N - 1` others, and configurations at Hamming distance `h + 1` are joined by
conjugating with `h` quarter turns. -/
theorem isGateProduct_twoLevel
    (hpair : ∀ s t, s ≠ t → ∀ Z ∈ unitaryGroup (Config X) ℂ, Z ∈ supportedOperators X {s, t} →
      IsGateProduct Γ k Z)
    {a b : Config X} (hab : a ≠ b) {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : IsSpecialTwo g) :
    IsGateProduct Γ ((2 * Fintype.card S - 1) * ((2 ^ Fintype.card S - 2) * k))
      (twoLevel a b g) := by
  set K₁ := (2 ^ Fintype.card S - 2) * k
  -- configurations differing at exactly one site
  have hone : ∀ (a : Config X) (t : S) (β : X t), β ≠ a t → ∀ g, IsSpecialTwo g →
      IsGateProduct Γ K₁ (twoLevel a (Function.update a t β) g) := by
    intro a t β hβ g hg
    rw [twoLevel_update_eq_ctrlOp a t hβ g]
    have h := isGateProduct_ctrlOp_twoLevel hpair a (Ne.symm hβ) _
      (Finset.notMem_erase t Finset.univ) hg
    have hN : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨t⟩
    rwa [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ,
      Nat.sub_add_cancel hN] at h
  have key : ∀ h : ℕ, ∀ a b : Config X, hammingDist a b = h + 1 → ∀ g, IsSpecialTwo g →
      IsGateProduct Γ ((2 * h + 1) * K₁) (twoLevel a b g) := by
    intro h
    induction h with
    | zero =>
      intro a b hab g hg
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hab
      have hb : b = Function.update a t (b t) := by
        funext i
        by_cases hi : i = t
        · subst hi; simp
        · rw [Function.update_of_ne hi]
          by_contra h'
          have : i ∈ Finset.univ.filter fun i ↦ a i ≠ b i := by simp [Ne.symm h']
          rw [ht] at this
          exact hi (Finset.mem_singleton.mp this)
      have hbt : b t ≠ a t := by
        have : t ∈ Finset.univ.filter fun i ↦ a i ≠ b i := by rw [ht]; simp
        simpa [eq_comm] using this
      rw [hb]
      simpa using hone a t (b t) hbt g hg
    | succ h ih =>
      intro a b hab g hg
      obtain ⟨t, ht⟩ : (Finset.univ.filter fun i ↦ a i ≠ b i).Nonempty :=
        Finset.card_pos.mp (by unfold hammingDist at hab; omega)
      have hat : a t ≠ b t := (Finset.mem_filter.mp ht).2
      set c := Function.update b t (a t) with hc
      have hfilter : (Finset.univ.filter fun i ↦ a i ≠ c i) =
          (Finset.univ.filter fun i ↦ a i ≠ b i).erase t := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hc]
        by_cases hi : i = t
        · subst hi; simp
        · simp [hi]
      have hac' : hammingDist a c = h + 1 := by
        unfold hammingDist
        rw [hfilter, Finset.card_erase_of_mem ht]
        unfold hammingDist at hab
        omega
      have hac : a ≠ c := hammingDist_pos.mp (by omega)
      have hbc : b ≠ c := fun h' ↦ by
        have := congrFun h' t
        rw [hc, Function.update_self] at this
        exact hat this.symm
      have hab' : a ≠ b := fun h' ↦ by rw [h'] at hat; exact hat rfl
      have hcb : b = Function.update c t (b t) := by
        rw [hc, Function.update_idem, Function.update_eq_self]
      have hT : IsGateProduct Γ K₁ (twoLevel c b quarterTwo) := by
        have hbt : b t ≠ c t := by rw [hc, Function.update_self]; exact Ne.symm hat
        rw [hcb]
        simpa using hone c t (b t) hbt _ quarterTwo_isSpecialTwo
      rw [twoLevel_conj_quarterTwo hab' hac hbc g]
      refine ((hT.conjTranspose.mul (ih a c hac' g hg)).mul hT).mono (le_of_eq ?_)
      ring
  obtain ⟨h, hh⟩ : ∃ h, hammingDist a b = h + 1 :=
    ⟨hammingDist a b - 1, by have := hammingDist_pos.mpr hab; omega⟩
  refine (key h a b hh g hg).mono (Nat.mul_le_mul_right _ ?_)
  have := (hammingDist_le_card_fintype (x := a) (y := b))
  omega

/-! ### Every unitary -/

variable (S X) in
/-- The number of gates in the synthesis of a unitary on `N` sites with `m` configurations,
relative to the cost of a unitary on two sites: `3 m² (2N - 1)(2^N - 2)`, from at most `3 m²`
two-level rotations and phases (Givens), each costing `(2N - 1)(2^N - 2)` unitaries on two
sites. Derived synthesis estimate of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def unitaryGateCount : ℕ :=
  3 * (∏ s, Fintype.card (X s)) * (∏ s, Fintype.card (X s)) *
    ((2 * Fintype.card S - 1) * (2 ^ Fintype.card S - 2))

/-- **Two-site universality with a gate count.** If every unitary supported on two distinct sites
is a product of gates of `Γ` of cost at most `k`, then every unitary is a product of gates of `Γ`
of cost at most `unitaryGateCount S X * k`. The circuit agrees with the unitary as a matrix,
including its global phase, and uses no auxiliary sites.

arXiv:2307.01696, caption of Fig. 1: the unitaries with constant support "can be further
expressed with a low-depth circuit of local gates"; the count is the derived synthesis estimate
of Section 5 of TNLean `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isGateProduct_unitaryGateCount
    (hpair : ∀ s t, s ≠ t → ∀ Z ∈ unitaryGroup (Config X) ℂ, Z ∈ supportedOperators X {s, t} →
      IsGateProduct Γ k Z)
    {U : Matrix (Config X) (Config X) ℂ} (hU : U ∈ unitaryGroup (Config X) ℂ) :
    IsGateProduct Γ (unitaryGateCount S X * k) U := by
  set K₂ := (2 * Fintype.card S - 1) * ((2 ^ Fintype.card S - 2) * k)
  set m := Fintype.card (Config X)
  have hcost : unitaryGateCount S X * k = 3 * m * m * K₂ := by
    simp only [unitaryGateCount, m, K₂, Fintype.card_pi]
    ring
  rw [hcost]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · have : IsEmpty (Config X) := Fintype.card_eq_zero_iff.mp hm
    rw [Subsingleton.elim U 1]
    exact IsGateProduct.one Γ X _
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq U.det hm
  have hdetn : ‖U.det‖ = 1 := by
    have h := congrArg det (mem_unitaryGroup_iff'.mp hU)
    rw [det_mul, det_one, star_eq_conjTranspose, det_conjTranspose, Complex.star_def,
      Complex.conj_mul'] at h
    exact_mod_cast (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp
      (by exact_mod_cast h)
  have hμn : ‖μ‖ = 1 := by
    have h : ‖μ‖ ^ m = 1 := by rw [← norm_pow, hμ, hdetn]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h
  have hμ0 : μ ≠ 0 := fun h ↦ by simp [h] at hμn
  set U' := μ⁻¹ • U with hU'
  have hU'u : U' ∈ unitaryGroup (Config X) ℂ := by
    have hu := IsGateProduct.smul_one (Γ := Γ) (X := X) (μ := μ⁻¹) (by simp [hμn]) 0
    have : U' = (μ⁻¹ • (1 : Matrix (Config X) (Config X) ℂ)) * U := by
      rw [hU', smul_mul_assoc, Matrix.one_mul]
    rw [this]
    exact Submonoid.mul_mem _ hu.mem_unitaryGroup hU
  have hU'det : U'.det = 1 := by
    rw [hU', det_smul, inv_pow, hμ, inv_mul_cancel₀]
    intro h; rw [h] at hdetn; simp at hdetn
  obtain ⟨l, hl, hlg, hlU⟩ := isTwoLevelWord_of_det_eq_one hU'u hU'det
  have hprod : IsGateProduct Γ (l.length * K₂)
      (l.map fun p ↦ twoLevel p.1 p.2.1 p.2.2).prod := by
    have := IsGateProduct.list_prod (K := K₂) (l.map fun p ↦ twoLevel p.1 p.2.1 p.2.2)
      (fun Y hY ↦ by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hY
        exact isGateProduct_twoLevel hpair (hlg p hp).1 (hlg p hp).2)
    simpa using this
  have hUeq : U = (μ • (1 : Matrix (Config X) (Config X) ℂ)) * U' := by
    rw [hU', smul_mul_assoc, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  rw [hUeq, hlU]
  refine ((IsGateProduct.smul_one hμn 0).mul hprod).mono ?_
  have : l.length * K₂ ≤ 3 * m * m * K₂ := Nat.mul_le_mul_right _ hl
  omega

/-- **Two-site universality.** If every unitary supported on two distinct sites is a product of
gates of `Γ` of cost at most `k`, there is `K` such that every unitary is a product of gates of
`Γ` of cost at most `K`.

arXiv:2307.01696, caption of Fig. 1: the unitaries with constant support "can be further
expressed with a low-depth circuit of local gates". -/
theorem exists_isGateProduct
    (hpair : ∀ s t, s ≠ t → ∀ Z ∈ unitaryGroup (Config X) ℂ, Z ∈ supportedOperators X {s, t} →
      IsGateProduct Γ k Z) :
    ∃ K, ∀ U ∈ unitaryGroup (Config X) ℂ, IsGateProduct Γ K U :=
  ⟨_, fun _ hU ↦ isGateProduct_unitaryGateCount hpair hU⟩

omit [DecidableEq S] [∀ s, DecidableEq (X s)] in
/-- When every site has at least two basis vectors, the gate count is at most `6 m⁴` for `m`
configurations: polynomial in the dimension. -/
theorem unitaryGateCount_le (hX : ∀ s, 2 ≤ Fintype.card (X s)) :
    unitaryGateCount S X ≤ 6 * (∏ s, Fintype.card (X s)) ^ 4 := by
  have h2N : 2 ^ Fintype.card S ≤ ∏ s, Fintype.card (X s) := by
    calc 2 ^ Fintype.card S = ∏ _s : S, 2 := by simp
      _ ≤ _ := Finset.prod_le_prod fun s _ ↦ hX s
  have hN : Fintype.card S ≤ 2 ^ Fintype.card S := Nat.lt_two_pow_self.le
  calc unitaryGateCount S X ≤ 3 * (∏ s, Fintype.card (X s)) * (∏ s, Fintype.card (X s)) *
        ((2 * ∏ s, Fintype.card (X s)) * ∏ s, Fintype.card (X s)) := by
        dsimp only [unitaryGateCount]
        gcongr
        · omega
        · omega
    _ = 6 * (∏ s, Fintype.card (X s)) ^ 4 := by ring

/-! ### The geometry of sites and ordered pairs -/

/-- On the geometry of sites and ordered pairs, a unitary supported on two distinct sites is one
gate, on a pair cell, of cost `c₂`. -/
theorem isGateProduct_sitesAndPairs_of_mem_supportedOperators_pair {c₁ c₂ : ℕ} {s t : S}
    (hst : s ≠ t) {Z : Matrix (Config X) (Config X) ℂ} (hZu : Z ∈ unitaryGroup (Config X) ℂ)
    (hZ : Z ∈ supportedOperators X {s, t}) :
    IsGateProduct (Geometry.sitesAndPairs S c₁ c₂) c₂ Z := by
  have hcell : (Geometry.sitesAndPairs S c₁ c₂).cell (Sum.inr ⟨(s, t), hst⟩) = {s, t} :=
    (Finset.insert_eq s {t}).symm
  exact IsGateProduct.of_mem_supportedOperators (Γ := Geometry.sitesAndPairs S c₁ c₂)
    (b := Sum.inr ⟨(s, t), hst⟩) hZu (hcell ▸ hZ)

/-- **Universality of one- and two-site gates.** Every unitary is a product of gates on sites and
ordered pairs of total cost at most `unitaryGateCount S X * c₂`, where `c₂` is the cost of a gate
on a pair; one-site gates are not needed beyond the free one-site unitaries. -/
theorem isGateProduct_sitesAndPairs (c₁ c₂ : ℕ)
    {U : Matrix (Config X) (Config X) ℂ} (hU : U ∈ unitaryGroup (Config X) ℂ) :
    IsGateProduct (Geometry.sitesAndPairs S c₁ c₂) (unitaryGateCount S X * c₂) U :=
  isGateProduct_unitaryGateCount
    (fun _ _ hst _ hZu hZ ↦ isGateProduct_sitesAndPairs_of_mem_supportedOperators_pair hst hZu hZ)
    hU

end QuantumCircuit
