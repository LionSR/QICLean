/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.TripartiteDecorrelation
import QICLean.ManyBody.Hamiltonian.FrustrationFree

/-!
# Commuting parent Hamiltonians on three regions

Let `a` and `b` be disjoint regions of a system of sites, and write `m` for the sites outside
`a ∪ b`. The system is the tripartite space `H_a ⊗ H_m ⊗ H_b`, with `a ∪ m` the complement of
`b` and `m ∪ b` the complement of `a`. An orthogonal projection `P` on the system has a
**commuting parent Hamiltonian** on `bᶜ` and `aᶜ` when there is a two-term interaction, with
one term supported on each of the two regions, whose terms are commuting orthogonal projections
and whose zero space is the range of `P`. This is CPSV16 Definition D.2: the terms are
`1 - P_{am}` and `1 - P_{mb}` for the local ground-space projections, and the zero space of the
interaction is the intersection of the two placed ground spaces. Such a `P` is the product of
the two placed ground projections, and the two-term interaction is frustration free whenever
`P ≠ 0`.

Proposition D.3 states that `P` has a commuting parent Hamiltonian exactly when the regions
`a` and `b` are decorrelated in `P`. The decorrelation predicate is the one on the tripartite
matrices, `TripartiteDecorrelation.IsDecorrelated`, read in the coordinates
`ManyBody.tripartiteEquiv` that split a configuration into its parts on `a`, `m` and `b`. In
those coordinates the placement of an operator on `a`, `b`, `bᶜ` or `aᶜ` is its tensor lift
`TripartiteDecorrelation.liftA`, `liftB`, `liftAX` or `liftXB`
(`reindex_place_left`, `reindex_place_right`, `reindex_place_compl_right`,
`reindex_place_compl_left`), so decorrelation is the vanishing of
`P (O_a ⊗ 1) (1 - P) (O_b ⊗ 1) P` for all operators `O_a` on `a` and `O_b` on `b`
(`isDecorrelated_reindex_iff`).

This restates, for an interaction on a system of sites with the terms placed by
`ManyBody.place`, the structure `TripartiteDecorrelation.CommutingParentHamiltonian` of
`TNLean/MPS/ParentHamiltonian/TripartiteDecorrelation.lean` at commit `414a18fb88`, which was
written with the tensor lifts on `A × (X × B)`; the proofs follow that file.

## Main definitions

* `ManyBody.tripartiteEquiv` — a configuration as its parts on `a`, on `(a ∪ b)ᶜ` and on `b`.
* `ManyBody.HasCommutingParentHamiltonian` — CPSV16 Definition D.2 on a system of sites.

## Main results

* `ManyBody.reindex_place_compl_right`, `ManyBody.reindex_place_compl_left` — placements on
  `bᶜ` and `aᶜ` are the tensor lifts from `a × m` and `m × b`.
* `ManyBody.isDecorrelated_reindex_iff` — decorrelation of `a` and `b` on the system of sites.
* `ManyBody.HasCommutingParentHamiltonian.eq_mul` — `P` is the product of the two ground
  projections.
* `ManyBody.hasCommutingParentHamiltonian_iff_isDecorrelated` — CPSV16 Proposition D.3.

## References

* Cirac, Pérez-García, Schuch and Verstraete, arXiv:1606.00608, Appendix D.2, Definitions D.1
  and D.2 and Proposition D.3, lines 2187--2289.
-/

open Matrix hiding liftA
open TripartiteDecorrelation
open scoped Kronecker

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-! ### Placements in product coordinates -/

section Coordinates

variable {D : Finset V} {R C : Type*} [DecidableEq C]

omit [∀ v, Fintype (X v)] in
/-- **A placement in product coordinates.** If an identification `g` of the configurations with
`R × C` reads the part on `D` in its first factor and determines the configuration outside `D`
by its second factor, then the placement of `K` on `D` is `K ⊗ 1` in these coordinates. -/
theorem reindex_place_eq_kronecker_one (g : Config X ≃ R × C) (g₁ : RegionConfig X D ≃ R)
    (h₁ : ∀ σ, (g σ).1 = g₁ fun v ↦ σ v)
    (h₂ : ∀ σ τ, (g σ).2 = (g τ).2 ↔ ∀ v ∉ D, σ v = τ v)
    (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    reindex g g (place D K) = reindex g₁ g₁ K ⊗ₖ (1 : Matrix C C ℂ) := by
  ext p q
  have hp := h₁ (g.symm p)
  have hq := h₁ (g.symm q)
  have hpq := h₂ (g.symm p) (g.symm q)
  simp only [Equiv.apply_symm_apply] at hp hq hpq
  simp only [reindex_apply, submatrix_apply, place_apply, kroneckerMap_apply, one_apply,
    hp, hq, Equiv.symm_apply_apply, ← hpq, mul_ite, mul_one, mul_zero]

omit [∀ v, Fintype (X v)] in
/-- **A placement in product coordinates, on the right.** If an identification `g` of the
configurations with `C × R` reads the part on `D` in its second factor and determines the
configuration outside `D` by its first factor, then the placement of `K` on `D` is `1 ⊗ K` in
these coordinates. -/
theorem reindex_place_eq_one_kronecker (g : Config X ≃ C × R) (g₁ : RegionConfig X D ≃ R)
    (h₁ : ∀ σ, (g σ).2 = g₁ fun v ↦ σ v)
    (h₂ : ∀ σ τ, (g σ).1 = (g τ).1 ↔ ∀ v ∉ D, σ v = τ v)
    (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    reindex g g (place D K) = (1 : Matrix C C ℂ) ⊗ₖ reindex g₁ g₁ K := by
  ext p q
  have hp := h₁ (g.symm p)
  have hq := h₁ (g.symm q)
  have hpq := h₂ (g.symm p) (g.symm q)
  simp only [Equiv.apply_symm_apply] at hp hq hpq
  simp only [reindex_apply, submatrix_apply, place_apply, kroneckerMap_apply, one_apply,
    hp, hq, Equiv.symm_apply_apply, ← hpq, ite_mul, one_mul, zero_mul]

end Coordinates

/-! ### Three regions -/

variable {a b : Finset V}

private theorem not_mem_of_mem_compl_union_left {v : V} (hv : v ∈ (a ∪ b)ᶜ) : v ∉ a := by
  simp_all

private theorem not_mem_of_mem_compl_union_right {v : V} (hv : v ∈ (a ∪ b)ᶜ) : v ∉ b := by
  simp_all

private theorem mem_compl_union {v : V} (ha : v ∉ a) (hb : v ∉ b) : v ∈ (a ∪ b)ᶜ := by
  simp [ha, hb]

/-- The configurations of the system as triples of configurations of `a`, of the sites outside
`a ∪ b`, and of `b`, for disjoint regions `a` and `b`. -/
def tripartiteEquiv (X : V → Type*) (hab : Disjoint a b) :
    Config X ≃ RegionConfig X a × (RegionConfig X (a ∪ b)ᶜ × RegionConfig X b) where
  toFun σ := (fun v ↦ σ v, fun v ↦ σ v, fun v ↦ σ v)
  invFun p v := if ha : v ∈ a then p.1 ⟨v, ha⟩ else if hb : v ∈ b then p.2.2 ⟨v, hb⟩ else
    p.2.1 ⟨v, mem_compl_union ha hb⟩
  left_inv σ := by
    funext v
    by_cases ha : v ∈ a
    · simp [ha]
    · by_cases hb : v ∈ b <;> simp [ha, hb]
  right_inv p := by
    refine Prod.ext (funext fun v ↦ by simp [v.2]) (Prod.ext (funext fun v ↦ ?_)
      (funext fun v ↦ ?_))
    · simp [not_mem_of_mem_compl_union_left v.2, not_mem_of_mem_compl_union_right v.2]
    · simp [Finset.disjoint_right.mp hab v.2, v.2]

/-- The configurations of `bᶜ` as pairs of configurations of `a` and of `(a ∪ b)ᶜ`. -/
def complRightEquiv (X : V → Type*) (hab : Disjoint a b) :
    RegionConfig X bᶜ ≃ RegionConfig X a × RegionConfig X (a ∪ b)ᶜ where
  toFun σ := (fun v ↦ σ ⟨v, Finset.mem_compl.mpr (Finset.disjoint_left.mp hab v.2)⟩,
    fun v ↦ σ ⟨v, Finset.mem_compl.mpr (not_mem_of_mem_compl_union_right v.2)⟩)
  invFun p v := if ha : v.1 ∈ a then p.1 ⟨v, ha⟩ else
    p.2 ⟨v, mem_compl_union ha (Finset.mem_compl.mp v.2)⟩
  left_inv σ := by
    funext v
    by_cases ha : v.1 ∈ a <;> simp [ha]
  right_inv p := by
    refine Prod.ext (funext fun v ↦ by simp [v.2]) (funext fun v ↦ ?_)
    simp [not_mem_of_mem_compl_union_left v.2]

/-- The configurations of `aᶜ` as pairs of configurations of `(a ∪ b)ᶜ` and of `b`. -/
def complLeftEquiv (X : V → Type*) (hab : Disjoint a b) :
    RegionConfig X aᶜ ≃ RegionConfig X (a ∪ b)ᶜ × RegionConfig X b where
  toFun σ := (fun v ↦ σ ⟨v, Finset.mem_compl.mpr (not_mem_of_mem_compl_union_left v.2)⟩,
    fun v ↦ σ ⟨v, Finset.mem_compl.mpr (Finset.disjoint_right.mp hab v.2)⟩)
  invFun p v := if hb : v.1 ∈ b then p.2 ⟨v, hb⟩ else
    p.1 ⟨v, mem_compl_union (Finset.mem_compl.mp v.2) hb⟩
  left_inv σ := by
    funext v
    by_cases hb : v.1 ∈ b <;> simp [hb]
  right_inv p := by
    refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ by simp [v.2])
    simp [not_mem_of_mem_compl_union_right v.2]

variable (hab : Disjoint a b)

/-- The tensor lift from `a × m` is the reassociation of `M ⊗ 1`. -/
private theorem liftAX_eq {A M' B : Type*} [Fintype A] [DecidableEq A] [Fintype M']
    [DecidableEq M'] [Fintype B] [DecidableEq B] (N : Matrix (A × M') (A × M') ℂ) :
    liftAX (B := B) N =
      reindex (Equiv.prodAssoc A M' B) (Equiv.prodAssoc A M' B) (N ⊗ₖ (1 : Matrix B B ℂ)) :=
  rfl

/-- In the coordinates `tripartiteEquiv`, the placement on `a` is the lift `K ⊗ 1`. -/
theorem reindex_place_left (K : Matrix (RegionConfig X a) (RegionConfig X a) ℂ) :
    reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) (place a K) = liftA K := by
  refine (reindex_place_eq_kronecker_one _ (Equiv.refl _) (fun _ ↦ rfl) (fun σ τ ↦ ?_) K).trans
    (by simp [liftA])
  simp only [tripartiteEquiv, Equiv.coe_fn_mk, Prod.mk.injEq, funext_iff, Subtype.forall]
  constructor
  · intro h v hv
    by_cases hb : v ∈ b
    · exact h.2 v hb
    · exact h.1 v (mem_compl_union hv hb)
  · intro h
    exact ⟨fun v hv ↦ h v (not_mem_of_mem_compl_union_left hv),
      fun v hv ↦ h v (Finset.disjoint_right.mp hab hv)⟩

/-- In the coordinates `tripartiteEquiv`, the placement on `b` is the lift `1 ⊗ 1 ⊗ K`. -/
theorem reindex_place_right (K : Matrix (RegionConfig X b) (RegionConfig X b) ℂ) :
    reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) (place b K) = liftB K := by
  have h := reindex_place_eq_one_kronecker
    ((tripartiteEquiv X hab).trans (Equiv.prodAssoc _ _ _).symm) (Equiv.refl _) (fun _ ↦ rfl)
    (fun σ τ ↦ ?_) K
  · ext p q
    have hpq := congrFun (congrFun h ((Equiv.prodAssoc _ _ _).symm p))
      ((Equiv.prodAssoc _ _ _).symm q)
    simp only [reindex_apply, submatrix_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply] at hpq
    rw [reindex_apply, submatrix_apply, hpq]
    simp only [liftB, rightKroneckerEmbed_apply, kroneckerMap_apply, one_apply,
      Equiv.prodAssoc_symm_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_id_id]
    split_ifs <;> simp_all
  · simp only [Equiv.trans_apply, tripartiteEquiv, Equiv.coe_fn_mk, Equiv.prodAssoc_symm_apply,
      Prod.mk.injEq, funext_iff, Subtype.forall]
    constructor
    · intro h v hv
      by_cases ha : v ∈ a
      · exact h.1 v ha
      · exact h.2 v (mem_compl_union ha hv)
    · intro h
      exact ⟨fun v hv ↦ h v (Finset.disjoint_left.mp hab hv),
        fun v hv ↦ h v (not_mem_of_mem_compl_union_right hv)⟩

/-- In the coordinates `tripartiteEquiv`, the placement on `bᶜ` is the lift from `a × m`. -/
theorem reindex_place_compl_right (K : Matrix (RegionConfig X bᶜ) (RegionConfig X bᶜ) ℂ) :
    reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) (place bᶜ K) =
      liftAX (reindex (complRightEquiv X hab) (complRightEquiv X hab) K) := by
  have h := reindex_place_eq_kronecker_one
    ((tripartiteEquiv X hab).trans (Equiv.prodAssoc _ _ _).symm) (complRightEquiv X hab)
    (fun _ ↦ rfl) (fun σ τ ↦ ?_) K
  · rw [liftAX_eq, ← h]
    ext p q
    simp
  · simp only [Equiv.trans_apply, tripartiteEquiv, Equiv.coe_fn_mk, Equiv.prodAssoc_symm_apply,
      funext_iff, Subtype.forall, Finset.mem_compl, not_not]

/-- In the coordinates `tripartiteEquiv`, the placement on `aᶜ` is the lift from `m × b`. -/
theorem reindex_place_compl_left (K : Matrix (RegionConfig X aᶜ) (RegionConfig X aᶜ) ℂ) :
    reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) (place aᶜ K) =
      liftXB (reindex (complLeftEquiv X hab) (complLeftEquiv X hab) K) := by
  refine (reindex_place_eq_one_kronecker _ (complLeftEquiv X hab) (fun _ ↦ rfl)
    (fun σ τ ↦ ?_) K).trans (by simp [liftXB])
  simp only [tripartiteEquiv, Equiv.coe_fn_mk, funext_iff, Subtype.forall, Finset.mem_compl,
    not_not]

/-- **Decorrelation on a system of sites.** The regions `a` and `b` are decorrelated in `P`,
in the tripartite coordinates, exactly when `P (O_a ⊗ 1) (1 - P) (O_b ⊗ 1) P = 0` for all
operators `O_a` on `a` and `O_b` on `b`. CPSV16, arXiv:1606.00608, Appendix D.2, Definition
D.1, lines 2187--2191, in its complex-linear form. -/
theorem isDecorrelated_reindex_iff {P : Matrix (Config X) (Config X) ℂ} :
    IsDecorrelated (reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) P) ↔
      ∀ (Oa : Matrix (RegionConfig X a) (RegionConfig X a) ℂ)
        (Ob : Matrix (RegionConfig X b) (RegionConfig X b) ℂ),
        P * place a Oa * (1 - P) * place b Ob * P = 0 := by
  set Ψ := reindexAlgEquiv ℂ ℂ (tripartiteEquiv X hab)
  have hΨ (M : Matrix (Config X) (Config X) ℂ) :
      Ψ M = reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) M := rfl
  refine forall_congr' fun Oa ↦ forall_congr' fun Ob ↦ ?_
  rw [← reindex_place_left hab, ← reindex_place_right hab, ← hΨ, ← hΨ, ← hΨ, ← map_one Ψ,
    ← map_sub, ← map_mul, ← map_mul, ← map_mul, ← map_mul, map_eq_zero_iff Ψ Ψ.injective]

/-! ### Commuting parent Hamiltonians -/

/-- **Commuting parent Hamiltonian.** An operator `P` on the system has a commuting parent
Hamiltonian on the complements `bᶜ` and `aᶜ` of two regions when there is a two-term
interaction, with the first term supported on `bᶜ` and the second on `aᶜ`, whose terms are
commuting orthogonal projections and whose zero space is the range of `P`. The terms are
`1 - P_{am}` and `1 - P_{mb}` for the projections onto the local ground spaces, and the zero
space is the intersection of the two placed ground spaces. CPSV16, arXiv:1606.00608, Appendix
D.2, Definition D.2, lines 2205--2218. -/
def HasCommutingParentHamiltonian (a b : Finset V) (P : Matrix (Config X) (Config X) ℂ) :
    Prop :=
  ∃ Φ : Interaction X ![bᶜ, aᶜ], (∀ i, IsStarProjection (Φ.term i)) ∧
    Commute (Φ.term 0) (Φ.term 1) ∧ Φ.zeroSpace = LinearMap.range (toEuclideanLin P)

/-- A vector lies in the range of an idempotent matrix exactly when the matrix fixes it. -/
private theorem mem_range_toEuclideanLin_iff {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : P * P = P) {ψ : EuclideanSpace ℂ n} :
    ψ ∈ LinearMap.range (toEuclideanLin P) ↔ P *ᵥ WithLp.ofLp ψ = WithLp.ofLp ψ := by
  constructor
  · rintro ⟨φ, rfl⟩
    simp [toLpLin_apply, mulVec_mulVec, hP]
  · intro h
    exact ⟨ψ, by simp [toLpLin_apply, h]⟩

/-- For a two-term interaction, a vector lies in the zero space exactly when both
complementary operators fix it. -/
private theorem mem_zeroSpace_two_iff {S : Fin 2 → Finset V} {Φ : Interaction X S}
    {ψ : EuclideanSpace ℂ (Config X)} :
    ψ ∈ Φ.zeroSpace ↔ (1 - Φ.term 0) *ᵥ WithLp.ofLp ψ = WithLp.ofLp ψ ∧
      (1 - Φ.term 1) *ᵥ WithLp.ofLp ψ = WithLp.ofLp ψ := by
  simp [Interaction.mem_zeroSpace_iff, Fin.forall_fin_two, sub_mulVec]

/-- **The ground projection is the product.** If `P` is an orthogonal projection with a
commuting parent Hamiltonian, then `P` is the product of the two complementary projections
`1 - h₀` and `1 - h₁` of its terms, in either order. CPSV16, arXiv:1606.00608, Appendix D.2,
lines 2205--2218 and 2279--2289. -/
theorem HasCommutingParentHamiltonian.eq_mul {P : Matrix (Config X) (Config X) ℂ}
    (hP : IsStarProjection P) {Φ : Interaction X ![bᶜ, aᶜ]}
    (hΦ : ∀ i, IsStarProjection (Φ.term i)) (hcomm : Commute (Φ.term 0) (Φ.term 1))
    (hzero : Φ.zeroSpace = LinearMap.range (toEuclideanLin P)) :
    (1 - Φ.term 0) * (1 - Φ.term 1) = P ∧ (1 - Φ.term 1) * (1 - Φ.term 0) = P := by
  have hS (i : Fin 2) : IsStarProjection (1 - Φ.term i) := (hΦ i).one_sub
  have hcomm' : Commute (1 - Φ.term 0) (1 - Φ.term 1) :=
    (Commute.one_left _).sub_left ((Commute.one_right _).sub_right hcomm)
  have hS01 : IsStarProjection ((1 - Φ.term 0) * (1 - Φ.term 1)) :=
    (hS 0).mul (hS 1) hcomm'
  have hrange : LinearMap.range (toLin' ((1 - Φ.term 0) * (1 - Φ.term 1))) =
      LinearMap.range (toLin' P) := by
    rw [range_mul_eq_inter _ _ (hS 0).isIdempotentElem.eq (hS 1).isIdempotentElem.eq
      hcomm'.eq]
    ext f
    have hf := hzero ▸ (mem_zeroSpace_two_iff (Φ := Φ) (ψ := WithLp.toLp 2 f))
    rw [mem_range_toEuclideanLin_iff hP.isIdempotentElem.eq] at hf
    have hidem {M : Matrix (Config X) (Config X) ℂ} (hM : M * M = M) :
        f ∈ LinearMap.range (toLin' M) ↔ M *ᵥ f = f := by
      refine ⟨?_, fun h ↦ ⟨f, h⟩⟩
      rintro ⟨g, rfl⟩
      simp [mulVec_mulVec, hM]
    rw [Submodule.mem_inf, hidem (hS 0).isIdempotentElem.eq, hidem (hS 1).isIdempotentElem.eq,
      hidem hP.isIdempotentElem.eq]
    exact hf.symm
  have h01 := hermitian_idempotent_eq_of_range_eq _ _ hS01.isSelfAdjoint
    hS01.isIdempotentElem.eq hP.isSelfAdjoint hP.isIdempotentElem.eq hrange
  exact ⟨h01, hcomm'.eq.symm.trans h01⟩

/-- **Commuting parent Hamiltonians decorrelate.** An orthogonal projection with a commuting
parent Hamiltonian on `bᶜ` and `aᶜ` decorrelates the regions `a` and `b`. The only-if
direction of CPSV16, arXiv:1606.00608, Appendix D.2, Proposition D.3, lines 2279--2289. -/
theorem HasCommutingParentHamiltonian.isDecorrelated {P : Matrix (Config X) (Config X) ℂ}
    (hP : IsStarProjection P) (h : HasCommutingParentHamiltonian a b P) :
    IsDecorrelated (reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) P) := by
  obtain ⟨Φ, hΦ, hcomm, hzero⟩ := h
  obtain ⟨hprod, hrev⟩ := HasCommutingParentHamiltonian.eq_mul hP hΦ hcomm hzero
  have hmem₀ : Φ.term 0 ∈ supportedOperators X bᶜ := Φ.mem 0
  have hmem₁ : Φ.term 1 ∈ supportedOperators X aᶜ := Φ.mem 1
  obtain ⟨K₀, hK₀⟩ := exists_eq_place_of_mem_supportedOperators hmem₀
  obtain ⟨K₁, hK₁⟩ := exists_eq_place_of_mem_supportedOperators hmem₁
  set Ψ := reindexAlgEquiv ℂ ℂ (tripartiteEquiv X hab)
  have hΨ (M : Matrix (Config X) (Config X) ℂ) :
      Ψ M = reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) M := rfl
  set SAX := liftAX (B := RegionConfig X b)
    (reindex (complRightEquiv X hab) (complRightEquiv X hab) (1 - K₀))
  set SXB := liftXB (A := RegionConfig X a)
    (reindex (complLeftEquiv X hab) (complLeftEquiv X hab) (1 - K₁))
  have hAX : Ψ (1 - Φ.term 0) = SAX := by
    rw [hΨ, hK₀, ← place_one (D := bᶜ), ← place_sub]
    exact reindex_place_compl_right hab _
  have hXB : Ψ (1 - Φ.term 1) = SXB := by
    rw [hΨ, hK₁, ← place_one (D := aᶜ), ← place_sub]
    exact reindex_place_compl_left hab _
  rw [← hΨ]
  set P' := Ψ P
  have hproduct : SAX * SXB = P' := by rw [← hAX, ← hXB, ← map_mul, hprod]
  have hrev' : SXB * SAX = P' := by rw [← hAX, ← hXB, ← map_mul, hrev]
  have hPidem : P' * P' = P' := by rw [← map_mul, hP.isIdempotentElem.eq]
  have hquad : SXB * P' * SAX = P' * P' := by
    calc
      SXB * P' * SAX = SXB * (SAX * SXB) * SAX := by rw [hproduct]
      _ = (SXB * SAX) * (SXB * SAX) := by noncomm_ring
      _ = P' * P' := by rw [hrev']
  have hmiddle : SXB * (1 - P') * SAX = 0 := by
    calc
      SXB * (1 - P') * SAX = SXB * SAX - SXB * P' * SAX := by noncomm_ring
      _ = P' - P' * P' := by rw [hrev', hquad]
      _ = 0 := by rw [hPidem, sub_self]
  intro OA OB
  have hAcomm : SXB * liftA OA = liftA OA * SXB := (liftA_comm_liftXB OA _).symm
  have hBcomm : liftB OB * SAX = SAX * liftB OB := liftB_comm_liftAX OB _
  calc
    P' * liftA OA * (1 - P') * liftB OB * P' =
        (SAX * SXB) * liftA OA * (1 - P') * liftB OB * (SAX * SXB) := by rw [hproduct]
    _ = SAX * (SXB * liftA OA) * (1 - P') * (liftB OB * SAX) * SXB := by noncomm_ring
    _ = SAX * (liftA OA * SXB) * (1 - P') * (SAX * liftB OB) * SXB := by
      rw [hAcomm, hBcomm]
    _ = SAX * liftA OA * (SXB * (1 - P') * SAX) * liftB OB * SXB := by noncomm_ring
    _ = 0 := by rw [hmiddle]; simp

/-- **Decorrelation gives a commuting parent Hamiltonian.** If the regions `a` and `b` are
decorrelated in an orthogonal projection `P`, then the projections onto the supports of the two
marginals of `P` on `bᶜ` and on `aᶜ` give a commuting parent Hamiltonian. The if direction of
CPSV16, arXiv:1606.00608, Appendix D.2, Proposition D.3, lines 2225--2277. -/
theorem hasCommutingParentHamiltonian_of_isDecorrelated {P : Matrix (Config X) (Config X) ℂ}
    (hP : IsStarProjection P)
    (hdec : IsDecorrelated (reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) P)) :
    HasCommutingParentHamiltonian a b P := by
  set Ψ := reindexAlgEquiv ℂ ℂ (tripartiteEquiv X hab)
  have hΨ (M : Matrix (Config X) (Config X) ℂ) :
      Ψ M = reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) M := rfl
  have hstar (M : Matrix (Config X) (Config X) ℂ) : (Ψ M)ᴴ = Ψ Mᴴ := by
    rw [hΨ, hΨ, conjTranspose_reindex]
  rw [← hΨ] at hdec
  have hPherm : (Ψ P).IsHermitian := by
    rw [IsHermitian, hstar]
    exact congrArg Ψ hP.isSelfAdjoint.star_eq
  have hPidem : Ψ P * Ψ P = Ψ P := by rw [← map_mul, hP.isIdempotentElem.eq]
  obtain ⟨hrevP, hprodP⟩ := supportProducts_eq hPherm hPidem hdec
  set GAX := supportAX hPherm
  set GXB := supportXB hPherm
  have hGAX : IsStarProjection GAX :=
    ⟨(partialTraceRight_isHermitian (groupAX_isHermitian hPherm)).supportProj_idem,
      (partialTraceRight_isHermitian (groupAX_isHermitian hPherm)).supportProj_isHermitian⟩
  have hGXB : IsStarProjection GXB :=
    ⟨(partialTraceLeft_isHermitian hPherm).supportProj_idem,
      (partialTraceLeft_isHermitian hPherm).supportProj_isHermitian⟩
  set K₀ := reindex (complRightEquiv X hab).symm (complRightEquiv X hab).symm GAX
  set K₁ := reindex (complLeftEquiv X hab).symm (complLeftEquiv X hab).symm GXB
  have hK₀ : Ψ (place bᶜ K₀) = liftAX GAX := by
    rw [hΨ, reindex_place_compl_right hab]
    simp [K₀]
  have hK₁ : Ψ (place aᶜ K₁) = liftXB GXB := by
    rw [hΨ, reindex_place_compl_left hab]
    simp [K₁]
  have hlift₀ : IsStarProjection (liftAX (B := RegionConfig X b) GAX) :=
    ⟨by rw [IsIdempotentElem, ← liftAX_mul, hGAX.isIdempotentElem.eq],
      by rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_liftAX,
        ← star_eq_conjTranspose, hGAX.isSelfAdjoint.star_eq]⟩
  have hlift₁ : IsStarProjection (liftXB (A := RegionConfig X a) GXB) :=
    ⟨by rw [IsIdempotentElem, ← liftXB_mul, hGXB.isIdempotentElem.eq],
      by rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_liftXB,
        ← star_eq_conjTranspose, hGXB.isSelfAdjoint.star_eq]⟩
  have hpull {M : Matrix (Config X) (Config X) ℂ} (hM : IsStarProjection (Ψ M)) :
      IsStarProjection M := by
    refine ⟨Ψ.injective (by rw [map_mul, hM.isIdempotentElem.eq]), Ψ.injective ?_⟩
    exact (hstar M).symm.trans hM.isSelfAdjoint.star_eq
  let Φ : Interaction X ![bᶜ, aᶜ] :=
    ⟨![1 - place bᶜ K₀, 1 - place aᶜ K₁], fun i ↦ by
      fin_cases i
      · change 1 - place bᶜ K₀ ∈ supportedOperators X bᶜ
        rw [← place_one (D := bᶜ), ← place_sub]
        exact place_mem_supportedOperators _
      · change 1 - place aᶜ K₁ ∈ supportedOperators X aᶜ
        rw [← place_one (D := aᶜ), ← place_sub]
        exact place_mem_supportedOperators _⟩
  have hΦ0 : Φ.term 0 = 1 - place bᶜ K₀ := rfl
  have hΦ1 : Φ.term 1 = 1 - place aᶜ K₁ := rfl
  have hproj₀ : IsStarProjection (place bᶜ K₀) := hpull (hK₀ ▸ hlift₀)
  have hproj₁ : IsStarProjection (place aᶜ K₁) := hpull (hK₁ ▸ hlift₁)
  have hcomm₀₁ : Commute (place bᶜ K₀) (place aᶜ K₁) := by
    refine Ψ.injective ?_
    rw [map_mul, map_mul, hK₀, hK₁, hprodP, hrevP]
  have hprod : place bᶜ K₀ * place aᶜ K₁ = P := Ψ.injective (by rw [map_mul, hK₀, hK₁, hprodP])
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hproj₀.one_sub
    · exact hproj₁.one_sub
  · rw [hΦ0, hΦ1]
    exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right hcomm₀₁)
  · ext ψ
    rw [mem_zeroSpace_two_iff, hΦ0, hΦ1, sub_sub_cancel, sub_sub_cancel,
      mem_range_toEuclideanLin_iff hP.isIdempotentElem.eq, ← hprod]
    constructor
    · rintro ⟨h₀, h₁⟩
      rw [← mulVec_mulVec, h₁, h₀]
    · intro h
      refine ⟨?_, ?_⟩
      · rw [← h, mulVec_mulVec, ← mul_assoc, hproj₀.isIdempotentElem.eq]
      · rw [← h, mulVec_mulVec, ← mul_assoc, ← hcomm₀₁.eq, mul_assoc,
          hproj₁.isIdempotentElem.eq]

/-- **CPSV16 Proposition D.3.** For disjoint regions `a` and `b`, an orthogonal projection `P`
on the system has a commuting parent Hamiltonian on `bᶜ` and `aᶜ` exactly when `a` and `b` are
decorrelated in `P`. arXiv:1606.00608, Appendix D.2, Proposition D.3, lines 2221--2289. -/
theorem hasCommutingParentHamiltonian_iff_isDecorrelated {P : Matrix (Config X) (Config X) ℂ}
    (hP : IsStarProjection P) :
    HasCommutingParentHamiltonian a b P ↔
      IsDecorrelated (reindex (tripartiteEquiv X hab) (tripartiteEquiv X hab) P) :=
  ⟨HasCommutingParentHamiltonian.isDecorrelated hab hP,
    hasCommutingParentHamiltonian_of_isDecorrelated hab hP⟩

end ManyBody
