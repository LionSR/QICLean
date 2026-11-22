/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Equal bipartite sums of linearly independent families

Two finite bipartite sums `∑_μ a_μ ⊗ a'_μ = ∑_ν b_ν ⊗ b'_ν` of complex-valued functions, with
the same number of terms and linearly independent factor families, determine each other up to
one coefficient matrix: a dual coordinate functional isolates one member of a linearly
independent family, applying these functionals expresses `a` through `b` with a matrix `g`, the
same `g` expresses `b'` through `a'`, and comparison with the reverse relation shows that the
two coefficient matrices are mutually inverse.

## Main results

* `LinearIndependent.exists_dual_isolating`: a dual functional isolates a chosen member of a
  linearly independent family.
* `LinearIndependent.exists_left_eq_sum_of_sum_mul_eq` and
  `LinearIndependent.right_eq_sum_of_sum_mul_eq`: equal bipartite sums are related on both
  sides by the same coefficient matrix.
* `LinearIndependent.sum_mul_eq_ite_of_eq_sum`: the forward coefficient matrix followed by the
  reverse one is the identity.

## References

* A. Molnár, N. Schuch, F. Verstraete, and J. I. Cirac, arXiv:1804.04964,
  Section 3, Lemma `inj_equal_tensors_2`, lines 1157--1204 of
  `Papers/1804.04964/paper_normal.tex`.

Moved from TNLean, `TNLean/Algebra/OperatorSchmidt.lean` at commit `49b78ed821` (Apache-2.0).
Changes: the namespace `TNLean.PEPS` became `LinearIndependent`, and the three statements
about bipartite sums were renamed after their content.
-/

open scoped BigOperators

namespace LinearIndependent

/-- A linearly independent finite family in a complex vector space admits a dual
functional isolating each index: for every index `μ₀` there is a linear
functional vanishing on the other family members and equal to `1` on the
`μ₀`-th one. This is the coordinate functional of the family, extended from its
span to the whole space.

This is the dual-functional step of
arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2: isolating one family member
reads off a single column of the coefficient matrix. -/
theorem exists_dual_isolating
    {K W : Type*} [DecidableEq K]
    [AddCommGroup W] [Module ℂ W]
    {f : K → W} (hf : LinearIndependent ℂ f) (μ₀ : K) :
    ∃ ψ : W →ₗ[ℂ] ℂ, ∀ μ : K, ψ (f μ) = if μ = μ₀ then 1 else 0 := by
  classical
  set φ : (Submodule.span ℂ (Set.range f)) →ₗ[ℂ] ℂ :=
    (Finsupp.lapply μ₀ : (K →₀ ℂ) →ₗ[ℂ] ℂ).comp (hf.repr) with hφ
  obtain ⟨ψ, hψ⟩ := φ.exists_extend
  refine ⟨ψ, fun μ => ?_⟩
  have hmem : f μ ∈ Submodule.span ℂ (Set.range f) :=
    Submodule.subset_span ⟨μ, rfl⟩
  have key : ψ (f μ) = φ ⟨f μ, hmem⟩ := by
    have := congrArg (fun L => L ⟨f μ, hmem⟩) hψ
    simpa using this
  rw [key, hφ]
  simp only [LinearMap.comp_apply, Finsupp.lapply_apply]
  rw [hf.repr_eq_single μ ⟨f μ, hmem⟩ rfl]
  simp [Finsupp.single_apply, eq_comm]

/-- First comparison of equal bipartite sums. If two bipartite tensors
`∑_μ a_μ ⊗ a'_μ` and `∑_ν b_ν ⊗ b'_ν` agree and the right family `a'`
is linearly independent, then each left vector `a_μ` lies in the span of the
left vectors `b_ν`, with the coefficient matrix `g μ ν` given by the dual
functional of `a'_μ` evaluated on `b'_ν`.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`. -/
theorem exists_left_eq_sum_of_sum_mul_eq
    {K V1 V2 : Type*} [Fintype K]
    {a b : K → V1 → ℂ} {a' b' : K → V2 → ℂ}
    (ha' : LinearIndependent ℂ (fun μ : K => (a' μ : V2 → ℂ)))
    (hcontr : ∀ (p1 : V1) (p2 : V2),
      (∑ μ : K, a μ p1 * a' μ p2) = ∑ ν : K, b ν p1 * b' ν p2) :
    ∃ g : K → K → ℂ, ∀ (μ : K) (p1 : V1),
      a μ p1 = ∑ ν : K, g μ ν * b ν p1 := by
  classical
  choose ψ hψ using fun μ₀ : K => exists_dual_isolating ha' μ₀
  refine ⟨fun μ ν => ψ μ (b' ν), fun μ₀ p1 => ?_⟩
  have hvec : (∑ μ : K, a μ p1 • (a' μ : V2 → ℂ))
      = ∑ ν : K, b ν p1 • (b' ν : V2 → ℂ) := by
    funext p2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hcontr p1 p2
  have happ := congrArg (ψ μ₀) hvec
  rw [map_sum, map_sum] at happ
  simp only [map_smul, smul_eq_mul] at happ
  rw [Finset.sum_congr rfl (fun μ _ => by rw [hψ μ₀ μ])] at happ
  simp only [mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq' Finset.univ μ₀ (fun μ => a μ p1), Finset.mem_univ, ite_true] at happ
  rw [happ]
  refine Finset.sum_congr rfl ?_
  intro ν _
  ring

/-- Second comparison of equal bipartite sums. Continuing from
`exists_left_eq_sum_of_sum_mul_eq`, substituting `a_μ = ∑_ν g μ ν • b_ν` into the bipartite identity
and using linear independence of the left family `b` forces the right vector
`b'_ν` to equal `∑_μ g μ ν • a'_μ` with the *same* coefficient matrix `g`.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`. -/
theorem right_eq_sum_of_sum_mul_eq
    {K V1 V2 : Type*} [Fintype K]
    {a b : K → V1 → ℂ} {a' b' : K → V2 → ℂ} {g : K → K → ℂ}
    (hb : LinearIndependent ℂ (fun ν : K => (b ν : V1 → ℂ)))
    (hcontr : ∀ (p1 : V1) (p2 : V2),
      (∑ μ : K, a μ p1 * a' μ p2) = ∑ ν : K, b ν p1 * b' ν p2)
    (hg1 : ∀ (μ : K) (p1 : V1), a μ p1 = ∑ ν : K, g μ ν * b ν p1) :
    ∀ (ν : K) (p2 : V2), b' ν p2 = ∑ μ : K, g μ ν * a' μ p2 := by
  classical
  choose χ hχ using fun ν₀ : K => exists_dual_isolating hb ν₀
  intro ν₀ p2
  have hvec : (∑ μ : K, a' μ p2 • (a μ : V1 → ℂ))
      = ∑ ν : K, b' ν p2 • (b ν : V1 → ℂ) := by
    funext p1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have := hcontr p1 p2
    rw [Finset.sum_congr rfl (fun μ _ => mul_comm (a μ p1) (a' μ p2))] at this
    rw [Finset.sum_congr rfl (fun ν _ => mul_comm (b ν p1) (b' ν p2))] at this
    exact this
  have hsubst : (∑ μ : K, a' μ p2 • (a μ : V1 → ℂ))
      = ∑ ν : K, (∑ μ : K, g μ ν * a' μ p2) • (b ν : V1 → ℂ) := by
    funext p1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun μ _ => by rw [hg1 μ p1])]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro ν _
    refine Finset.sum_congr rfl ?_
    intro μ _
    ring
  have hcomb : (∑ ν : K, (∑ μ : K, g μ ν * a' μ p2) • (b ν : V1 → ℂ))
      = ∑ ν : K, b' ν p2 • (b ν : V1 → ℂ) := by rw [← hsubst, hvec]
  have happ := congrArg (χ ν₀) hcomb
  rw [map_sum, map_sum] at happ
  simp only [map_smul, smul_eq_mul, hχ ν₀, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq' Finset.univ ν₀, Finset.mem_univ, ite_true] at happ
  rw [happ]

/-- Invertibility of the coefficient matrix. If `a = g·b` and `b = g'·a` with the family `a`
linearly independent, then the forward coefficient matrix followed by the reverse one
is the identity: `∑_ν g μ ν * g' ν κ = δ_{μκ}`.

Source: arXiv:1804.04964, Section 3, Lemma inj_equal_tensors_2, lines
1157--1204 of `Papers/1804.04964/paper_normal.tex`. -/
theorem sum_mul_eq_ite_of_eq_sum
    {K V1 : Type*} [Fintype K] [DecidableEq K]
    {a b : K → V1 → ℂ} {g g' : K → K → ℂ}
    (ha : LinearIndependent ℂ (fun μ : K => (a μ : V1 → ℂ)))
    (hg1 : ∀ (μ : K) (p1 : V1), a μ p1 = ∑ ν : K, g μ ν * b ν p1)
    (hg1' : ∀ (ν : K) (p1 : V1), b ν p1 = ∑ κ : K, g' ν κ * a κ p1) :
    ∀ μ κ : K, (∑ ν : K, g μ ν * g' ν κ) = if μ = κ then 1 else 0 := by
  classical
  intro μ₀
  have hrep : ∀ p1 : V1,
      a μ₀ p1 = ∑ κ : K, (∑ ν : K, g μ₀ ν * g' ν κ) * a κ p1 := by
    intro p1
    rw [hg1 μ₀ p1]
    rw [Finset.sum_congr rfl (fun ν _ => by rw [hg1' ν p1])]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro κ _
    refine Finset.sum_congr rfl ?_
    intro ν _
    ring
  have hcoeff : (fun p1 : V1 => a μ₀ p1) =
      ∑ κ : K, (∑ ν : K, g μ₀ ν * g' ν κ) • (a κ : V1 → ℂ) := by
    funext p1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hrep p1
  have hself : (fun p1 : V1 => a μ₀ p1) =
      ∑ κ : K, (if κ = μ₀ then (1:ℂ) else 0) • (a κ : V1 → ℂ) := by
    funext p1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq' Finset.univ μ₀, Finset.mem_univ, ite_true]
  have hdiff : (∑ κ : K,
      ((∑ ν : K, g μ₀ ν * g' ν κ) - (if κ = μ₀ then (1:ℂ) else 0)) •
        (a κ : V1 → ℂ)) = 0 := by
    funext p1
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, sub_mul, Pi.zero_apply]
    rw [Finset.sum_sub_distrib]
    have h1 := congrFun hcoeff p1
    have h2 := congrFun hself p1
    rw [Finset.sum_apply] at h1 h2
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
    ring
  have hzero := (Fintype.linearIndependent_iff.1 ha) _ hdiff
  intro κ₀
  have := hzero κ₀
  rw [sub_eq_zero] at this
  rw [this]
  by_cases h : μ₀ = κ₀
  · subst h; simp
  · rw [ite_eq_right (fun hk => h hk.symm), ite_eq_right h]

end LinearIndependent
