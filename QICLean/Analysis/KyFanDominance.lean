/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.VectorSubmajorization
import QICLean.Analysis.PolarUnitaryCorrection
import QICLean.Analysis.TraceNormAbs
import Mathlib.Analysis.Convex.Jensen

/-!
# Unitarily invariant norms and Ky Fan dominance

A norm `N` on `M_d(ℂ)` is unitarily invariant if `N (U A V) = N A` for all unitaries `U, V`.
Its value depends only on the singular values of `A`, and the map `x ↦ N (diag x)` on real
vectors is convex, invariant under permutations and sign changes. This file proves Wolf's Ky Fan
dominance theorem: if every Ky Fan norm of `A` dominates the corresponding Ky Fan norm of `B`,
then `N A ≥ N B` for every unitarily invariant norm `N`.

The proof: the Ky Fan hypothesis is the weak submajorization `s(B) ≺_w s(A)` of the singular
value vectors. Some `z ≺ s(A)` dominates `s(B)` entrywise, and `z` lies in the convex hull of
the permutations of `s(A)`. Convexity bounds `N (diag z)` by `N (diag s(A)) = N A`, and the
sign-change invariance makes `x ↦ N (diag x)` monotone in the absolute values of the entries,
which bounds `N B = N (diag s(B))` by `N (diag z)`.

## Main definitions

* `Matrix.IsUnitarilyInvariantNorm`: a norm on `M_d(ℂ)` invariant under `A ↦ U A V`.
* `Matrix.singularValues`: the singular values `√λᵢ(A†A)`, in the eigenvalue order of `A†A`.
* `Matrix.kyFanNorm`: the Ky Fan `k`-norm, the sum of the `k` largest singular values.

## Main results

* `Matrix.IsUnitarilyInvariantNorm.apply_eq_diagonal_singularValues`: `N A = N (diag s(A))`.
* `Matrix.IsUnitarilyInvariantNorm.diagonal_le_of_abs_le`: monotonicity on diagonal matrices.
* `Matrix.IsUnitarilyInvariantNorm.le_of_kyFanNorm_le`: **Ky Fan dominance**, Wolf
  Theorem 8.2(5).

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 8.1, local source
  `Notes/WolfNoteTexSource/ch08_distance_measures.tex`: unitarily invariant norms,
  lines 53--61; Ky Fan norms, lines 68--72; Theorem "Unitarily invariant norms", item 5
  (Ky Fan dominance), lines 135--136.
-/

open Finset
open scoped BigOperators ComplexOrder

namespace Matrix

variable {d : ℕ}

/-- A **unitarily invariant norm** on `M_d(ℂ)`: a norm (triangle inequality, absolute
homogeneity, definiteness) with `N (U A V) = N A` for all unitaries `U, V`.
Wolf §8.1, `ch08_distance_measures.tex` lines 45--55. Sub-multiplicativity is not required. -/
structure IsUnitarilyInvariantNorm (N : Matrix (Fin d) (Fin d) ℂ → ℝ) : Prop where
  add_le : ∀ A B, N (A + B) ≤ N A + N B
  smul : ∀ (c : ℂ) A, N (c • A) = ‖c‖ * N A
  eq_zero : ∀ A, N A = 0 → A = 0
  unitary_mul_mul : ∀ U ∈ unitaryGroup (Fin d) ℂ, ∀ V ∈ unitaryGroup (Fin d) ℂ, ∀ A,
    N (U * A * V) = N A

/-- The singular values of `A`: the square roots of the eigenvalues of `A†A`, listed in the
order of `Matrix.IsHermitian.eigenvalues`. -/
noncomputable def singularValues (A : Matrix (Fin d) (Fin d) ℂ) : Fin d → ℝ :=
  fun i ↦ √((posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i)

theorem singularValues_nonneg (A : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    0 ≤ singularValues A i :=
  Real.sqrt_nonneg _

/-- The **Ky Fan `k`-norm** `‖A‖_(k)`: the sum of the `k` largest singular values of `A`,
counted with multiplicity. Wolf §8.1, `ch08_distance_measures.tex` lines 68--72. -/
noncomputable def kyFanNorm (A : Matrix (Fin d) (Fin d) ℂ) (k : ℕ) : ℝ :=
  TNLean.vectorPrefix (TNLean.decreasingSort (singularValues A)) k

/-- Singular value decomposition `A = U diag(s(A)) V` with unitary `U, V`, from the polar
decomposition `A = W √(A†A)` and the spectral decomposition of `A†A`. -/
theorem exists_unitary_mul_diagonal_singularValues_mul (A : Matrix (Fin d) (Fin d) ℂ) :
    ∃ U ∈ unitaryGroup (Fin d) ℂ, ∃ V ∈ unitaryGroup (Fin d) ℂ,
      A = U * diagonal (fun i ↦ (singularValues A i : ℂ)) * V := by
  obtain ⟨W, hW, -⟩ := exists_unitary_polar_correction A
  set hH := (posSemidef_conjTranspose_mul_self A).isHermitian
  set E := hH.eigenvectorUnitary
  refine ⟨(W : Matrix (Fin d) (Fin d) ℂ) * E, Submonoid.mul_mem _ W.2 E.2,
    star (E : Matrix (Fin d) (Fin d) ℂ), Unitary.star_mem E.2, ?_⟩
  conv_lhs => rw [hW, (posSemidef_conjTranspose_mul_self A).sqrt_eq_cfc_real_sqrt]
  rw [IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp only [Matrix.mul_assoc]
  rfl

namespace IsUnitarilyInvariantNorm

variable {N : Matrix (Fin d) (Fin d) ℂ → ℝ} (hN : IsUnitarilyInvariantNorm N)
include hN

theorem nonneg (A : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ N A := by
  have h := hN.add_le A (-A)
  have hneg : N (-A) = N A := by
    simpa using hN.smul (-1) A
  rw [add_neg_cancel, hneg] at h
  have h0 : N 0 = 0 := by simpa using hN.smul 0 0
  linarith

/-- A unitarily invariant norm depends only on the singular values.
Wolf §8.1, `ch08_distance_measures.tex` lines 55--57. -/
theorem apply_eq_diagonal_singularValues (A : Matrix (Fin d) (Fin d) ℂ) :
    N A = N (diagonal fun i ↦ (singularValues A i : ℂ)) := by
  obtain ⟨U, hU, V, hV, hA⟩ := exists_unitary_mul_diagonal_singularValues_mul A
  conv_lhs => rw [hA]
  exact hN.unitary_mul_mul U hU V hV _

/-- The diagonal matrix with real entries `x`. -/
local notation "diagR " x:max => Matrix.diagonal (fun i ↦ (((x : Fin _ → ℝ) i : ℝ) : ℂ))

theorem diagonal_comp_perm (x : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) :
    N (diagR (x ∘ σ)) = N (diagR x) := by
  have hP : σ.permMatrix ℂ ∈ unitaryGroup (Fin d) ℂ := by
    rw [mem_unitaryGroup_iff]
    ext i j
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Matrix.mul_apply, Matrix.one_apply,
      Equiv.toPEquiv_apply, eq_comm]
  have h : diagR (x ∘ σ) = σ.permMatrix ℂ * diagR x * star (σ.permMatrix ℂ) := by
    ext i j
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Matrix.mul_apply, diagonal_apply,
      Equiv.toPEquiv_apply]
    split_ifs with hij <;> simp [hij]
  rw [h]
  exact hN.unitary_mul_mul _ hP _ (Unitary.star_mem hP) _

theorem diagonal_mul_sign (x ε : Fin d → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    N (diagR (fun i ↦ ε i * x i)) = N (diagR x) := by
  have hD : diagR ε ∈ unitaryGroup (Fin d) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    ext i
    rcases hε i with h | h <;> simp [h]
  have h : diagR (fun i ↦ ε i * x i) = diagR ε * diagR x * 1 := by
    rw [Matrix.mul_one, diagonal_mul_diagonal]
    congr 1
    ext i
    push_cast
    rfl
  rw [h]
  exact hN.unitary_mul_mul _ hD _ (one_mem _) _

/-- `x ↦ N (diag x)` is convex. -/
theorem convexOn_diagonal : ConvexOn ℝ Set.univ fun x : Fin d → ℝ ↦ N (diagR x) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ ↦ ?_⟩
  have h : diagR (a • x + b • y) = (a : ℂ) • diagR x + (b : ℂ) • diagR y := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  dsimp only
  rw [h]
  refine (hN.add_le _ _).trans ?_
  rw [hN.smul, hN.smul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha,
    Real.norm_of_nonneg hb]
  rfl

/-- Changing one coordinate to one of smaller absolute value does not increase `N (diag ·)`. -/
theorem diagonal_update_le (z : Fin d → ℝ) (j : Fin d) {a : ℝ} (ha : |a| ≤ |z j|) :
    N (diagR (Function.update z j a)) ≤ N (diagR z) := by
  classical
  by_cases hz : z j = 0
  · have ha0 : a = 0 := by simpa [hz] using ha
    have : Function.update z j a = z := by
      rw [ha0, ← hz]; exact Function.update_eq_self j z
    rw [this]
  set ε : Fin d → ℝ := Function.update (fun _ ↦ 1) j (-1)
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i ↦ by
    by_cases hi : i = j
    · subst hi; simp [ε]
    · simp [ε, hi]
  set z' : Fin d → ℝ := fun i ↦ ε i * z i
  have hz' : N (diagR z') = N (diagR z) := hN.diagonal_mul_sign z ε hε
  set t : ℝ := (1 + a / z j) / 2
  have habs : |a / z j| ≤ 1 := by
    rw [abs_div, div_le_one (abs_pos.mpr hz)]; exact ha
  have ht0 : 0 ≤ t := by
    have := neg_abs_le (a / z j); simp only [t]; linarith
  have ht1 : 0 ≤ 1 - t := by
    have := le_abs_self (a / z j); simp only [t]; linarith
  have hcomb : Function.update z j a = t • z + (1 - t) • z' := by
    ext i
    by_cases hi : i = j
    · subst hi
      simp only [Function.update_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul, z', ε, t]
      field_simp
      ring
    · simp [hi, z', ε]
      ring
  rw [hcomb]
  refine ((hN.convexOn_diagonal).2 (Set.mem_univ _) (Set.mem_univ _) ht0 ht1 (by ring)).trans ?_
  dsimp only
  rw [hz', smul_eq_mul, smul_eq_mul, ← add_mul]
  simp

/-- **Monotonicity on diagonal matrices.** If `|xᵢ| ≤ |zᵢ|` for all `i`, then
`N (diag x) ≤ N (diag z)`. -/
theorem diagonal_le_of_abs_le {x z : Fin d → ℝ} (h : ∀ i, |x i| ≤ |z i|) :
    N (diagR x) ≤ N (diagR z) := by
  classical
  let w : Finset (Fin d) → Fin d → ℝ := fun S i ↦ if i ∈ S then x i else z i
  have key : ∀ S : Finset (Fin d), N (diagR (w S)) ≤ N (diagR z) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [w]
    | insert j S hj ih =>
      have hupd : w (insert j S) = Function.update (w S) j (x j) := by
        ext i
        by_cases hi : i = j
        · subst hi; simp [w]
        · simp [w, hi]
      rw [hupd]
      refine (hN.diagonal_update_le (w S) j ?_).trans ih
      simpa [w, hj] using h j
  have hx : w Finset.univ = x := by ext i; simp [w]
  simpa [hx] using key Finset.univ

/-- **Ky Fan dominance for vectors.** If `x ≥ 0` is weakly submajorized by `y`, then
`N (diag x) ≤ N (diag y)`. -/
theorem diagonal_le_of_vectorSubmajorized {x y : Fin d → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hxy : TNLean.VectorSubmajorized x y) : N (diagR x) ≤ N (diagR y) := by
  obtain ⟨z, hz, hle⟩ := hxy.exists_majorized_ge
  obtain ⟨_, ⟨σ, rfl⟩, hσ⟩ := (hN.convexOn_diagonal).exists_ge_of_mem_convexHull
    (Set.subset_univ _) hz.mem_convexHull_permutations
  refine (hN.diagonal_le_of_abs_le fun i ↦ ?_).trans (hσ.trans (hN.diagonal_comp_perm y σ).le)
  rw [abs_of_nonneg (hx i), abs_of_nonneg ((hx i).trans (hle i))]
  exact hle i

/-- **Ky Fan dominance**, Wolf Theorem 8.2(5): if `‖A‖_(k) ≥ ‖B‖_(k)` for all Ky Fan norms,
`k = 1, …, d`, then `‖A‖ ≥ ‖B‖` for every unitarily invariant norm.
Wolf, `ch08_distance_measures.tex` lines 135--136. -/
theorem le_of_kyFanNorm_le {A B : Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ k, 1 ≤ k → k ≤ d → kyFanNorm B k ≤ kyFanNorm A k) : N B ≤ N A := by
  rw [hN.apply_eq_diagonal_singularValues A, hN.apply_eq_diagonal_singularValues B]
  refine hN.diagonal_le_of_vectorSubmajorized (singularValues_nonneg B) fun k hk ↦ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exact h k hk0 hk

end IsUnitarilyInvariantNorm

end Matrix
