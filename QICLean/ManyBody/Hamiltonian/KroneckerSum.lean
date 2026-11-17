/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Hamiltonian.GroundSpace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Gaps of a Kronecker sum

For Hermitian `A` and `B`, the Kronecker sum `A ⊗ 1 + 1 ⊗ B` is the conjugate, by the Kronecker
product of the eigenvector unitaries, of the diagonal matrix with entries `λᵢ + μⱼ`. Unitary
conjugation preserves the ground space and the gap, so both reduce to the diagonal case. If `A`
and `B` are gapped at `a` and `b` with gaps `Δa` and `Δb`, one of them nonnegative, then
`A ⊗ 1 + 1 ⊗ B` is gapped at `a + b` with gap `min Δa Δb`. If both gaps are nonnegative and the
ground spaces are the lines through `u` and `v`, the ground space of the sum is the line through
`u ⊗ v`. A Hamiltonian with no term across a cut is such a sum.

`Matrix.kronecker_mulVec_mul` is moved from TNLean, `TNLean/Algebra/KroneckerLeastEigenvalue.lean`
at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`, with its statement and proof unchanged.

## Main results

* `ManyBody.isGapped_diagonal_iff`, `ManyBody.mem_groundSpace_diagonal_iff` — the gap and the
  ground space of a diagonal matrix.
* `Matrix.IsHermitian.kronecker_add_eq_conj` — the diagonalization of a Kronecker sum.
* `ManyBody.IsGapped.kronecker_add` — the gap of a Kronecker sum.
* `ManyBody.groundSpace_kronecker_add_eq_span` — its ground space is the line through `u ⊗ v`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 2.2 (`lem:zero-boundary`), `01-preliminaries.tex`, lines 123–134.
-/

open Matrix
open scoped Kronecker ComplexOrder

/-- A Kronecker product acts factorwise on a product vector. -/
theorem Matrix.kronecker_mulVec_mul {α β : Type*} [Fintype α] [Fintype β]
    (M : Matrix α α ℂ) (N : Matrix β β ℂ) (u : α → ℂ)
    (v : β → ℂ) :
    (M ⊗ₖ N) *ᵥ (fun p ↦ u p.1 * v p.2) = fun p ↦ (M *ᵥ u) p.1 * (N *ᵥ v) p.2 := by
  funext p
  change (∑ t : α × β, M p.1 t.1 * N p.2 t.2 * (u t.1 * v t.2)) =
    (∑ a : α, M p.1 a * u a) * (∑ b : β, N p.2 b * v b)
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring

/-- The Kronecker sum `A ⊗ 1 + 1 ⊗ B` of two Hermitian matrices is the conjugate, by the
Kronecker product of their eigenvector unitaries, of the diagonal matrix of the sums of their
eigenvalues. -/
theorem Matrix.IsHermitian.kronecker_add_eq_conj {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ B =
      ((hA.eigenvectorUnitary : Matrix α α ℂ) ⊗ₖ (hB.eigenvectorUnitary : Matrix β β ℂ)) *
        diagonal (fun p : α × β ↦ ((hA.eigenvalues p.1 + hB.eigenvalues p.2 : ℝ) : ℂ)) *
        ((hA.eigenvectorUnitary : Matrix α α ℂ) ⊗ₖ (hB.eigenvectorUnitary : Matrix β β ℂ))ᴴ := by
  set U : Matrix α α ℂ := (hA.eigenvectorUnitary : Matrix α α ℂ)
  set V : Matrix β β ℂ := (hB.eigenvectorUnitary : Matrix β β ℂ)
  have hA' : A = U * diagonal (fun i ↦ (hA.eigenvalues i : ℂ)) * Uᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have hB' : B = V * diagonal (fun j ↦ (hB.eigenvalues j : ℂ)) * Vᴴ := by
    conv_lhs => rw [hB.spectral_theorem]
    rfl
  have hU : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hV : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  have hdiag : diagonal (fun p : α × β ↦ ((hA.eigenvalues p.1 + hB.eigenvalues p.2 : ℝ) : ℂ)) =
      diagonal (fun i ↦ (hA.eigenvalues i : ℂ)) ⊗ₖ (1 : Matrix β β ℂ) +
        (1 : Matrix α α ℂ) ⊗ₖ diagonal (fun j ↦ (hB.eigenvalues j : ℂ)) := by
    rw [← (diagonal_one : diagonal (1 : β → ℂ) = 1), ← (diagonal_one : diagonal (1 : α → ℂ) = 1),
      diagonal_kronecker_diagonal, diagonal_kronecker_diagonal, diagonal_add]
    congr 1
    funext p
    push_cast
    ring
  rw [hdiag, conjTranspose_kronecker, mul_add, add_mul, ← mul_kronecker_mul, ← mul_kronecker_mul,
    ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.mul_one, hU, hV,
    ← hA', ← hB']

namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvalues of a diagonal matrix are its diagonal entries. -/
theorem hasEigenvalue_toEuclideanLin_diagonal_iff (d : n → ℂ) (μ : ℂ) :
    Module.End.HasEigenvalue (toEuclideanLin (diagonal d)) μ ↔ ∃ k, d k = μ := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLpLin, spectrum_diagonal]
  rfl

/-- A vector lies in the ground space of a diagonal matrix exactly when it vanishes at the
entries different from the energy. -/
theorem mem_groundSpace_diagonal_iff (d : n → ℂ) (E₀ : ℝ) (ψ : EuclideanSpace ℂ n) :
    ψ ∈ groundSpace (diagonal d) E₀ ↔ ∀ k, d k ≠ E₀ → ψ k = 0 := by
  rw [mem_groundSpace_iff_mulVec, funext_iff]
  refine forall_congr' fun k ↦ ?_
  simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h hk
    exact (mul_eq_mul_right_iff.mp h).resolve_left hk
  · intro h
    by_cases hk : d k = E₀
    · rw [hk]
    · rw [h hk, mul_zero, mul_zero]

/-- A real diagonal matrix is gapped at `E₀` with gap `Δ` exactly when some entry is `E₀` and
every entry is `E₀` or at least `E₀ + Δ`. -/
theorem isGapped_diagonal_iff (d : n → ℝ) {E₀ Δ : ℝ} :
    IsGapped (diagonal fun k ↦ (d k : ℂ)) E₀ Δ ↔
      (∃ k, d k = E₀) ∧ ∀ k, d k = E₀ ∨ E₀ + Δ ≤ d k := by
  unfold IsGapped groundSpace
  rw [← Module.End.hasEigenvalue_iff, hasEigenvalue_toEuclideanLin_diagonal_iff]
  simp only [hasEigenvalue_toEuclideanLin_diagonal_iff, Complex.ofReal_inj, forall_exists_index,
    forall_apply_eq_imp_iff, Complex.real_le_real]

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

private theorem exists_eigenvalue_eq_of_isGapped {A : Matrix α α ℂ} (hA : A.IsHermitian)
    {a Δ : ℝ} (h : IsGapped A a Δ) : ∃ i, hA.eigenvalues i = a := by
  obtain ⟨k, hk⟩ := hA.hasEigenvalue_toEuclideanLin_iff.mp (Module.End.hasEigenvalue_iff.mpr h.1)
  exact ⟨k, (Complex.ofReal_inj.mp hk).symm⟩

private theorem le_eigenvalues_of_isGapped {A : Matrix α α ℂ} (hA : A.IsHermitian)
    {a Δ : ℝ} (h : IsGapped A a Δ) (hΔ : 0 ≤ Δ) (i : α) : a ≤ hA.eigenvalues i := by
  rcases ((isGapped_iff_eigenvalues hA).mp h).2 i with hi | hi
  · exact hi.ge
  · linarith

/-- **The gap of a Kronecker sum.** If `A` and `B` are Hermitian and gapped at `a` and `b`
with gaps `Δa` and `Δb`, one of them nonnegative, then `A ⊗ 1 + 1 ⊗ B` is gapped at `a + b`
with gap `min Δa Δb`. Without the sign condition the statement fails: two negative gaps let
`λ + μ` fall below `a + b + min Δa Δb`. -/
theorem IsGapped.kronecker_add {A : Matrix α α ℂ} {B : Matrix β β ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {a b Δa Δb : ℝ} (hgA : IsGapped A a Δa) (hgB : IsGapped B b Δb)
    (hΔ : 0 ≤ Δa ∨ 0 ≤ Δb) :
    IsGapped (A ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ B) (a + b) (min Δa Δb) := by
  rw [hA.kronecker_add_eq_conj hB,
    isGapped_unitary_conj_iff (kronecker_mem_unitary hA.eigenvectorUnitary.2
      hB.eigenvectorUnitary.2)]
  refine (isGapped_diagonal_iff (fun p : α × β ↦ hA.eigenvalues p.1 + hB.eigenvalues p.2)).mpr
    ⟨?_, fun p ↦ ?_⟩
  · obtain ⟨i, hi⟩ := exists_eigenvalue_eq_of_isGapped hA hgA
    obtain ⟨j, hj⟩ := exists_eigenvalue_eq_of_isGapped hB hgB
    exact ⟨(i, j), by simp only [hi, hj]⟩
  · have hmin := min_le_left Δa Δb
    have hmin' := min_le_right Δa Δb
    rcases ((isGapped_iff_eigenvalues hA).mp hgA).2 p.1 with h1 | h1 <;>
      rcases ((isGapped_iff_eigenvalues hB).mp hgB).2 p.2 with h2 | h2
    · exact Or.inl (by simp only [h1, h2])
    · exact Or.inr (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inr (by rcases hΔ with hΔ | hΔ <;> linarith)

/-- **The ground space of a Kronecker sum.** If `A` and `B` are Hermitian and gapped at `a`
and `b` with nonnegative gaps, and their ground spaces are the lines through `u` and `v`,
then the ground space of `A ⊗ 1 + 1 ⊗ B` at `a + b` is the line through `u ⊗ v`. -/
theorem groundSpace_kronecker_add_eq_span {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {a b Δa Δb : ℝ} (hgA : IsGapped A a Δa)
    (hgB : IsGapped B b Δb) (hΔa : 0 ≤ Δa) (hΔb : 0 ≤ Δb) {u : EuclideanSpace ℂ α}
    {v : EuclideanSpace ℂ β} (hu : groundSpace A a = Submodule.span ℂ {u})
    (hv : groundSpace B b = Submodule.span ℂ {v}) :
    groundSpace (A ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ B) (a + b) =
      Submodule.span ℂ {WithLp.toLp 2 fun p : α × β ↦ u p.1 * v p.2} := by
  set U : Matrix α α ℂ := (hA.eigenvectorUnitary : Matrix α α ℂ)
  set V : Matrix β β ℂ := (hB.eigenvectorUnitary : Matrix β β ℂ)
  have hUu : U ∈ unitaryGroup α ℂ := hA.eigenvectorUnitary.2
  have hVu : V ∈ unitaryGroup β ℂ := hB.eigenvectorUnitary.2
  have hA' : A = U * diagonal (fun i ↦ (hA.eigenvalues i : ℂ)) * Uᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    rfl
  have hB' : B = V * diagonal (fun j ↦ (hB.eigenvalues j : ℂ)) * Vᴴ := by
    conv_lhs => rw [hB.spectral_theorem]
    rfl
  -- The images of the ground basis vectors lie on the given lines.
  have hUe (i : α) (hi : hA.eigenvalues i = a) :
      ∃ c : ℂ, c • u = toEuclideanLin U (EuclideanSpace.single i 1) := by
    have hmem : toEuclideanLin U (EuclideanSpace.single i 1) ∈ groundSpace A a := by
      rw [hA', groundSpace_unitary_conj hUu]
      refine Submodule.mem_map_of_mem ((mem_groundSpace_diagonal_iff _ _ _).mpr fun k hk ↦ ?_)
      have hki : k ≠ i := fun h ↦ hk (by rw [h, hi])
      simp [hki]
    rw [hu] at hmem
    exact Submodule.mem_span_singleton.mp hmem
  have hVe (j : β) (hj : hB.eigenvalues j = b) :
      ∃ c : ℂ, c • v = toEuclideanLin V (EuclideanSpace.single j 1) := by
    have hmem : toEuclideanLin V (EuclideanSpace.single j 1) ∈ groundSpace B b := by
      rw [hB', groundSpace_unitary_conj hVu]
      refine Submodule.mem_map_of_mem ((mem_groundSpace_diagonal_iff _ _ _).mpr fun k hk ↦ ?_)
      have hkj : k ≠ j := fun h ↦ hk (by rw [h, hj])
      simp [hkj]
    rw [hv] at hmem
    exact Submodule.mem_span_singleton.mp hmem
  apply le_antisymm
  · rw [hA.kronecker_add_eq_conj hB, groundSpace_unitary_conj (kronecker_mem_unitary hUu hVu),
      Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap]
    rw [← (EuclideanSpace.basisFun (α × β) ℂ).sum_repr y, map_sum]
    refine Submodule.sum_mem _ fun p _ ↦ ?_
    rw [map_smul]
    by_cases hp : hA.eigenvalues p.1 + hB.eigenvalues p.2 = a + b
    · refine Submodule.smul_mem _ _ ?_
      have h1 := le_eigenvalues_of_isGapped hA hgA hΔa p.1
      have h2 := le_eigenvalues_of_isGapped hB hgB hΔb p.2
      obtain ⟨c, hc⟩ := hUe p.1 (by linarith)
      obtain ⟨d, hd⟩ := hVe p.2 (by linarith)
      have hsingle : (EuclideanSpace.basisFun (α × β) ℂ p : EuclideanSpace ℂ (α × β)) =
          WithLp.toLp 2 fun q : α × β ↦ (EuclideanSpace.single p.1 (1 : ℂ) : α → ℂ) q.1 *
            (EuclideanSpace.single p.2 (1 : ℂ) : β → ℂ) q.2 := by
        apply WithLp.ofLp_injective 2
        funext q
        rw [EuclideanSpace.basisFun_apply]
        by_cases h1 : q.1 = p.1 <;> by_cases h2 : q.2 = p.2 <;>
          simp [PiLp.single_apply, h1, h2, Prod.ext_iff]
      rw [hsingle]
      refine Submodule.mem_span_singleton.mpr ⟨c * d, ?_⟩
      apply WithLp.ofLp_injective 2
      simp only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul, kronecker_mulVec_mul]
      have hc' := congrArg WithLp.ofLp hc
      have hd' := congrArg WithLp.ofLp hd
      simp only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] at hc' hd'
      rw [← hc', ← hd']
      funext q
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · have hy0 : (EuclideanSpace.basisFun (α × β) ℂ).repr y p = 0 := by
        rw [EuclideanSpace.basisFun_repr]
        exact (mem_groundSpace_diagonal_iff _ _ _).mp hy p (by exact_mod_cast hp)
      rw [hy0, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_groundSpace_iff_mulVec]
    have hAu := mulVec_eq_of_groundSpace_eq_span hu
    have hBv := mulVec_eq_of_groundSpace_eq_span hv
    simp only [add_mulVec, kronecker_mulVec_mul, one_mulVec, hAu, hBv]
    funext q
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

end ManyBody
