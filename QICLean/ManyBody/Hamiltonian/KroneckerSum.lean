/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Eigenvalue.HermitianExtremalEigenvalues
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity
import QICLean.ManyBody.Hamiltonian.GroundSpace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.ManyBody.Sites.Placement.Basic

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
at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`, and stated over any commutative semiring.

## Main results

* `ManyBody.isGapped_diagonal_iff`, `ManyBody.mem_groundSpace_diagonal_iff` — the gap and the
  ground space of a diagonal matrix.
* `Matrix.IsHermitian.kronecker_add_eq_conj` — the diagonalization of a Kronecker sum.
* `ManyBody.IsGapped.kronecker_add` — the gap of a Kronecker sum.
* `ManyBody.groundSpace_kronecker_add_eq_span` — its ground space is the line through `u ⊗ v`.
* `ManyBody.exists_isGapped_factors_of_kronecker_sum` — conversely, a gapped unique ground
  vector of a Kronecker sum is a product of gapped unique ground vectors of the factors, with
  the same gap.

The converse is variational. With `a`, `b` the minimum eigenvalues of `A`, `B` and `u`, `v`
unit eigenvectors, `A ⊗ 1 + 1 ⊗ B ≥ a + b` and `u ⊗ v` has energy `a + b`; the gap inequality
evaluated on `u ⊗ v` forces `|⟨Ω, u ⊗ v⟩| = 1`, so `Ω` is `u ⊗ v` up to a phase, which is
absorbed into `u`. Compressing the gap inequality along `ξ ↦ ξ ⊗ v` and `η ↦ u ⊗ η` gives the
gaps of the factors. The converse is moved from TNLean,
`TNLean/Lattice/ProductGroundState.lean` at commit `e41c3b63`.
* `ManyBody.exists_isGapped_factors_of_sum_place`: gapped ground vectors of a sum of single-site
  Hamiltonians.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, Lemma reductions, `part1_arealaw.tex`, lines 64–89.

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 2.2 (`lem:zero-boundary`), `01-preliminaries.tex`, lines 123–134.
-/

open Matrix
open scoped Kronecker ComplexOrder

section KroneckerSum

/-- A Kronecker product acts factorwise on a product vector. -/
theorem Matrix.kronecker_mulVec_mul {R α β : Type*} [NonUnitalCommSemiring R] [Fintype α]
    [Fintype β] (M : Matrix α α R) (N : Matrix β β R) (u : α → R) (v : β → R) :
    (M ⊗ₖ N) *ᵥ (fun p ↦ u p.1 * v p.2) = fun p ↦ (M *ᵥ u) p.1 * (N *ᵥ v) p.2 := by
  funext p
  change (∑ t : α × β, M p.1 t.1 * N p.2 t.2 * (u t.1 * v t.2)) =
    (∑ a : α, M p.1 a * u a) * (∑ b : β, N p.2 b * v b)
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ mul_mul_mul_comm _ _ _ _

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

section Converse

open scoped MatrixOrder Matrix.Norms.L2Operator

private theorem norm_toLp_eq_one_of_star_dotProduct {γ : Type*} [Fintype γ]
    (w : γ → ℂ) (hw : star w ⬝ᵥ w = 1) : ‖WithLp.toLp 2 w‖ = 1 := by
  have hinner : inner ℂ (WithLp.toLp 2 w) (WithLp.toLp 2 w) = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hw
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsq : ‖WithLp.toLp 2 w‖ ^ 2 = (1 : ℝ) := by
    simpa only [RCLike.re_ofReal_pow, RCLike.one_re] using
      congrArg (RCLike.re : ℂ → ℝ) hinner
  nlinarith [norm_nonneg (WithLp.toLp 2 w)]



omit [Fintype α] in
variable [Finite α] in
/-- Restrict the tensor-sum projector gap along the unit vector in the second factor.
TNLean one-dimensional note, Lemma reductions, part1_arealaw.tex:71–80. -/
private theorem gap_left_of_kronecker_sum
    (HA : Matrix α α ℂ) (HB : Matrix β β ℂ) (u : α → ℂ) (v : β → ℂ)
    (E b Δ : ℝ) (hv : star v ⬝ᵥ v = 1)
    (hb : star v ⬝ᵥ (HB *ᵥ v) = (b : ℂ))
    (hgap : (HA ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ HB -
      (E : ℂ) • 1 - (Δ : ℂ) •
        (1 - vecMulVec (fun p : α × β ↦ u p.1 * v p.2)
          (star fun p : α × β ↦ u p.1 * v p.2))).PosSemidef) :
    (HA - ((E - b : ℝ) : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec u (star u))).PosSemidef := by
  let _ := Fintype.ofFinite α
  let V : Matrix (α × β) α ℂ := fun p i ↦ if p.1 = i then v p.2 else 0
  have hV : Vᴴ * V = 1 := by
    have hv' : ∑ j, star (v j) * v j = 1 := hv
    ext i j
    change (∑ p : α × β, star (V p i) * V p j) = if i = j then 1 else 0
    by_cases hij : i = j
    · subst j
      simpa [V, Fintype.sum_prod_type] using hv'
    · simp [V, Fintype.sum_prod_type, hij, Ne.symm hij]
  have hAV : (HA ⊗ₖ (1 : Matrix β β ℂ)) * V = V * HA := by
    ext ⟨i, j⟩ k
    change (∑ p : α × β, HA i p.1 * (1 : Matrix β β ℂ) j p.2 * V p k) =
      ∑ a : α, V (i, j) a * HA a k
    simp [V, Fintype.sum_prod_type, Matrix.one_apply, mul_comm]
  have hBV : Vᴴ * (((1 : Matrix α α ℂ) ⊗ₖ HB) * V) = (b : ℂ) • 1 := by
    have hb' : ∑ j, star (v j) * (∑ k, HB j k * v k) = (b : ℂ) := hb
    ext i j
    change (∑ p : α × β, star (V p i) *
      (∑ s : α × β, (1 : Matrix α α ℂ) p.1 s.1 * HB p.2 s.2 * V s j)) =
        (b : ℂ) * if i = j then 1 else 0
    by_cases hij : i = j
    · subst j
      simpa [V, Fintype.sum_prod_type, Matrix.one_apply] using hb'
    · simp [V, Fintype.sum_prod_type, Matrix.one_apply, hij, Ne.symm hij]
  have hVu : Vᴴ *ᵥ (fun p : α × β ↦ u p.1 * v p.2) = u := by
    have hv' : ∑ j, star (v j) * v j = 1 := hv
    funext i
    change (∑ p : α × β, star (V p i) * (u p.1 * v p.2)) = u i
    simpa [V, apply_ite, Fintype.sum_prod_type, mul_left_comm, ← Finset.mul_sum] using
      congrArg (u i * ·) hv'
  have hPV : Vᴴ * vecMulVec (fun p : α × β ↦ u p.1 * v p.2)
      (star fun p : α × β ↦ u p.1 * v p.2) * V = vecMulVec u (star u) := by
    have hrow : (star fun p : α × β ↦ u p.1 * v p.2) ᵥ* V = star u := by
      simpa only [star_mulVec, conjTranspose_conjTranspose] using congrArg star hVu
    rw [mul_vecMulVec, vecMulVec_mul, hVu, hrow]
  have hAV' : Vᴴ * (HA ⊗ₖ (1 : Matrix β β ℂ)) * V = HA := by
    rw [Matrix.mul_assoc, hAV, ← Matrix.mul_assoc, hV, Matrix.one_mul]
  have hBV' : Vᴴ * ((1 : Matrix α α ℂ) ⊗ₖ HB) * V = (b : ℂ) • 1 := by
    rw [Matrix.mul_assoc, hBV]
  have hcompress : Vᴴ * (HA ⊗ₖ (1 : Matrix β β ℂ) +
      (1 : Matrix α α ℂ) ⊗ₖ HB - (E : ℂ) • 1 - (Δ : ℂ) •
        (1 - vecMulVec (fun p : α × β ↦ u p.1 * v p.2)
          (star fun p : α × β ↦ u p.1 * v p.2))) * V =
        HA - ((E - b : ℝ) : ℂ) • 1 -
          (Δ : ℂ) • (1 - vecMulVec u (star u)) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hAV', hBV', hPV, hV]
    push_cast
    rw [sub_smul]
    abel
  rw [← hcompress]
  exact hgap.conjTranspose_mul_mul_same V

/-- The eigen-equation of a coordinate vector in the operator form of the gapped ground-state
iff. -/
private theorem toEuclideanCLM_toLp_eq_smul {γ : Type*} [Fintype γ] [DecidableEq γ]
    {K : Matrix γ γ ℂ} {E : ℝ} {w : γ → ℂ} (h : K *ᵥ w = (E : ℂ) • w) :
    toEuclideanCLM (n := γ) (𝕜 := ℂ) K (WithLp.toLp 2 w) = (E : ℂ) • WithLp.toLp 2 w := by
  rw [← (WithLp.ofLp_injective 2).eq_iff, ofLp_toEuclideanCLM, WithLp.ofLp_smul]
  exact h

omit [Fintype α] [Fintype β] in
/-- A tensor sum `H_A ⊗ 1 + 1 ⊗ H_B` of Hermitian matrices is Hermitian. -/
private theorem isHermitian_kronecker_sum {HA : Matrix α α ℂ} {HB : Matrix β β ℂ}
    (hA : HA.IsHermitian) (hB : HB.IsHermitian) :
    (HA ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ HB).IsHermitian := by
  simp only [IsHermitian, conjTranspose_add, conjTranspose_kronecker, conjTranspose_one, hA.eq,
    hB.eq]

/-- A gapped ground vector `ω` of `H_A ⊗ 1 + 1 ⊗ H_B` is `u ⊗ v` with `E₀ = a + b`, where `u` and
`v` are unit vectors spanning the ground spaces of `H_A` at `a` and `H_B` at `b`, both gapped
with the same gap `Δ`. -/
private theorem exists_gapped_factors_of_gap {HA : Matrix α α ℂ} {HB : Matrix β β ℂ}
    (hA : HA.IsHermitian)
    (hB : HB.IsHermitian) {ω : α × β → ℂ} (hω : star ω ⬝ᵥ ω = 1) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (hev : (HA ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ HB) *ᵥ ω = (E₀ : ℂ) • ω)
    (hgap : (HA ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ HB - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec ω (star ω))).PosSemidef) :
    ∃ (a b : ℝ) (u : α → ℂ) (v : β → ℂ), E₀ = a + b ∧
      (ω = fun p ↦ u p.1 * v p.2) ∧
        (‖WithLp.toLp 2 u‖ = 1 ∧ IsGapped HA a Δ ∧
          groundSpace HA a = Submodule.span ℂ {WithLp.toLp 2 u}) ∧
        (‖WithLp.toLp 2 v‖ = 1 ∧ IsGapped HB b Δ ∧
          groundSpace HB b = Submodule.span ℂ {WithLp.toLp 2 v}) := by
  have hne : Nonempty (α × β) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [dotProduct] at hω
  have : Nonempty α := ⟨(Classical.arbitrary (α × β)).1⟩
  have : Nonempty β := ⟨(Classical.arbitrary (α × β)).2⟩
  obtain ⟨a, u, hu, hu1, hua⟩ := exists_unit_eigenvector_minEigenvalue hA
  obtain ⟨b, v, hv, hv1, hvb⟩ := exists_unit_eigenvector_minEigenvalue hB
  set H := HA ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ HB with hH
  set ψ : α × β → ℂ := fun p ↦ u p.1 * v p.2 with hψ
  -- `H - (a + b)` is positive semidefinite.
  have hsplit : H - ((a + b : ℝ) : ℂ) • 1 =
      (HA - (a : ℂ) • 1) ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ (HB - (b : ℂ) • 1) := by
    have e1 : (HA - (a : ℂ) • 1) ⊗ₖ (1 : Matrix β β ℂ) =
        HA ⊗ₖ (1 : Matrix β β ℂ) - (a : ℂ) • 1 := by
      ext ⟨i, j⟩ ⟨k, l⟩
      by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [one_apply, hik, hjl]
    have e2 : (1 : Matrix α α ℂ) ⊗ₖ (HB - (b : ℂ) • 1) =
        (1 : Matrix α α ℂ) ⊗ₖ HB - (b : ℂ) • 1 := by
      ext ⟨i, j⟩ ⟨k, l⟩
      by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [one_apply, hik, hjl]
    rw [e1, e2, hH]
    push_cast
    rw [add_smul]
    abel
  have hlow : (H - ((a + b : ℝ) : ℂ) • 1).PosSemidef := by
    rw [hsplit]
    exact (hua.kronecker PosSemidef.one).add (PosSemidef.one.kronecker hvb)
  -- `E₀ ≥ a + b`.
  have hE : a + b ≤ E₀ := by
    have h := (RCLike.nonneg_iff.mp (hlow.dotProduct_mulVec_nonneg ω)).1
    rw [sub_mulVec, hev, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
      dotProduct_smul, hω] at h
    simpa using h
  -- `ψ` has energy `a + b`.
  have hψH : H *ᵥ ψ = ((a + b : ℝ) : ℂ) • ψ := by
    rw [hH, add_mulVec, kronecker_mulVec_mul, kronecker_mulVec_mul, one_mulVec, one_mulVec,
      hu, hv]
    funext p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hψ]
    push_cast
    ring
  have hψ1 : star ψ ⬝ᵥ ψ = 1 := by rw [hψ, star_mul_dotProduct_mul, hu1, hv1, one_mul]
  -- The gap inequality evaluated on `ψ`.
  set z := star ω ⬝ᵥ ψ with hz
  have hgψ := (RCLike.nonneg_iff.mp (hgap.dotProduct_mulVec_nonneg ψ)).1
  have hstar : star ψ ⬝ᵥ ω = star z := by rw [hz, star_dotProduct]
  rw [sub_mulVec, sub_mulVec, hψH, smul_mulVec, one_mulVec, smul_mulVec, sub_mulVec,
    one_mulVec, vecMulVec_mulVec, dotProduct_sub, dotProduct_sub, dotProduct_smul,
    dotProduct_smul, dotProduct_smul, dotProduct_sub, dotProduct_smul, hψ1, hstar] at hgψ
  have hw : star z * (star ω ⬝ᵥ ψ) = (Complex.normSq z : ℂ) := by
    rw [← hz, Complex.normSq_eq_conj_mul_self, RCLike.star_def]
  rw [op_smul_eq_mul, hw] at hgψ
  have hreal : (0 : ℝ) ≤ (a + b) - E₀ - Δ * (1 - Complex.normSq z) := by
    have h := hgψ
    simp only [smul_eq_mul, mul_one] at h
    norm_cast at h
  have hz1 : 1 ≤ Complex.normSq z := by nlinarith
  -- `ω` is the multiple `conj z • ψ` of the product vector.
  have hdiff : star (ω - star z • ψ) ⬝ᵥ (ω - star z • ψ) = 1 - (Complex.normSq z : ℂ) := by
    rw [star_sub, star_smul, star_star, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, hω, hψ1, hstar, ← hz]
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [smul_eq_mul, RCLike.star_def]
    ring
  have hnn := (dotProduct_star_self_nonneg (ω - star z • ψ))
  rw [hdiff] at hnn
  have hz0 : Complex.normSq z = 1 := by
    have hle : Complex.normSq z ≤ 1 := by
      have := (Complex.nonneg_iff.mp hnn).1
      simpa using this
    exact le_antisymm hle hz1
  have hEeq : E₀ = a + b := by
    rw [hz0] at hreal
    linarith
  have h0 : star (ω - star z • ψ) ⬝ᵥ (ω - star z • ψ) = 0 := by
    rw [hdiff, hz0]
    simp
  have heq := dotProduct_star_self_eq_zero.mp h0
  have hprod : ω = fun p ↦ (star z * u p.1) * v p.2 := by
    funext p
    have hp := congrFun heq p
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at hp
    rw [hp, hψ]
    ring
  let u' : α → ℂ := star z • u
  have hzunit : z * star z = 1 := by
    simpa only [RCLike.star_def, hz0, Complex.ofReal_one] using Complex.mul_conj z
  have hu'1 : star u' ⬝ᵥ u' = 1 := by
    change star (star z • u) ⬝ᵥ (star z • u) = 1
    rw [star_smul, star_star, smul_dotProduct, dotProduct_smul, hu1]
    simpa only [smul_eq_mul, mul_one] using hzunit
  have hu' : HA *ᵥ u' = (a : ℂ) • u' := by
    dsimp only [u']
    rw [mulVec_smul, hu, smul_comm]
  have hgap' : (HA ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ HB -
      (E₀ : ℂ) • 1 - (Δ : ℂ) •
        (1 - vecMulVec (fun p : α × β ↦ u' p.1 * v p.2)
          (star fun p : α × β ↦ u' p.1 * v p.2))).PosSemidef := by
    simpa only [u', Pi.smul_apply, smul_eq_mul, ← hprod] using hgap
  have hga : (HA - (a : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec u' (star u'))).PosSemidef := by
    have hb : star v ⬝ᵥ (HB *ᵥ v) = (b : ℂ) := by
      rw [hv, dotProduct_smul, hv1, smul_eq_mul, mul_one]
    simpa only [hEeq, add_sub_cancel_right] using
      gap_left_of_kronecker_sum HA HB u' v E₀ b Δ hv1 hb hgap'
  have hswap : (HB ⊗ₖ (1 : Matrix α α ℂ) + (1 : Matrix β β ℂ) ⊗ₖ HA -
      (E₀ : ℂ) • 1 - (Δ : ℂ) •
        (1 - vecMulVec (fun p : β × α ↦ v p.1 * u' p.2)
          (star fun p : β × α ↦ v p.1 * u' p.2))).PosSemidef := by
    convert hgap'.submatrix (Equiv.prodComm β α) using 1
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [Matrix.submatrix_apply, Matrix.one_apply, vecMulVec_apply, Pi.star_apply,
      Prod.mk.injEq, and_comm, mul_comm, add_comm]
  have hgb : (HB - (b : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec v (star v))).PosSemidef := by
    have ha : star u' ⬝ᵥ (HA *ᵥ u') = (a : ℂ) := by
      rw [hu', dotProduct_smul, hu'1, smul_eq_mul, mul_one]
    simpa only [hEeq, add_sub_cancel_left] using
      gap_left_of_kronecker_sum HB HA v u' E₀ a Δ hu'1 ha hswap
  refine ⟨a, b, u', v, hEeq, hprod, ?_, ?_⟩
  · exact ((isGapped_and_groundSpace_eq_span_iff hΔ _).mp
      ⟨norm_toLp_eq_one_of_star_dotProduct u' hu'1, toEuclideanCLM_toLp_eq_smul hu', hga⟩).2
  · exact ((isGapped_and_groundSpace_eq_span_iff hΔ _).mp
      ⟨norm_toLp_eq_one_of_star_dotProduct v hv1, toEuclideanCLM_toLp_eq_smul hv, hgb⟩).2

/-- **A gapped unique ground vector of a Kronecker sum is a product.** If `A` and `B` are
Hermitian and `A ⊗ 1 + 1 ⊗ B` is gapped at `E₀` with gap `Δ > 0` and ground space the line
through the unit vector `Ω`, then `Ω = u ⊗ v` for unit vectors `u`, `v`, `E₀ = a + b`, and `A`
and `B` are gapped at `a` and `b` with the same gap `Δ` and ground spaces the lines through `u`
and `v`. This is the converse of `IsGapped.kronecker_add` and
`groundSpace_kronecker_add_eq_span`.
TNLean one-dimensional note, Lemma reductions, `part1_arealaw.tex`, lines 71–80; OpenAI,
*A two-dimensional area law from a global spectral gap*, Lemma 2.2 (`lem:zero-boundary`),
`01-preliminaries.tex`, lines 123–134. -/
theorem exists_isGapped_factors_of_kronecker_sum
    {HA : Matrix α α ℂ} {HB : Matrix β β ℂ} (hA : HA.IsHermitian) (hB : HB.IsHermitian)
    {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (α × β)} (hΔ : 0 < Δ) (hunit : ‖Ω‖ = 1)
    (hgs : IsGapped (HA ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ HB) E₀ Δ)
    (hspan : groundSpace (HA ⊗ₖ (1 : Matrix β β ℂ) + (1 : Matrix α α ℂ) ⊗ₖ HB) E₀ =
      Submodule.span ℂ {Ω}) :
    ∃ (a b : ℝ) (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β), E₀ = a + b ∧
      (∀ p : α × β, Ω p = u p.1 * v p.2) ∧
        (‖u‖ = 1 ∧ IsGapped HA a Δ ∧ groundSpace HA a = Submodule.span ℂ {u}) ∧
        (‖v‖ = 1 ∧ IsGapped HB b Δ ∧ groundSpace HB b = Submodule.span ℂ {v}) := by
  have hev := mulVec_eq_of_groundSpace_eq_span hspan
  have hgap := hgs.posSemidef_sub_smul_one (isHermitian_kronecker_sum hA hB) hunit hspan
  have hω : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      inner_self_eq_one_of_norm_eq_one (𝕜 := ℂ) hunit
  obtain ⟨a, b, u, v, hE, hprod, hu, hv⟩ :=
    exists_gapped_factors_of_gap hA hB hω hΔ hev hgap
  exact ⟨a, b, WithLp.toLp 2 u, WithLp.toLp 2 v, hE, fun p ↦ congrFun hprod p, hu, hv⟩

end Converse

end ManyBody

end KroneckerSum

section ProductGround

/-!
## Gapped ground vectors of a sum of single-site Hamiltonians

Let `H = ∑ᵥ Hᵥ ⊗ 1`, where each Hermitian `Hᵥ` acts on the single site `v` of a nonempty finite
set of sites. If `H` is gapped at `E₀` with gap `Δ > 0` and its ground space is the line through
a unit vector `Ω`, then `Ω = ⨂ᵥ ωᵥ` for unit vectors `ωᵥ`, `E₀ = ∑ᵥ aᵥ`, and each `Hᵥ` is
gapped at `aᵥ` with the same gap `Δ` and ground space the line through `ωᵥ`.

At each site `v`, the cut of the system into `v` and the other sites writes `H` as the Kronecker
sum `Hᵥ ⊗ 1 + 1 ⊗ H'`, and `ManyBody.exists_isGapped_factors_of_kronecker_sum` gives the gap of
`Hᵥ`, a unit vector `uᵥ` spanning its ground space at `aᵥ`, and `(Hᵥ ⊗ 1) Ω = aᵥ Ω`. Summing over
`v` gives `E₀ = ∑ᵥ aᵥ`. The unit product `⨂ᵥ uᵥ` has energy `∑ᵥ aᵥ`, so it lies on the line
through `Ω`; the phase between them is absorbed into one factor.

Moved from TNLean, `TNLean/Lattice/ProductGroundState.lean` at commit `e41c3b63`, where the
factors were indexed by `Fin (n + 1)` and the summands were written with a separate definition
`factorOperator`; here they are the placements `place {v} Hᵥ` on a system of sites.

### Main results

* `ManyBody.exists_isGapped_factors_of_sum_place` — the factorization of the ground vector.

### References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, Lemma reductions (`lem:reductions`), `part1_arealaw.tex`, lines 64–89.
-/

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]

/-- Configurations of the system are families of configurations of the single sites. -/
private def siteConfigEquiv : Config X ≃ ∀ v, RegionConfig X {v} :=
  Equiv.piCongrRight fun v ↦ (Equiv.piUnique fun w : ({v} : Finset V) ↦ X w.1).symm

omit [Fintype V] [DecidableEq V] [∀ v, Fintype (X v)] in
private theorem siteConfigEquiv_apply (x : Config X) (v : V) :
    siteConfigEquiv x v = fun w : ({v} : Finset V) ↦ x w := by
  funext w
  obtain ⟨w, hw⟩ := w
  obtain rfl := Finset.mem_singleton.mp hw
  rfl

/-- The product vector `x ↦ ∏ᵥ uᵥ(x_v)`. -/
private noncomputable def siteProduct (u : ∀ v, EuclideanSpace ℂ (RegionConfig X {v})) :
    Config X → ℂ :=
  fun x ↦ ∏ v, u v (fun w : ({v} : Finset V) ↦ x w)

private theorem star_siteProduct_dotProduct (u : ∀ v, EuclideanSpace ℂ (RegionConfig X {v})) :
    star (siteProduct u) ⬝ᵥ siteProduct u = ∏ v, star (WithLp.ofLp (u v)) ⬝ᵥ WithLp.ofLp (u v) := by
  simp only [dotProduct, Fintype.prod_sum]
  rw [← siteConfigEquiv.sum_comp]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [siteProduct, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib,
    siteConfigEquiv_apply]

variable [∀ v, DecidableEq (X v)]

/-- A single-site Hamiltonian acts on a product vector through its own factor. -/
private theorem place_mulVec_siteProduct (u : ∀ v, EuclideanSpace ℂ (RegionConfig X {v})) (v : V)
    (K : Matrix (RegionConfig X {v}) (RegionConfig X {v}) ℂ) {a : ℝ}
    (hK : K *ᵥ WithLp.ofLp (u v) = (a : ℂ) • WithLp.ofLp (u v)) :
    place {v} K *ᵥ siteProduct u = (a : ℂ) • siteProduct u := by
  funext σ
  rw [place_mulVec_apply]
  have hglue (r : RegionConfig X {v}) :
      siteProduct u ((cutEquiv X {v}).symm (r, (cutEquiv X {v} σ).2)) =
        u v r * ∏ w ∈ Finset.univ.erase v, u w (fun z : ({w} : Finset V) ↦ σ z) := by
    rw [siteProduct, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
    congr 1
    · refine congrArg (WithLp.ofLp (u v)) (funext fun z ↦ ?_)
      obtain ⟨z, hz⟩ := z
      exact cutEquiv_symm_apply_mem _ _ hz
    · refine Finset.prod_congr rfl fun w hw ↦ congrArg (WithLp.ofLp (u w)) (funext fun z ↦ ?_)
      obtain ⟨z, hz⟩ := z
      obtain rfl := Finset.mem_singleton.mp hz
      exact cutEquiv_symm_apply_not_mem _ _
        (by simpa using (Finset.ne_of_mem_erase hw))
  simp only [hglue, ← mul_assoc, ← Finset.sum_mul]
  have hv := congrFun hK (fun w : ({v} : Finset V) ↦ σ w)
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hv
  rw [hv, Pi.smul_apply, smul_eq_mul, siteProduct, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
    mul_assoc]

/-- At one site, the Kronecker-sum factorization gives the gap and the ground line of the
single-site Hamiltonian, and its eigenvalue on the ground vector. -/
private theorem exists_site_factor {H : ∀ v, Matrix (RegionConfig X {v}) (RegionConfig X {v}) ℂ}
    (hH : ∀ v, (H v).IsHermitian) {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Config X)} (hΔ : 0 < Δ)
    (hΩ : ‖Ω‖ = 1) (hgs : IsGapped (∑ v, place {v} (H v)) E₀ Δ)
    (hspan : groundSpace (∑ v, place {v} (H v)) E₀ = Submodule.span ℂ {Ω}) (v : V) :
    ∃ (a : ℝ) (u : EuclideanSpace ℂ (RegionConfig X {v})), ‖u‖ = 1 ∧ IsGapped (H v) a Δ ∧
      groundSpace (H v) a = Submodule.span ℂ {u} ∧
      place {v} (H v) *ᵥ WithLp.ofLp Ω = (a : ℂ) • WithLp.ofLp Ω := by
  classical
  set c := cutEquiv X {v}
  have hne : Nonempty (Config X) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Ω = 0 := by
      apply WithLp.ofLp_injective 2
      funext x
      exact isEmptyElim x
    simp [this] at hΩ
  obtain ⟨x₀⟩ := hne
  let r₀ : RegionConfig X {v} := (c x₀).1
  let B := ∑ w ∈ Finset.univ.erase v, place {w} (H w)
  have hsplit : ∑ w, place {w} (H w) = place {v} (H v) + B :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
  have hB : B ∈ supportedOperators X ({v}ᶜ) := by
    refine sum_mem fun w hw ↦ supportedOperators_mono ?_ (place_mem_supportedOperators _)
    simpa [eq_comm] using Finset.ne_of_mem_erase hw
  obtain ⟨B₂, hB₂⟩ := exists_eq_one_kronecker_of_mem_supportedOperators
    (D := {v}) disjoint_compl_left hB
  have hBherm : B.IsHermitian :=
    (isSelfAdjoint_sum _ fun w _ ↦ (isHermitian_place (hH w)).isSelfAdjoint).isHermitian
  have hA : place {v} (H v) =
      ((H v) ⊗ₖ (1 : Matrix (ComplConfig X {v}) (ComplConfig X {v}) ℂ)).submatrix c c := by
    simp [place, reindex_apply, c]
  have hcut : (∑ w, place {w} (H w)).submatrix c.symm c.symm =
      H v ⊗ₖ (1 : Matrix (ComplConfig X {v}) (ComplConfig X {v}) ℂ) +
        (1 : Matrix (RegionConfig X {v}) (RegionConfig X {v}) ℂ) ⊗ₖ B₂ := by
    rw [hsplit, hA, hB₂]
    ext i j
    simp [c]
  have hB₂herm : B₂.IsHermitian := by
    have hK : ((1 : Matrix (RegionConfig X {v}) (RegionConfig X {v}) ℂ) ⊗ₖ B₂).IsHermitian := by
      have := hBherm.submatrix c.symm
      rwa [hB₂, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at this
    refine IsHermitian.ext fun i j ↦ ?_
    simpa only [kroneckerMap_apply, one_apply_eq, one_mul] using hK.apply (r₀, i) (r₀, j)
  have hgs' := (isGapped_submatrix_iff c.symm).mpr hgs
  have hspan' := groundSpace_submatrix_eq_span c.symm hspan
  rw [hcut] at hgs' hspan'
  have hn' : ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ c.symm.symm Ω‖ = 1 :=
    (LinearIsometryEquiv.norm_map _ _).trans hΩ
  obtain ⟨a, b, u, w, -, hprod, hu, -⟩ :=
    exists_isGapped_factors_of_kronecker_sum (hH v) hB₂herm hΔ hn' hgs' hspan'
  refine ⟨a, u, hu.1, hu.2.1, hu.2.2, ?_⟩
  have hΩc : WithLp.ofLp Ω ∘ c.symm = fun p ↦ u p.1 * w p.2 := by
    funext p
    simpa [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using hprod p
  have hu' := mulVec_eq_of_groundSpace_eq_span hu.2.2
  rw [hA, submatrix_mulVec_equiv, hΩc, kronecker_mulVec_mul, one_mulVec, hu']
  funext σ
  have hσ := congrFun hΩc (c σ)
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at hσ
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, hσ, mul_assoc]

/-- **A gapped unique ground vector of a sum of single-site Hamiltonians is a product.** Let
`Hᵥ` be Hermitian on the site `v` of a nonempty finite set of sites, and let
`H = ∑ᵥ place {v} Hᵥ` be gapped at `E₀` with gap `Δ > 0` and ground space the line through the
unit vector `Ω`. Then `Ω(x) = ∏ᵥ ωᵥ(x_v)` for unit vectors `ωᵥ`, `E₀ = ∑ᵥ aᵥ`, and each `Hᵥ`
is gapped at `aᵥ` with the same gap `Δ` and ground space the line through `ωᵥ`. The set of
sites is nonempty because the empty product is `1`, while for no sites `Ω` can be any unit scalar.
TNLean one-dimensional note, Lemma reductions (`lem:reductions`), `part1_arealaw.tex`,
lines 64–89: each component Hamiltonian inherits the gap inequality with the same gap. -/
theorem exists_isGapped_factors_of_sum_place [Nonempty V]
    {H : ∀ v, Matrix (RegionConfig X {v}) (RegionConfig X {v}) ℂ} (hH : ∀ v, (H v).IsHermitian)
    {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Config X)} (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1)
    (hgs : IsGapped (∑ v, place {v} (H v)) E₀ Δ)
    (hspan : groundSpace (∑ v, place {v} (H v)) E₀ = Submodule.span ℂ {Ω}) :
    ∃ (a : V → ℝ) (ω : ∀ v, EuclideanSpace ℂ (RegionConfig X {v})), E₀ = ∑ v, a v ∧
      (∀ x, Ω x = ∏ v, ω v (fun w : ({v} : Finset V) ↦ x w)) ∧
      ∀ v, ‖ω v‖ = 1 ∧ IsGapped (H v) (a v) Δ ∧
        groundSpace (H v) (a v) = Submodule.span ℂ {ω v} := by
  classical
  choose a u hu1 hgap hsp hev using exists_site_factor hH hΔ hΩ hgs hspan
  have hΩne : WithLp.ofLp Ω ≠ 0 := by
    intro h
    have : Ω = 0 := WithLp.ofLp_injective 2 h
    simp [this] at hΩ
  -- The energy is additive.
  have hE : E₀ = ∑ v, a v := by
    have hsum : (∑ v, place {v} (H v)) *ᵥ WithLp.ofLp Ω = ((∑ v, a v : ℝ) : ℂ) • WithLp.ofLp Ω := by
      rw [sum_mulVec]
      simp only [hev, ← Finset.sum_smul, Complex.ofReal_sum]
    rw [mulVec_eq_of_groundSpace_eq_span hspan] at hsum
    exact_mod_cast smul_left_injective ℂ hΩne hsum
  -- The product of the factor ground vectors is a unit ground vector.
  have hu1' (v : V) : star (WithLp.ofLp (u v)) ⬝ᵥ WithLp.ofLp (u v) = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      inner_self_eq_one_of_norm_eq_one (𝕜 := ℂ) (hu1 v)
  have hψ1 : star (siteProduct u) ⬝ᵥ siteProduct u = 1 := by
    rw [star_siteProduct_dotProduct]
    simp [hu1']
  have hψ : WithLp.toLp 2 (siteProduct u) ∈ groundSpace (∑ v, place {v} (H v)) E₀ := by
    rw [mem_groundSpace_iff_mulVec, WithLp.ofLp_toLp, sum_mulVec, hE]
    simp only [fun v ↦ place_mulVec_siteProduct u v (H v)
        (mulVec_eq_of_groundSpace_eq_span (hsp v)),
      ← Finset.sum_smul, Complex.ofReal_sum]
  rw [hspan] at hψ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hψ
  have hc' : siteProduct u = c • WithLp.ofLp Ω := by
    simpa using (congrArg WithLp.ofLp hc).symm
  have hΩ1 : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      inner_self_eq_one_of_norm_eq_one (𝕜 := ℂ) hΩ
  have hcc : star c * c = 1 := by
    rw [hc', star_smul, smul_dotProduct, dotProduct_smul, hΩ1] at hψ1
    simpa [mul_comm] using hψ1
  -- Absorb the phase into one factor.
  obtain ⟨v₀⟩ := ‹Nonempty V›
  let ω : ∀ v, EuclideanSpace ℂ (RegionConfig X {v}) := Function.update u v₀ (star c • u v₀)
  have hω₀ : ω v₀ = star c • u v₀ := Function.update_self _ _ _
  have hω (v : V) (hv : v ≠ v₀) : ω v = u v := Function.update_of_ne hv _ _
  have hcne : star c ≠ 0 := by
    intro h
    simp [h] at hcc
  refine ⟨a, ω, hE, fun x ↦ ?_, fun v ↦ ?_⟩
  · have hx := congrFun hc' x
    rw [Pi.smul_apply, smul_eq_mul] at hx
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v₀), hω₀,
      Finset.prod_congr rfl fun v hv ↦ by rw [hω v (Finset.ne_of_mem_erase hv)]]
    have hprod : siteProduct u x =
        u v₀ (fun w : ({v₀} : Finset V) ↦ x w) *
          ∏ v ∈ Finset.univ.erase v₀, u v (fun w : ({v} : Finset V) ↦ x w) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ v₀)).symm
    rw [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← hprod, hx, ← mul_assoc, hcc, one_mul]
  · by_cases hv : v = v₀
    · subst hv
      rw [hω₀]
      refine ⟨?_, hgap v, ?_⟩
      · rw [norm_smul, hu1, mul_one]
        have h2 : ((Complex.normSq c : ℝ) : ℂ) = 1 := by
          rw [← Complex.mul_conj, mul_comm]
          exact hcc
        have h3 : ‖c‖ ^ 2 = 1 := by
          rw [← Complex.normSq_eq_norm_sq]
          exact_mod_cast h2
        rw [norm_star]
        nlinarith [norm_nonneg c]
      · rw [hsp, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hcne)]
    · rw [hω v hv]
      exact ⟨hu1 v, hgap v, hsp v⟩

end ManyBody

end ProductGround
