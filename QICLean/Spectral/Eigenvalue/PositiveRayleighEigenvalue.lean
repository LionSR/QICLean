/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Small positive eigenvalues from a Rayleigh bound

A positive operator `T` on a finite-dimensional complex inner product space, with a vector `v`
orthogonal to its kernel whose Rayleigh quotient `Re ⟨T v, v⟩ / ‖v‖²` is below `ε`, has a
positive eigenvalue below `ε`: expanding `v` in an eigenvector basis of `T`, its coordinates on
the kernel vanish, and if every positive eigenvalue were at least `ε` the energy would be at
least `ε ‖v‖²`. For an arbitrary trial vector the kernel component is subtracted first; this
keeps the energy and removes the squared norm of the projection onto the kernel.

## Main results

* `LinearMap.IsPositive.exists_pos_eigenvalue_lt_of_rayleigh` — a vector orthogonal to the
  kernel with Rayleigh quotient below `ε`.
* `LinearMap.IsPositive.exists_pos_eigenvalue_lt_of_projection_bound` — an arbitrary vector, with
  the squared norm of its kernel projection subtracted.

## References

* arXiv:1210.6613, proof of Theorem `thm:gapless`, lines 1302–1314, the spectral step for the
  uncle Hamiltonians.
-/

open scoped InnerProductSpace

namespace LinearMap.IsPositive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- A positive operator on a finite-dimensional space has a positive eigenvalue below `ε` when
some vector orthogonal to its kernel has Rayleigh quotient below `ε`. arXiv:1210.6613, proof of
`thm:gapless`, lines 1302–1314. -/
theorem exists_pos_eigenvalue_lt_of_rayleigh {T : E →ₗ[ℂ] E} (hT : T.IsPositive) (v : E)
    (hv : v ∈ (LinearMap.ker T)ᗮ) (ε : ℝ) (hRayleigh : (⟪T v, v⟫_ℂ).re < ε * ‖v‖ ^ 2) :
    ∃ μ : ℝ, 0 < μ ∧ μ < ε ∧ Module.End.HasEigenvalue T (μ : ℂ) := by
  classical
  let b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
    hT.isSymmetric.eigenvectorBasis rfl
  let lam : Fin (Module.finrank ℂ E) → ℝ := hT.isSymmetric.eigenvalues rfl
  have hnonneg (i) : 0 ≤ lam i := hT.nonneg_eigenvalues rfl i
  have heig (i) : Module.End.HasEigenvalue T (lam i : ℂ) :=
    hT.isSymmetric.hasEigenvalue_eigenvalues rfl i
  have hcoord_zero (i) (hi : lam i = 0) : b.repr v i = 0 := by
    have hker : b i ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker]
      change T (hT.isSymmetric.eigenvectorBasis rfl i) = 0
      rw [hT.isSymmetric.apply_eigenvectorBasis]
      change (lam i : ℂ) • b i = 0
      rw [hi, Complex.ofReal_zero, zero_smul]
    rw [b.repr_apply_apply]
    exact ((LinearMap.ker T).mem_orthogonal v).mp hv (b i) hker
  have hnorm : ‖v‖ ^ 2 = ∑ i, ‖b.repr v i‖ ^ 2 := by
    rw [← b.repr.norm_map v, PiLp.norm_sq_eq_of_L2]
  have henergy : (⟪T v, v⟫_ℂ).re = ∑ i, lam i * ‖b.repr v i‖ ^ 2 := by
    rw [← b.repr.inner_map_map (T v) v, PiLp.inner_apply]
    change Complex.reCLM (∑ i, inner ℂ (b.repr (T v) i) (b.repr v i)) = _
    rw [map_sum Complex.reCLM]
    apply Finset.sum_congr rfl
    intro i _
    have hdia : b.repr (T v) i = (lam i : ℂ) * b.repr v i :=
      hT.isSymmetric.eigenvectorBasis_apply_self_apply rfl v i
    rw [hdia]
    change (inner ℂ ((lam i : ℂ) • b.repr v i) (b.repr v i)).re = _
    rw [inner_smul_left, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact congrArg (lam i * ·) (inner_self_eq_norm_sq (𝕜 := ℂ) (b.repr v i))
  suffices ∃ i, 0 < lam i ∧ lam i < ε by
    obtain ⟨i, hi, hε⟩ := this
    exact ⟨lam i, hi, hε, heig i⟩
  by_contra hnone
  have hweight (i) : ε * ‖b.repr v i‖ ^ 2 ≤ lam i * ‖b.repr v i‖ ^ 2 := by
    by_cases hi : lam i = 0
    · rw [hcoord_zero i hi]
      simp
    · have hpos : 0 < lam i := lt_of_le_of_ne (hnonneg i) (Ne.symm hi)
      have hlarge : ε ≤ lam i := not_lt.mp fun hlt ↦ hnone ⟨i, hpos, hlt⟩
      exact mul_le_mul_of_nonneg_right hlarge (sq_nonneg _)
  have hlower : ε * ‖v‖ ^ 2 ≤ (⟪T v, v⟫_ℂ).re := by
    rw [hnorm, henergy, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hweight i
  exact (not_lt_of_ge hlower) hRayleigh

/-- The variational step for an arbitrary trial vector of a positive operator on a
finite-dimensional space. Subtracting the projection of the vector onto the kernel keeps the
energy and removes exactly the squared norm of that projection, so the vector need not be
orthogonal to the kernel. arXiv:1210.6613, proof of `thm:gapless`, lines 1302–1314. -/
theorem exists_pos_eigenvalue_lt_of_projection_bound {T : E →ₗ[ℂ] E} (hT : T.IsPositive)
    (v : E) (ε : ℝ)
    (hRayleigh : (⟪T v, v⟫_ℂ).re <
      ε * (‖v‖ ^ 2 - ‖(LinearMap.ker T).starProjection v‖ ^ 2)) :
    ∃ μ : ℝ, 0 < μ ∧ μ < ε ∧ Module.End.HasEigenvalue T (μ : ℂ) := by
  let K := LinearMap.ker T
  let w := v - K.starProjection v
  have hw : w ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal (K := K) v
  have hkill : T (K.starProjection v) = 0 :=
    LinearMap.mem_ker.mp (K.starProjection_apply_mem v)
  have hTw : T w = T v := by
    change T (v - K.starProjection v) = T v
    rw [map_sub, hkill, sub_zero]
  have hcross : inner ℂ (T v) (K.starProjection v) = 0 := by
    rw [hT.isSymmetric v (K.starProjection v), hkill, inner_zero_right]
  have henergy : (⟪T w, w⟫_ℂ).re = (⟪T v, v⟫_ℂ).re := by
    rw [hTw]
    change (inner ℂ (T v) (v - K.starProjection v)).re = _
    rw [inner_sub_right, hcross, sub_zero]
  have hnorm : ‖w‖ ^ 2 = ‖v‖ ^ 2 - ‖K.starProjection v‖ ^ 2 := by
    have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection v K
    have horth : Kᗮ.starProjection v = w :=
      Submodule.starProjection_orthogonal_val (K := K) v
    rw [horth] at hpyth
    linarith
  apply hT.exists_pos_eigenvalue_lt_of_rayleigh w hw ε
  rw [henergy, hnorm]
  exact hRayleigh

end LinearMap.IsPositive
