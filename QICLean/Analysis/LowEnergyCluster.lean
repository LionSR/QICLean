/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyPerturbation
import QICLean.Analysis.ViableSubspaceDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A low-energy cluster from restricted residual estimates

Let two operators have complete orthonormal eigenbases with real eigenvalues.
Suppose the original spectrum consists of an energy `e` and eigenvalues at
least `e + γ`. Two small residual estimates, on the original low spectral
span and on a larger perturbed low spectral span, identify the perturbed low
cluster. Its dimension equals the full original ground-space dimension and
the two spaces approximate one another with squared projection loss `1 / 200`.

All cutoffs are absolute energies relative to `e`. No comparison of minimum
energies or physical truncation estimate is contained in this assertion. The
result is a finite-dimensional auxiliary to ALVV, arXiv:1602.08828v2,
`lem:hard-trunc`, lines 955–968, and the proof of `t:ais`, lines 1010–1024.

**Local fix (window count):** The perturbation estimate uses the corrected
count in `docs/paper-gaps/alvv16_hard_truncation_windows.tex`, rather than the
printed count involving an absolute ground energy.
-/

open scoped InnerProductSpace

/-- A lower quadratic-form bound and a residual at one unit eigenvector
give a lower bound for its real eigenvalue. Auxiliary to ALVV,
arXiv:1602.08828v2, lines 955–968 and 1010–1024. -/
private theorem real_eigenvalue_ge_of_unit_residual {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B : E → E) (x : E) (e lam ξ : ℝ) (hx : ‖x‖ = 1)
    (hBx : B x = (lam : ℂ) • x)
    (hlower : e * ‖x‖ ^ 2 ≤ (⟪x, A x⟫_ℂ).re)
    (hres : ‖A x - B x‖ ≤ ξ) : e - ξ ≤ lam := by
  have hlam : (⟪x, B x⟫_ℂ).re = lam := by
    rw [hBx, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
    simp
  have hdiff : (⟪x, A x⟫_ℂ).re - lam ≤ ξ := by
    calc
      (⟪x, A x⟫_ℂ).re - lam = (⟪x, A x - B x⟫_ℂ).re := by
        rw [inner_sub_right, Complex.sub_re, hlam]
      _ ≤ ‖x‖ * ‖A x - B x‖ := re_inner_le_norm (𝕜 := ℂ) x (A x - B x)
      _ ≤ ξ := by simpa only [hx, one_mul] using hres
  have he : e ≤ (⟪x, A x⟫_ℂ).re := by
    simpa only [hx, one_pow, mul_one] using hlower
  linarith

namespace OrthonormalBasis

/-- The energy quadratic form is the sum of the real eigenvalues weighted
by the squared expansion coefficients. Auxiliary to the low-energy bounds
in ALVV, arXiv:1602.08828v2, `lem:hard-trunc`, lines 955–968,
and Theorem `t:ais`, lines 1010–1024. -/
private theorem re_inner_apply_eq_sum_of_eigen
    {E n : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype n]
    (b : OrthonormalBasis n ℂ E) (a : n → ℝ) (H : E →ₗ[ℂ] E)
    (hH : ∀ j, H (b j) = (a j : ℂ) • b j) (x : E) :
    (inner ℂ x (H x)).re = ∑ j, a j * ‖b.repr x j‖ ^ 2 := by
  classical
  rw [← b.repr.inner_map_map x (H x), PiLp.inner_apply]
  change Complex.reCLM (∑ j, inner ℂ (b.repr x j) (b.repr (H x) j)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (inner ℂ (b.repr x j) (b.repr (H x) j)).re = a j * ‖b.repr x j‖ ^ 2
  rw [RCLike.inner_apply, b.repr_apply_of_eigen a hH x j, mul_assoc]
  let z : ℂ := b.repr x j
  change ((a j : ℂ) * (z * (starRingEnd ℂ) z)).re = a j * ‖z‖ ^ 2
  have hscalar : ((a j : ℂ) * (z * (starRingEnd ℂ) z)).re =
      a j * (z * (starRingEnd ℂ) z).re :=
    Complex.re_ofReal_mul (a j) (z * (starRingEnd ℂ) z)
  have hz : (z * (starRingEnd ℂ) z).re = ‖z‖ ^ 2 := by
    change RCLike.re (inner ℂ z z) = ‖z‖ ^ 2
    exact inner_self_eq_norm_sq (𝕜 := ℂ) z
  exact hscalar.trans (congrArg (fun r : ℝ ↦ a j * r) hz)

end OrthonormalBasis

/-- One common window bound for the two directions of the low-energy
comparison. The width is at most the original gap. Auxiliary to ALVV,
arXiv:1602.08828v2, lines 955–968. -/
private theorem low_cluster_window_bound {γ ξ w v : ℝ}
    (hγ : 0 < γ) (hξ : 0 ≤ ξ) (hξγ : ξ ≤ γ / 1000000)
    (hw : w ≤ γ) (hv : γ / 40 ≤ v) :
    (⌈w / (2 * (γ / 1000000))⌉₊ : ℝ) * (ξ + γ / 1000000) ^ 2 ≤
      (1 / 200 : ℝ) * (v + γ / 1000000) ^ 2 := by
  have hden : 0 < 2 * (γ / 1000000) := by positivity
  have hceil : ⌈w / (2 * (γ / 1000000))⌉₊ ≤ 500001 := by
    apply Nat.ceil_le.mpr
    norm_num only [Nat.cast_ofNat]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hceilR : (⌈w / (2 * (γ / 1000000))⌉₊ : ℝ) ≤ 500001 := by
    exact_mod_cast hceil
  have hsquare : (ξ + γ / 1000000) ^ 2 ≤ (2 * γ / 1000000) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hsep : (γ / 40) ^ 2 ≤ (v + γ / 1000000) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  calc
    (⌈w / (2 * (γ / 1000000))⌉₊ : ℝ) * (ξ + γ / 1000000) ^ 2
        ≤ 500001 * (ξ + γ / 1000000) ^ 2 :=
      mul_le_mul_of_nonneg_right hceilR (sq_nonneg _)
    _ ≤ 500001 * (2 * γ / 1000000) ^ 2 := by gcongr
    _ ≤ (1 / 200 : ℝ) * (γ / 40) ^ 2 := by nlinarith [sq_nonneg γ]
    _ ≤ (1 / 200 : ℝ) * (v + γ / 1000000) ^ 2 := by gcongr

namespace Submodule

/-- Monotonicity of a closed low-energy span, used in the finite cutoff
comparison in ALVV, arXiv:1602.08828v2, lines 955–968 and 1020. -/
private theorem spectralSpanLE_mono_cutoff
    {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]
    (b : OrthonormalBasis ι ℂ F) (a : ι → ℝ) {c d : ℝ} (hcd : c ≤ d) :
    spectralSpanLE b a c ≤ spectralSpanLE b a d := by
  apply span_mono
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨j, hj.trans hcd, rfl⟩

/-- A recorded eigenvector belongs to every closed spectral span whose
cutoff is at least its eigenvalue. Auxiliary to ALVV, arXiv:1602.08828v2,
lines 955–968. -/
private theorem basis_mem_spectralSpanLE
    {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]
    (b : OrthonormalBasis ι ℂ F) (a : ι → ℝ) {c : ℝ} (j : ι) (hj : a j ≤ c) :
    b j ∈ spectralSpanLE b a c :=
  subset_span ⟨j, hj, rfl⟩

/-- Below an actual gap, the closed low-energy span is the full ground
space, with arbitrary degeneracy. Auxiliary to ALVV, arXiv:1602.08828v2,
proof of `t:ais`, lines 1010–1024. -/
private theorem spectralSpanLE_eq_ground_of_dichotomy
    {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]
    (b : OrthonormalBasis ι ℂ F) (a : ι → ℝ) {e γ c : ℝ}
    (hspec : ∀ j, a j = e ∨ e + γ ≤ a j) (hec : e ≤ c) (hcg : c < e + γ) :
    spectralSpanLE b a c = spectralSpanLE b a e := by
  apply le_antisymm
  · intro x hx
    rw [mem_spectralSpanLE_iff] at hx ⊢
    intro j hj
    apply hx j
    rcases hspec j with h | h
    · exact False.elim ((ne_of_gt hj) h)
    · linarith
  · exact spectralSpanLE_mono_cutoff b a hec

/-- Two actual restricted residual bounds identify the whole perturbed low
cluster, preserve the ground-space dimension, and leave a spectral interval
empty. This is a finite-dimensional auxiliary to ALVV, arXiv:1602.08828v2,
`lem:hard-trunc`, lines 955–968, and `t:ais`, lines 1010–1024. No full operator
norm bound, one-dimensional ground space, eigenvalue attainment above the gap,
or shifted-minimum estimate is assumed or concluded. -/
theorem low_spectral_cluster_of_restricted_residuals
    {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] [Fintype ι]
    (H H' : F →L[ℂ] F) (b b' : OrthonormalBasis ι ℂ F) (a a' : ι → ℝ)
    (hH : ∀ j, H (b j) = (a j : ℂ) • b j)
    (hH' : ∀ j, H' (b' j) = (a' j : ℂ) • b' j)
    (e γ ξ : ℝ) (hγ : 0 < γ) (hξ : 0 ≤ ξ) (hξγ : ξ ≤ γ / 1000000)
    (hspec : ∀ j, a j = e ∨ e + γ ≤ a j)
    (hres : ‖(H - H').domRestrict (spectralSpanLE b a (e + γ / 40))‖ ≤ ξ)
    (hres' : ‖(H - H').domRestrict (spectralSpanLE b' a' (e + 19 * γ / 20))‖ ≤ ξ) :
    let G := spectralSpanLE b a e
    let U := spectralSpanLE b' a' (e + γ / 20)
    let V := spectralSpanLE b' a' (e + 19 * γ / 20)
    U = V ∧ Module.finrank ℂ U = Module.finrank ℂ G ∧
      IsCloseTo (1 / 200 : ℝ) U G ∧ IsCloseTo (1 / 200 : ℝ) G U ∧
      (∀ τ : ℝ, e + γ / 20 ≤ τ → τ ≤ e + 19 * γ / 20 →
        spectralSpanLE b' a' τ = U ∧
        IsCloseTo (1 / 200 : ℝ) (spectralSpanLE b' a' τ) G ∧
        IsCloseTo (1 / 200 : ℝ) G (spectralSpanLE b' a' τ)) ∧
      (∀ j, a' j ≤ e + γ / 10 ∨ e + 9 * γ / 10 ≤ a' j) := by
  classical
  dsimp only
  let G := spectralSpanLE b a e
  let U := spectralSpanLE b' a' (e + γ / 20)
  let V := spectralSpanLE b' a' (e + 19 * γ / 20)
  change U = V ∧ Module.finrank ℂ U = Module.finrank ℂ G ∧
    IsCloseTo (1 / 200 : ℝ) U G ∧ IsCloseTo (1 / 200 : ℝ) G U ∧
    (∀ τ : ℝ, e + γ / 20 ≤ τ → τ ≤ e + 19 * γ / 20 →
      spectralSpanLE b' a' τ = U ∧
      IsCloseTo (1 / 200 : ℝ) (spectralSpanLE b' a' τ) G ∧
      IsCloseTo (1 / 200 : ℝ) G (spectralSpanLE b' a' τ)) ∧
    (∀ j, a' j ≤ e + γ / 10 ∨ e + 9 * γ / 10 ≤ a' j)
  have hfloor (j : ι) : e ≤ a j := by
    rcases hspec j with h | h
    · exact h.ge
    · linarith
  have hlower (x : F) : e * ‖x‖ ^ 2 ≤ (inner ℂ x (H x)).re := by
    have hnorm : ‖x‖ ^ 2 = ∑ j, ‖b.repr x j‖ ^ 2 := by
      rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]
    have hquad : (inner ℂ x (H x)).re = ∑ j, a j * ‖b.repr x j‖ ^ 2 :=
      b.re_inner_apply_eq_sum_of_eigen a H.toLinearMap hH x
    rw [hquad, hnorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hfloor j) (sq_nonneg _)
  have hvector (x : F) (hx : x ∈ spectralSpanLE b a (e + γ / 40)) :
      ‖H x - H' x‖ ≤ ξ * ‖x‖ := by
    have hxbound := ((H - H').domRestrict (spectralSpanLE b a (e + γ / 40))).le_of_opNorm_le
      hres ⟨x, hx⟩
    change ‖H x - H' x‖ ≤ ξ * ‖x‖ at hxbound
    exact hxbound
  have hvector' (x : F) (hx : x ∈ spectralSpanLE b' a' (e + 19 * γ / 20)) :
      ‖H x - H' x‖ ≤ ξ * ‖x‖ := by
    have hxbound :=
      ((H - H').domRestrict (spectralSpanLE b' a' (e + 19 * γ / 20))).le_of_opNorm_le
        hres' ⟨x, hx⟩
    change ‖H x - H' x‖ ≤ ξ * ‖x‖ at hxbound
    exact hxbound
  have hfloor' (j : ι) (hj : a' j ≤ e + 19 * γ / 20) : e - ξ ≤ a' j := by
    have hjmem := basis_mem_spectralSpanLE b' a' j hj
    have hjres : ‖H (b' j) - H' (b' j)‖ ≤ ξ := by
      simpa only [b'.norm_eq_one j, mul_one] using hvector' (b' j) hjmem
    exact real_eigenvalue_ge_of_unit_residual
      (fun x => H x) (fun x => H' x) (b' j) e (a' j) ξ
      (b'.norm_eq_one j) (hH' j) (hlower (b' j)) hjres
  have hα : spectralSpanLE b a (e + γ / 40) = G :=
    spectralSpanLE_eq_ground_of_dichotomy b a hspec (by linarith) (by linarith)
  have hω : spectralSpanLE b a (e + 39 * γ / 40) = G :=
    spectralSpanLE_eq_ground_of_dichotomy b a hspec (by linarith) (by linarith)
  have hUG : IsCloseTo (1 / 200 : ℝ) U G := by
    have hp := isCloseTo_spectralSpanLE_of_perturbation b b' a a'
      (H := H.toLinearMap) (H' := H'.toLinearMap) hH hH'
      (c := e + γ / 40) (c' := e + γ / 20) (ξ := ξ)
      (h := γ / 1000000) (m := e) (δ := 1 / 200)
      hvector (by positivity) (fun j _ => hfloor j) (by linarith) (by linarith)
      (low_cluster_window_bound hγ hξ hξγ (by linarith) (by linarith))
    simpa only [hα] using hp
  have hGV : IsCloseTo (1 / 200 : ℝ) G V := by
    have hreverse (x : F) (hx : x ∈ spectralSpanLE b' a' (e + 19 * γ / 20)) :
        ‖H' x - H x‖ ≤ ξ * ‖x‖ := by
      rw [norm_sub_rev]
      exact hvector' x hx
    have hp := isCloseTo_spectralSpanLE_of_perturbation b' b a' a
      (H := H'.toLinearMap) (H' := H.toLinearMap) hH' hH
      (c := e + 19 * γ / 20) (c' := e + 39 * γ / 40) (ξ := ξ)
      (h := γ / 1000000) (m := e - ξ) (δ := 1 / 200)
      hreverse (by positivity) hfloor' (by linarith) (by linarith)
      (low_cluster_window_bound hγ hξ hξγ (by linarith) (by linarith))
    simpa only [hω] using hp
  have hUV : U ≤ V := spectralSpanLE_mono_cutoff b' a' (by linarith)
  obtain ⟨hEq, hIntermediate⟩ := eq_and_isCloseTo_of_le hUV hUG hGV
    (by norm_num) (by norm_num)
  have hGU : IsCloseTo (1 / 200 : ℝ) G U := by simpa only [hEq] using hGV
  have hdim : Module.finrank ℂ U = Module.finrank ℂ G :=
    le_antisymm (hGU.finrank_le (by norm_num)) (hUG.finrank_le (by norm_num))
  refine ⟨hEq, hdim, hUG, hGU, ?_, ?_⟩
  · intro τ hτlo hτhi
    exact hIntermediate (spectralSpanLE b' a' τ)
      (spectralSpanLE_mono_cutoff b' a' hτlo)
      (spectralSpanLE_mono_cutoff b' a' hτhi)
  · intro j
    by_cases hj : a' j ≤ e + γ / 20
    · left; linarith
    · right
      have hlarge : e + 19 * γ / 20 < a' j := by
        by_contra hnot
        have hv : b' j ∈ V := basis_mem_spectralSpanLE b' a' j (le_of_not_gt hnot)
        have hu : b' j ∈ U := by rw [hEq]; exact hv
        have hz := (mem_spectralSpanLE_iff b' a' (e + γ / 20) (b' j)).mp hu j
          (lt_of_not_ge hj)
        simp at hz
      linarith

end Submodule
