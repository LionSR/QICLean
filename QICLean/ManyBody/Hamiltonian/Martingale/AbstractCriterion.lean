/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Gap.EigenvalueGap
import QICLean.Analysis.Projection.Geometry
import QICLean.Analysis.Projection.TwoProjectionCompression
import QICLean.Spectral.Gap.WeightedPositiveKernel

/-!
# Abstract martingale criterion (quadratic form → norm bound)

For a positive operator \(H\) on a finite-dimensional complex Hilbert space, the
quadratic-form inequality \(H² ≥ γ H\) (with \(γ > 0\)) implies the norm lower bound
\(γ ‖v‖ ≤ ‖H v‖\) on the orthogonal complement of \(\ker H\). This is the
operator-theoretic kernel of the Kastoryano–Lucia / Nachtergaele martingale
method for spectral gaps. In eigenvalue form,
`FrustrationFree.forall_hasEigenvalue_of_martingale_of_finiteDimensional`, every eigenvalue of
\(H\) other than \(0\) is at least \(γ\). The converse, from the gap to the quadratic-form
inequality, is `LinearMap.IsPositive.quadraticForm_sq_ge_of_forall_hasEigenvalue`.

For a finite family of symmetric projections whose anticommutator forms obey row- and
column-summable bounds, the sum of the projections satisfies the quadratic-form inequality and
hence has the gap `γ` above its kernel
(`FrustrationFree.spectralGap_of_martingale_anticommutator_rowCol_of_finiteDimensional`).

Moved from TNLean, `TNLean/MPS/ParentHamiltonian/Martingale/AbstractCriterion.lean` at
commit `414a18fb88`, with no change to the statements. The row–column criterion is moved from
TNLean, `TNLean/MPS/ParentHamiltonian/ParentInteraction/Reduction.lean` at commit `600676ccac`
(there in the namespace `MPSTensor`), with no change to the statement.

It also contains the following results.

* `FrustrationFree.forall_hasEigenvalue_of_two_ground_projection_bounds`: a sharp comparison from
  two ground projections.
-/

section AbstractCriterion

open scoped BigOperators InnerProductSpace ComplexOrder

namespace FrustrationFree

/--
**Abstract martingale criterion (quadratic form ⟹ norm bound).**

Let \(H\) be a positive linear operator (in the sense of `LinearMap.IsPositive`:
symmetric with \(0 ≤ \operatorname{Re}\langle H v, v\rangle\)) on a finite-dimensional
complex Hilbert space satisfying the quadratic-form inequality

    \(γ ⟨v, H v⟩ ≤ ⟨H v, H v⟩\) for all \(v\),

i.e.\ \(H² ≥ γ H\) as a quadratic form. Then on the orthogonal complement
of \(\ker H\), \(H\) is bounded below in norm by \(γ\):

    \(γ ‖v‖ ≤ ‖H v‖\) for all \(v \perp \ker H\).

The positivity hypothesis is essential: it rules out negative eigenvalues of
small magnitude (such as \(H = -Id\), which otherwise satisfies
\(γ ⟨v, H v⟩ ≤ ⟨H v, H v⟩\) vacuously but fails the conclusion). For a
frustration-free Hamiltonian \(H = ∑ᵢ hᵢ\) whose terms are orthogonal
projections this hypothesis is automatic.

This is the operator-theoretic content of the Kastoryano–Lucia /
Nachtergaele martingale method: once an anticommutator estimate for
overlapping local ground spaces, together with a row-sum bound, produces the
operator inequality \(H² ≥ γ H\) for the positive operator \(H\), the norm
lower bound, and hence the spectral gap for eigenvectors of \(H\), follows by
the spectral theorem. This lemma provides that final step.
-/
theorem spectralGap_of_martingale_of_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {γ : ℝ} (hγ : 0 < γ)
    {H : E →ₗ[ℂ] E} (hH : H.IsPositive)
    (hOpIneq : ∀ v, γ * (⟪H v, v⟫_ℂ).re ≤ (⟪H v, H v⟫_ℂ).re) :
    ∀ v ∈ (LinearMap.ker H)ᗮ, γ * ‖v‖ ≤ ‖H v‖ := by
  classical
  -- Spectral setup: diagonalise the positive symmetric operator.
  set n := Module.finrank ℂ E with hn_def
  have hn : Module.finrank ℂ E = n := hn_def.symm
  have hSym : H.IsSymmetric := hH.isSymmetric
  set b := hSym.eigenvectorBasis hn with hb_def
  set μ : Fin n → ℝ := hSym.eigenvalues hn with hμ_def
  have hμ_nn : ∀ i, 0 ≤ μ i := fun i => hH.nonneg_eigenvalues hn i
  have hHb : ∀ i, H (b i) = ((μ i : ℂ)) • b i := fun i =>
    hSym.apply_eigenvectorBasis hn i
  have hbb : ∀ i j : Fin n, ⟪b i, b j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  -- Apply the operator inequality to each eigenvector: \(γ μᵢ ≤ μᵢ²\).
  have hμ_ineq : ∀ i, γ * μ i ≤ μ i * μ i := by
    intro i
    have key := hOpIneq (b i)
    rw [hHb i] at key
    have e1 : (⟪((μ i : ℂ)) • b i, b i⟫_ℂ).re = μ i := by
      rw [inner_smul_left, hbb i i, ite_eq_left rfl, mul_one, Complex.conj_ofReal,
          Complex.ofReal_re]
    have e2 : (⟪((μ i : ℂ)) • b i, ((μ i : ℂ)) • b i⟫_ℂ).re = μ i * μ i := by
      rw [inner_smul_left, inner_smul_right, hbb i i, ite_eq_left rfl, mul_one,
          Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [e1, e2] at key
    exact key
  -- Combined with \(μᵢ ≥ 0\), this gives \(μᵢ = 0 ∨ γ ≤ μᵢ\) for each \(i\).
  have hμ_alt : ∀ i, μ i = 0 ∨ γ ≤ μ i := by
    intro i
    rcases (hμ_nn i).lt_or_eq with hpos | hzero
    · right
      have := hμ_ineq i
      have hpos' : 0 < μ i := hpos
      nlinarith
    · left; exact hzero.symm
  -- Main argument on \(v ∈ (\ker H)^\perp\).
  intro v hv
  -- Eigenvectors with zero eigenvalue lie in \(\ker H\), hence are orthogonal to \(v\).
  have hker : ∀ i, μ i = 0 → b i ∈ LinearMap.ker H := by
    intro i hi
    rw [LinearMap.mem_ker, hHb i]
    simp [hi]
  have hv_perp : ∀ i, μ i = 0 → ⟪b i, v⟫_ℂ = 0 := fun i hi =>
    Submodule.inner_right_of_mem_orthogonal (hker i hi) hv
  -- Express \(‖v‖²\) and \(‖Hv‖²\) through the eigenvector basis.
  have hv_sq : ‖v‖ ^ 2 = ∑ i, ‖(b.repr v) i‖ ^ 2 := by
    have hiso := b.repr.norm_map v
    rw [← hiso, EuclideanSpace.norm_sq_eq]
  have hHv_sq : ‖H v‖ ^ 2 = ∑ i, (μ i) ^ 2 * ‖(b.repr v) i‖ ^ 2 := by
    have hiso := b.repr.norm_map (H v)
    rw [← hiso, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hSym.eigenvectorBasis_apply_self_apply hn v i, norm_mul, mul_pow,
        RCLike.norm_ofReal, sq_abs]
  -- The quadratic-form bound \(γ² ‖v‖² ≤ ‖Hv‖²\) is now term-by-term.
  have h_sq : γ ^ 2 * ‖v‖ ^ 2 ≤ ‖H v‖ ^ 2 := by
    rw [hv_sq, hHv_sq, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rcases hμ_alt i with hi | hi
    · have h0 : (b.repr v) i = 0 := by
        rw [b.repr_apply_apply]
        exact hv_perp i hi
      rw [h0, norm_zero]
      simp
    · have hγ_sq : γ ^ 2 ≤ (μ i) ^ 2 :=
        pow_le_pow_left₀ hγ.le hi 2
      have hnn : (0 : ℝ) ≤ ‖(b.repr v) i‖ ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right hγ_sq hnn
  -- Take square roots to conclude \(γ ‖v‖ ≤ ‖Hv‖\).
  have h1 : (γ * ‖v‖) ^ 2 ≤ ‖H v‖ ^ 2 := by
    rw [mul_pow]; exact h_sq
  have h2 : 0 ≤ γ * ‖v‖ := mul_nonneg hγ.le (norm_nonneg v)
  have h3 : 0 ≤ ‖H v‖ := norm_nonneg _
  have hsqrt := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq h2, Real.sqrt_sq h3] at hsqrt

/-- **Abstract martingale criterion, eigenvalue form.** If a positive operator \(H\) on a
finite-dimensional complex Hilbert space satisfies \(γ ⟨v, H v⟩ ≤ ⟨H v, H v⟩\) for all \(v\),
with \(γ > 0\), then every eigenvalue of \(H\) other than \(0\) is at least \(γ\). -/
theorem forall_hasEigenvalue_of_martingale_of_finiteDimensional {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {γ : ℝ} (hγ : 0 < γ)
    {H : E →ₗ[ℂ] E} (hH : H.IsPositive)
    (hOpIneq : ∀ v, γ * (⟪H v, v⟫_ℂ).re ≤ (⟪H v, H v⟫_ℂ).re) :
    ∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ (γ : ℂ) ≤ μ :=
  hH.forall_hasEigenvalue_iff_norm.mpr
    (spectralGap_of_martingale_of_finiteDimensional hγ hH hOpIneq)

open Classical in
/-- Combined martingale criterion for a finite family of symmetric projections.

If the anticommutator forms satisfy row- and column-summable bounds with
constant \(γ\), then the sum \(H = \sum_i P_i\) of the projections satisfies
both the quadratic-form inequality
\(γ \operatorname{Re}\langle Hv, v\rangle \le \operatorname{Re}\langle Hv, Hv\rangle\)
for every \(v\), and the gap \(γ\) above the kernel: every eigenvalue of \(H\) other than
\(0\) is at least \(γ\), because \(H\) is positive (a sum of positive maps). -/
theorem spectralGap_of_martingale_anticommutator_rowCol_of_finiteDimensional
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {γ : ℝ} (hγpos : 0 < γ) (hγle : γ ≤ 1)
    (P : ι → E →ₗ[ℂ] E)
    (hP : ∀ i, (P i).IsSymmetricProjection)
    (c : ι → ι → ℝ)
    (hRow : ∀ i, (∑ j ∈ Finset.univ.erase i, c i j) ≤ 1)
    (hCol : ∀ j, (∑ i ∈ Finset.univ.erase j, c i j) ≤ 1)
    (hAnti : ∀ i j, j ∈ Finset.univ.erase i → ∀ v,
      -(1 - γ) * c i j *
          ((⟪P i v, v⟫_ℂ).re + (⟪P j v, v⟫_ℂ).re) ≤
        (⟪P i v, P j v⟫_ℂ).re + (⟪P j v, P i v⟫_ℂ).re) :
    (∀ v, γ * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤ (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re) ∧
    ∀ μ : ℂ, Module.End.HasEigenvalue (∑ i, P i) μ → μ = 0 ∨ (γ : ℂ) ≤ μ := by
  have hQuad : ∀ v,
      γ * (⟪(∑ i, P i) v, v⟫_ℂ).re ≤ (⟪(∑ i, P i) v, (∑ i, P i) v⟫_ℂ).re :=
    ProjectionGeometry.quadraticForm_sum_projections_of_anticommutator_rowCol
      hγle P hP c hRow hCol hAnti
  exact ⟨hQuad, forall_hasEigenvalue_of_martingale_of_finiteDimensional hγpos
    (LinearMap.isPositive_sum Finset.univ fun i _ => (hP i).isPositive) hQuad⟩

end FrustrationFree

end AbstractCriterion

section TwoGroundProjectionGap

/-!
## A sharp comparison from two ground projections

Let two interval ground spaces contain the ground space of an open chain.
If the product of their orthogonal projections differs from the full ground
projection by at most \(c<1\), then their complementary projections have
sum bounded below by \(1-c\) on the full ground-space complement. An energy
comparison with coefficient \(\kappa\) therefore gives a gap
\(\kappa(1-c)\): every eigenvalue of the Hamiltonian other than \(0\) is at
least \(\kappa(1-c)\).

This is an auxiliary consequence of the three-interval ground-projection
estimate in Nachtergaele, arXiv:cond-mat/9410110, Section 6, Lemma
`commutation` (ii). The proof uses the Friedrichs-angle anticommutator
inequality for the complementary projections. In contrast to a triangle
inequality, this comparison retains the limiting coefficient as the
projection defect tends to zero.

Moved from TNLean, `TNLean/MPS/ParentHamiltonian/Martingale/TwoGroundProjectionGap.lean` at
commit `414a18fb88`. The gap, stated there as a norm bound on the orthogonal complement of the
kernel, is stated here with eigenvalues.
-/

open scoped InnerProductSpace ComplexOrder

namespace FrustrationFree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

private theorem intersection_eq_of_strict_defect
    (U V W : Submodule ℂ E) {c : ℝ} (hc : c < 1)
    (hWU : W ≤ U) (hWV : W ≤ V)
    (hDefect : ‖W.starProjection - U.starProjection.comp V.starProjection‖ ≤ c) :
    W = U ⊓ V := by
  refine le_antisymm (le_inf hWU hWV) ?_
  intro v hv
  let z := v - W.starProjection v
  have hzU : z ∈ U := U.sub_mem hv.1 (hWU (W.starProjection_apply_mem v))
  have hzV : z ∈ V := V.sub_mem hv.2 (hWV (W.starProjection_apply_mem v))
  have hzW : z ∈ Wᗮ := W.sub_starProjection_mem_orthogonal v
  have hNorm : ‖z‖ ≤ c * ‖z‖ := by
    simpa only [sub_apply, ContinuousLinearMap.comp_apply,
      W.starProjection_apply_eq_zero_iff.mpr hzW,
      V.starProjection_eq_self_iff.mpr hzV, U.starProjection_eq_self_iff.mpr hzU,
      zero_sub, norm_neg] using ContinuousLinearMap.le_of_opNorm_le
        (W.starProjection - U.starProjection.comp V.starProjection) hDefect z
  have hz : z = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg z])
  exact W.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm

private theorem sum_excitation_ker (U V : Submodule ℂ E) :
    LinearMap.ker (Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap) = U ⊓ V := by
  simpa [Submodule.ker_starProjection, Fintype.sum_bool, iInf_bool_eq, inf_comm] using
    (WeightedPositiveKernel.ker_sum_eq_iInf (P := fun b : Bool =>
      if b then Uᗮ.starProjection.toLinearMap else Vᗮ.starProjection.toLinearMap)
      (by intro b; cases b <;> exact (Submodule.isSymmetricProjection_starProjection _).isPositive))

private theorem sum_excitation_gap (U V : Submodule ℂ E) {c : ℝ} (hc : c < 1)
    (hDefect : ‖U.starProjection.comp V.starProjection - (U ⊓ V).starProjection‖ ≤ c) :
    ∀ v ∈ (U ⊓ V)ᗮ, (1 - c) * ‖v‖ ≤
      ‖(Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap) v‖ := by
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hDefect
  have hAngle := Submodule.isFriedrichsBound_of_norm_starProjection_comp_sub_inf_starProjection_le
    U V hDefect
  have hPositive := (Submodule.isSymmetricProjection_starProjection Uᗮ).isPositive.add
    (Submodule.isSymmetricProjection_starProjection Vᗮ).isPositive
  suffices hGap : ∀ v ∈ (LinearMap.ker
      (Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap))ᗮ,
      (1 - c) * ‖v‖ ≤ ‖(Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap) v‖
    by simpa only [sum_excitation_ker] using hGap
  apply FrustrationFree.spectralGap_of_martingale_of_finiteDimensional (sub_pos.mpr hc)
    hPositive
  intro v
  have hAnti :=
    Submodule.re_inner_anticommutator_starProjection_orthogonal_ge_neg_of_friedrichs_bound
      U V hc0 hAngle v
  simp only [LinearMap.add_apply, ContinuousLinearMap.coe_coe, inner_add_left,
    inner_add_right, RCLike.re_eq_complex_re, Complex.add_re] at hAnti ⊢
  have hDiag (S : Submodule ℂ E) : (⟪S.starProjection v, S.starProjection v⟫_ℂ).re =
      (⟪S.starProjection v, v⟫_ℂ).re := by
    rw [← S.inner_starProjection_left_eq_right, S.starProjection_eq_self_iff.mpr
      (S.starProjection_apply_mem v)]
  nlinarith [hDiag Uᗮ, hDiag Vᗮ]

/-- If two ground spaces contain \(\ker H\), their projection defect is
at most \(c<1\), and \(H\) dominates \(\kappa\) times the sum of their
excitation projections, then every eigenvalue of \(H\) other than \(0\) is
at least \(\kappa(1-c)\). The positivity of \(H\) follows from the
comparison.

This is the sharp two-interval comparison used with Nachtergaele,
arXiv:cond-mat/9410110, Section 6, Lemma `commutation` (ii). The strict
projection-defect bound also forces the two ground spaces to intersect
exactly in \(\ker H\). -/
theorem forall_hasEigenvalue_of_two_ground_projection_bounds (H : E →ₗ[ℂ] E) (U V : Submodule ℂ E)
    {κ c : ℝ} (hκ : 0 ≤ κ) (hc : c < 1)
    (hWU : LinearMap.ker H ≤ U) (hWV : LinearMap.ker H ≤ V)
    (hLower : (κ : ℂ) • (Uᗮ.starProjection.toLinearMap +
      Vᗮ.starProjection.toLinearMap) ≤ H)
    (hDefect : ‖(LinearMap.ker H).starProjection -
      U.starProjection.comp V.starProjection‖ ≤ c) :
    ∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ ((κ * (1 - c) : ℝ) : ℂ) ≤ μ := by
  have hInter := intersection_eq_of_strict_defect U V (LinearMap.ker H) hc hWU hWV hDefect
  have hSumPos := (Submodule.isSymmetricProjection_starProjection Uᗮ).isPositive.add
    (Submodule.isSymmetricProjection_starProjection Vᗮ).isPositive
  have hAngleDefect : ‖U.starProjection.comp V.starProjection -
      (U ⊓ V).starProjection‖ ≤ c := by simpa only [hInter, norm_sub_rev] using hDefect
  have hSumGap : ∀ v ∈ (LinearMap.ker
      (Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap))ᗮ,
      (1 - c) * ‖v‖ ≤ ‖(Uᗮ.starProjection.toLinearMap + Vᗮ.starProjection.toLinearMap) v‖ :=
    by simpa only [sum_excitation_ker] using sum_excitation_gap U V hc hAngleDefect
  have hH : H.IsPositive := LinearMap.nonneg_iff_isPositive.mp
    ((LinearMap.nonneg_iff_isPositive.mpr
      (hSumPos.smul_of_nonneg (Complex.zero_le_real.mpr hκ))).trans hLower)
  refine hH.forall_hasEigenvalue_iff_re_inner.mpr fun v hv ↦ ?_
  have hEnergy := hSumPos.re_inner_ge_of_norm_gap (sub_nonneg.mpr hc.le) hSumGap v
    (by simpa only [sum_excitation_ker, ← hInter] using hv)
  have hComparison : κ * (⟪(Uᗮ.starProjection.toLinearMap +
      Vᗮ.starProjection.toLinearMap) v, v⟫_ℂ).re ≤ (⟪H v, v⟫_ℂ).re := by
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_left,
      inner_smul_left, RCLike.re_eq_complex_re, Complex.conj_ofReal,
      Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, sub_nonneg] using
      hLower.re_inner_nonneg_left v
  rw [← hH.isSymmetric v v]
  simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hEnergy hκ).trans hComparison

end FrustrationFree

end TwoGroundProjectionGap
