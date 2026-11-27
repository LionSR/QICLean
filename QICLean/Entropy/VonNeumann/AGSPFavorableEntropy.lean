/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.VonNeumann.Entropy
import QICLean.Entropy.Classical.ProbabilityEntropyRankTails
import QICLean.Channel.Schmidt.AGSPGeometricTails
import QICLean.Analysis.Real.CappedGeometricSum

/-!
# Entropy under a favorable approximate-projection tradeoff

Let a bipartite operator fix a unit vector and preserve its orthogonal
complement. If its squared-norm shrinking factor is δ, its operator-Schmidt
rank is at most D, and Dδ ≤ 1/2, then the original vector has reduced entropy
at most 4 log D. Logarithms are natural.

For D ≥ 2, the proof sums the original vector's descending Schmidt tails,
retaining the contribution of the first two rank cutoffs. For D = 1, the
invariant vector has Schmidt rank at most one and its reduced entropy is zero.
The shrinking factor may be any real number.

## Main statements

* `Matrix.vonNeumannEntropy_reduced_le_four_log_of_operatorSchmidtRank`: the
  fixed-vector entropy bound, with no supplied spectral-tail premise.
* `Matrix.vonNeumannEntropy_reduced_le_log_of_zero_perpendicular_shrinking`,
  `Matrix.vonNeumannEntropy_reduced_le_of_operatorSchmidtRank_of_product_overlap`: A corrected
  general approximate-projector entropy estimate.

## References

AKLV, arXiv:1301.1162v1, Definition 2.1 (`def:AGSP`), Corollary 2.4
(`col:half`), lines 296–361, and the rank-tail entropy argument, lines 1059–1075.
This is a quantitative auxiliary for the invariant-line setting.
The unrestricted printed entropy formula is discussed in the source note:
https://github.com/LionSR/QICLean/blob/ff2f24570636412fc4dab308a45e171815424b71/docs/paper-gaps/aklv13_entropy_small_shrinking.tex
-/

section AGSPFavorableEntropy

open scoped BigOperators Matrix InnerProductSpace ComplexOrder

/-- The geometric entropy coefficient is at most four logarithms of the rank
bound. This is the finite comparison supporting AKLV, arXiv:1301.1162v1,
Corollary 2.4 (`col:half`), with natural logarithms. -/
private theorem favorable_geometric_coefficient_le_four_log
    (D : ℕ) (hD : 2 ≤ D) :
    2 * Real.log (D : ℝ) +
        (Real.log 2 + (1 / (2 * (D : ℝ))) * Real.log (D : ℝ)) /
          (1 - 1 / (2 * (D : ℝ))) ≤
      4 * Real.log (D : ℝ) := by
  have hDreal : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hlogD : 0 ≤ Real.log (D : ℝ) :=
    Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2 : ℝ) ≤ Real.log (D : ℝ) :=
    Real.log_le_log (by norm_num) hDreal
  let θ : ℝ := 1 / (2 * (D : ℝ))
  have hθ : θ ≤ 1 / 4 := by
    dsimp only [θ]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hden : 0 < 1 - θ := by linarith
  have hprod : θ * Real.log (D : ℝ) ≤ (1 / 4) * Real.log (D : ℝ) :=
    mul_le_mul_of_nonneg_right hθ hlogD
  have hfrac :
      (Real.log 2 + θ * Real.log (D : ℝ)) / (1 - θ) ≤
        2 * Real.log (D : ℝ) := by
    apply (div_le_iff₀ hden).2
    nlinarith
  change 2 * Real.log (D : ℝ) +
      (Real.log 2 + θ * Real.log (D : ℝ)) / (1 - θ) ≤
    4 * Real.log (D : ℝ)
  linarith

open Classical in
/-- A finite geometric bound on the descending spectrum of a density matrix
implies an entropy bound. This is the finite entropy summation supporting
AKLV, arXiv:1301.1162v1, col:half and lines 1059–1075. The spectral tail
hypothesis is explicit; deriving it from an operator is a separate result. -/
private theorem Matrix.vonNeumannEntropy_le_four_log_of_geometric_eigenvalue_tails
    {m : Type*} [Fintype m] (ρ : Matrix m m ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (D : ℕ) (hD : 2 ≤ D)
    (htail : ∀ i < Fintype.card m,
      (∑ b ∈ Finset.univ.filter (fun b : Fin (Fintype.card m) ↦ D ^ (2 + i) ≤ b.val),
        hρ.isHermitian.eigenvalues₀ b) ≤ (1 / (2 * (D : ℝ))) ^ (i + 1)) :
    vonNeumannEntropy ρ hρ.isHermitian ≤ 4 * Real.log (D : ℝ) := by
  rw [vonNeumannEntropy_eq_probabilityEntropy_eigenvalues₀]
  refine (Entropy.probabilityEntropy_le_of_geometricRankTailBounds
    (fun b : Fin (Fintype.card m) ↦ hρ.isHermitian.eigenvalues₀ b)
    2 (Fintype.card m) D (1 / (2 * (D : ℝ)))
    ?hp ?hsum (by omega) (by positivity) ?hθ1 ?hcover htail).trans
      (favorable_geometric_coefficient_le_four_log D hD)
  case hcover =>
    calc
      Fintype.card m = 1 * Fintype.card m := (one_mul _).symm
      _ ≤ D * Fintype.card m := Nat.mul_le_mul_right _ (by omega)
      _ ≤ D ^ Fintype.card m := Nat.mul_le_pow (by omega) _
      _ ≤ D ^ (2 + Fintype.card m) := pow_le_pow_right' (by omega) (by omega)
  case hsum =>
    simpa [htr] using hρ.isHermitian.sum_eigenvalues₀_filter_le 0
  case hp =>
    exact fun b ↦ by
      simpa only [Matrix.IsHermitian.descEigenvalue, dite_eq_left b.isLt] using
        hρ.descEigenvalue_nonneg b.val
  case hθ1 =>
    exact (div_lt_one (by positivity)).2
      (by exact_mod_cast (show 1 < 2 * D by omega))

namespace Matrix

open Classical in
/-- A fixed unit vector has zero reduced entropy when an operator of
operator-Schmidt rank at most one contracts its orthogonal complement by a
squared-norm factor below one. This is the rank-one endpoint of AKLV,
arXiv:1301.1162v1, def:AGSP and col:half, lines 296–361. No sign condition
on the real shrinking parameter is assumed. -/
private theorem vonNeumannEntropy_reduced_eq_zero_of_operatorSchmidtRank_le_one
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    {δ : ℝ}
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ)
    (hrank : Matrix.operatorSchmidtRank K ≤ 1) (hδ : δ < 1) :
    let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
    vonNeumannEntropy (C * Cᴴ) (posSemidef_self_mul_conjTranspose C).isHermitian = 0 := by
  refine vonNeumannEntropy_eq_zero_of_rank_le_one
    (posSemidef_self_mul_conjTranspose (schmidtCoeffMatrix (WithLp.ofLp Γ))) ?htr ?hr
  case htr =>
    exact trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one Γ hΓ
  case hr =>
    simpa only [rank_self_mul_conjTranspose, schmidtRank] using
      schmidtRank_le_one_of_operatorSchmidtRank_le_one K Γ hΓ hfix hperp hrank hδ

end Matrix

open Classical in
/-- A fixed-vector entropy bound under a favorable operator-Schmidt-rank
and squared-norm shrinking tradeoff. This is a direct quantitative auxiliary
for AKLV arXiv:1301.1162v1, Corollary 2.4 (`col:half`), lines 350–361,
in the unique-ground-vector setting; it does not use the printed Lemma 2.3
(`lem:S`). For the general printed entropy formula, see the small-shrinking note cited below.

The entropy is that of the original fixed vector. The printed general entropy lemma is not used. -/
theorem Matrix.vonNeumannEntropy_reduced_le_four_log_of_operatorSchmidtRank
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ : EuclideanSpace ℂ (m × n))
    (hΓ : ‖Γ‖ = 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    {D : ℕ} {δ : ℝ}
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ)
    (hrank : Matrix.operatorSchmidtRank K ≤ D)
    (htradeoff : (D : ℝ) * δ ≤ 1 / 2) :
    let C := Matrix.schmidtCoeffMatrix (WithLp.ofLp Γ)
    vonNeumannEntropy (C * Cᴴ)
      (Matrix.posSemidef_self_mul_conjTranspose C).isHermitian ≤
        4 * Real.log (D : ℝ)
 := by
  classical
  have hKne : K ≠ 0 := by
    rintro rfl
    simpa [hΓ] using congrArg norm hfix
  have hD : 1 ≤ D := Nat.succ_le_of_lt
    ((Matrix.operatorSchmidtRank_pos_of_ne_zero K hKne).trans_le hrank)
  let C := Matrix.schmidtCoeffMatrix (WithLp.ofLp Γ)
  let hρ := Matrix.posSemidef_self_mul_conjTranspose C
  change vonNeumannEntropy (C * Cᴴ) hρ.isHermitian ≤ 4 * Real.log (D : ℝ)
  have htr : (C * Cᴴ).trace = 1 :=
    Matrix.trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one Γ hΓ
  by_cases hD2 : 2 ≤ D
  · apply Matrix.vonNeumannEntropy_le_four_log_of_geometric_eigenvalue_tails
      (C * Cᴴ) hρ htr D hD2
    exact fun i _hi ↦ Matrix.sum_eigenvalues_geometric_tail_of_operatorSchmidtRank
      K Γ hΓ hfix hperp hrank htradeoff i
  · obtain rfl : D = 1 := by omega
    have hδ : δ < 1 := by
      norm_num at htradeoff
      linarith
    have hzero := Matrix.vonNeumannEntropy_reduced_eq_zero_of_operatorSchmidtRank_le_one
      K Γ hΓ hfix hperp hrank hδ
    simpa only [Nat.cast_one, Real.log_one, mul_zero] using le_of_eq hzero

end AGSPFavorableEntropy

section AGSPGeneralEntropy

/-!
## A corrected general approximate-projector entropy estimate

A unit product vector with nonzero overlap with an invariant unit vector gives
an entropy bound with an additive logarithm of the operator Schmidt rank. The
operator need not satisfy the favorable rank-times-shrinking tradeoff.

**Local fix (general entropy estimate):** The estimate has the necessary additive
term missing from AKLV, arXiv:1301.1162v1, Lemma 2.3 (`lem:S`), lines 339–348.
The printed formula and its Bell-vector counterexample remain documented in
`docs/paper-gaps/aklv13_entropy_small_shrinking.tex`. The invariant-line
hypotheses are those of the source's unique-ground applications in Sections 4
and 6.1. No arbitrary degenerate-ground-space extension is asserted.
-/

open scoped BigOperators InnerProductSpace Matrix ComplexOrder

namespace Matrix

/-- The exact-projection endpoint has entropy at most the logarithm of its
operator Schmidt rank. This corrects the zero-shrinking endpoint of AKLV,
arXiv:1301.1162v1, `lem:S`, lines 339–348. -/
theorem vonNeumannEntropy_reduced_le_log_of_zero_perpendicular_shrinking
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ φ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1)
    (hφrank : schmidtRank (WithLp.ofLp φ) ≤ 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ 0)
    {D : ℕ} (hrank : Matrix.operatorSchmidtRank K ≤ D)
    (ha : ⟪Γ, φ⟫_ℂ ≠ 0) :
    let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
    vonNeumannEntropy (C * Cᴴ) (posSemidef_self_mul_conjTranspose C).isHermitian ≤
      Real.log (D : ℝ) := by
  classical
  let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
  let hρ := posSemidef_self_mul_conjTranspose C
  have htr : (C * Cᴴ).trace = 1 :=
    trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one Γ hΓ
  have hr : (C * Cᴴ).rank ≤ D := by
    rw [rank_self_mul_conjTranspose]
    exact schmidtRank_le_of_zero_perpendicular_shrinking K Γ φ hΓ hφrank hfix hperp hrank ha
  exact (vonNeumannEntropy_le_log_rank hρ htr).trans
    (Real.log_le_log (by exact_mod_cast hρ.rank_pos_of_trace_one htr)
      (by exact_mod_cast hr : ((C * Cᴴ).rank : ℝ) ≤ D))

/-- The entropy estimate for rank bounds at least two. The product overlap in
this intermediate statement is the actual overlap, rather than a lower bound. -/
private theorem entropy_le_of_actual_product_overlap
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ φ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1) (hφ : ‖φ‖ = 1)
    (hφrank : schmidtRank (WithLp.ofLp φ) ≤ 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    {D : ℕ} (hD : 2 ≤ D) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ)
    (hrank : Matrix.operatorSchmidtRank K ≤ D)
    (ha : ⟪Γ, φ⟫_ℂ ≠ 0) :
    let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
    vonNeumannEntropy (C * Cᴴ) (posSemidef_self_mul_conjTranspose C).isHermitian ≤
      12 * (1 + Real.log (‖⟪Γ, φ⟫_ℂ‖⁻¹) / (-Real.log δ)) * Real.log (D : ℝ) := by
  classical
  let μ : ℝ := ‖⟪Γ, φ⟫_ℂ‖
  have hμ0 : 0 < μ := norm_pos_iff.mpr ha
  have hμ1 : μ ≤ 1 := by simpa only [hΓ, hφ, mul_one] using norm_inner_le_norm Γ φ
  let A : ℝ := (1 - μ ^ 2) / μ ^ 2
  have hA : 0 ≤ A := div_nonneg (by nlinarith) (sq_nonneg μ)
  have hAeq : 1 + A = 1 / μ ^ 2 := by
    dsimp only [A]
    field_simp [hμ0.ne']
    ring
  have hlogA : Real.log (1 + A) = 2 * Real.log μ⁻¹ := by
    rw [hAeq, one_div, Real.log_inv, Real.log_pow, Real.log_inv]
    ring
  let q := Real.log μ⁻¹ / (-Real.log δ)
  have hq : 0 ≤ q := div_nonneg
    (Real.log_nonneg ((one_le_inv₀ hμ0).2 hμ1))
    (neg_pos.mpr (Real.log_neg hδ0 hδ1)).le
  let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
  let hρ := posSemidef_self_mul_conjTranspose C
  let p := hρ.isHermitian.eigenvalues₀
  have hp (b : Fin (Fintype.card m)) : 0 ≤ p b := by
    simpa only [p, IsHermitian.descEigenvalue, dite_eq_left b.isLt] using
      hρ.descEigenvalue_nonneg b.val
  have htr : (C * Cᴴ).trace = 1 :=
    trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one Γ hΓ
  have hsum : ∑ b, p b = 1 := by
    simpa [htr] using hρ.isHermitian.sum_eigenvalues₀_filter_le 0
  have htail (j : ℕ) :
      (∑ b ∈ Finset.univ.filter (fun b : Fin (Fintype.card m) ↦ D ^ j ≤ b.val), p b) ≤
        min 1 (A * δ ^ j) :=
    sum_eigenvalues_tail_of_operatorSchmidtRank_of_product_overlap
      K Γ φ hΓ hφ hφrank hfix hδ0.le hperp hrank ha j
  have hcover : Fintype.card m ≤ D ^ Fintype.card m :=
    ((@Nat.lt_two_pow_self (Fintype.card m)).le).trans
      (Nat.pow_le_pow_left (by omega : 2 ≤ D) _)
  have hraw := Entropy.probabilityEntropy_le_of_rankTailBounds
    (M := Fintype.card m) p (fun i ↦ D ^ i) (fun i ↦ min 1 (A * δ ^ i)) hp hsum
    (by simp) (fun i _ ↦ pow_le_pow_right' (by omega) (Nat.le_succ i))
    hcover (fun i _ ↦ htail i)
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hratio (i : ℕ) :
      Real.log (((D ^ (i + 1) : ℕ) : ℝ) / ((D ^ i : ℕ) : ℝ)) =
        Real.log (D : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, pow_succ, mul_div_cancel_left₀ _
      (pow_ne_zero _ hDreal.ne')]
  simp_rw [hratio] at hraw
  rw [← Finset.sum_mul] at hraw
  simp only [pow_zero, Nat.cast_one, Real.log_one, zero_add] at hraw
  have hmass := Real.sum_min_one_mul_pow_le A δ hA hδ0 hδ1 (Fintype.card m)
  rw [hlogA] at hmass
  have hmass' : (∑ i ∈ Finset.range (Fintype.card m), min 1 (A * δ ^ i)) ≤ 2 + 6 * q := by
    convert hmass using 1
    dsimp only [q]
    ring
  have hlog2 : Real.log 2 ≤ Real.log (D : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hD)
  have hlogD : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ D))
  have hlog20 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hcost := mul_le_mul_of_nonneg_right hmass' (add_nonneg hlog20 hlogD)
  have hcomp := mul_le_mul_of_nonneg_right hlog2 (by positivity : 0 ≤ 3 + 6 * q)
  change vonNeumannEntropy (C * Cᴴ) hρ.isHermitian ≤ 12 * (1 + q) * Real.log (D : ℝ)
  rw [vonNeumannEntropy_eq_probabilityEntropy_eigenvalues₀]
  change Entropy.probabilityEntropy p ≤ _
  have hrest : 0 ≤ 7 * Real.log (D : ℝ) := by positivity
  nlinarith only [hraw, hcost, hcomp, hrest]

/-- A corrected general invariant-line entropy bound, with an explicit additive
logarithmic rank cost. A unit rank-one vector is precisely a unit product vector.
The zero-shrinking endpoint is stated separately above. For rank one the entropy
is zero; rank zero is ruled out by the fixed unit vector.

Source: AKLV, arXiv:1301.1162v1, `lem:S`, lines 339–348; this is the corrected
estimate described in the module's paper-gap record, not the printed formula. -/
theorem vonNeumannEntropy_reduced_le_of_operatorSchmidtRank_of_product_overlap
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ φ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1) (hφ : ‖φ‖ = 1)
    (hφrank : schmidtRank (WithLp.ofLp φ) ≤ 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    {D : ℕ} {δ μ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hμ : 0 < μ)
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ)
    (hrank : Matrix.operatorSchmidtRank K ≤ D)
    (hoverlap : μ ≤ ‖⟪Γ, φ⟫_ℂ‖) :
    let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
    vonNeumannEntropy (C * Cᴴ) (posSemidef_self_mul_conjTranspose C).isHermitian ≤
      12 * (1 + Real.log μ⁻¹ / (-Real.log δ)) * Real.log (D : ℝ) := by
  classical
  have hane : ⟪Γ, φ⟫_ℂ ≠ 0 := norm_pos_iff.mp (hμ.trans_le hoverlap)
  have hKne : K ≠ 0 := by
    intro hz
    have hzero : Γ = 0 := by simpa only [hz, map_zero, LinearMap.zero_apply] using hfix.symm
    simp [hzero] at hΓ
  have hD : 1 ≤ D := Nat.succ_le_of_lt ((operatorSchmidtRank_pos_of_ne_zero K hKne).trans_le hrank)
  have hlogD : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg (by exact_mod_cast hD)
  by_cases hD2 : 2 ≤ D
  · refine (entropy_le_of_actual_product_overlap K Γ φ hΓ hφ hφrank hfix
      hD2 hδ0 hδ1 hperp hrank hane).trans ?_
    apply mul_le_mul_of_nonneg_right _ hlogD
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 12)
    refine add_le_add le_rfl ?_
    apply div_le_div_of_nonneg_right _ (neg_pos.mpr (Real.log_neg hδ0 hδ1)).le
    rw [Real.log_inv, Real.log_inv]
    exact neg_le_neg (Real.log_le_log hμ hoverlap)
  · obtain rfl : D = 1 := by omega
    have hC := schmidtRank_le_one_of_operatorSchmidtRank_le_one K Γ hΓ hfix hperp hrank hδ1
    have hzero := vonNeumannEntropy_eq_zero_of_rank_le_one
      (posSemidef_self_mul_conjTranspose (schmidtCoeffMatrix (WithLp.ofLp Γ)))
      (trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one Γ hΓ)
      (by rw [rank_self_mul_conjTranspose]; exact hC)
    simpa only [Nat.cast_one, Real.log_one, mul_zero, hzero] using (le_refl (0 : ℝ))

end Matrix

end AGSPGeneralEntropy
