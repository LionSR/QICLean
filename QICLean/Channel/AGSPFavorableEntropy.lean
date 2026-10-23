/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Entropy
import QICLean.Analysis.ProbabilityEntropyGeometricTails
import QICLean.Channel.AGSPGeometricTails

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

## References

AKLV, arXiv:1301.1162v1, Definition 2.1 (`def:AGSP`), Corollary 2.4
(`col:half`), lines 296–361, and the rank-tail entropy argument, lines 1059–1075.
This is a quantitative auxiliary for the invariant-line setting.
The unrestricted printed entropy formula is discussed in the source note:
https://github.com/LionSR/QICLean/blob/ff2f24570636412fc4dab308a45e171815424b71/docs/paper-gaps/aklv13_entropy_small_shrinking.tex
-/

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
