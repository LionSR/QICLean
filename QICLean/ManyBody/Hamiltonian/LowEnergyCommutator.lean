/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyBasis.OffDiagonal
import QICLean.ManyBody.Hamiltonian.GaussianFilterLocality
import QICLean.ManyBody.Hamiltonian.GaussianFilterMetric
import QICLean.ManyBody.Hamiltonian.GaussianFilterTruncation

/-!
# Low-energy commutators of filtered terms

For a Hermitian `H` with every eigenvalue equal to `E₀` or at least `E₀ + ΔE`, let `P` project
onto the ground space. Hastings, arXiv:cond-mat/0508554v3, eqs. `lc` and `blecm`
(lines 1548–1601), bounds `‖[P W P, P B P]‖` by the locality of the Gaussian-filtered terms.

* `groundCompression H E₀ W`: the compression `P W P`; `groundCompression_gaussianFilteredTerm`:
  filtering leaves it unchanged.
* `norm_groundCompression_commutator_le`: the commutator of two compressions, up to
  `2‖W‖‖B‖e^{-q/2}`, is that of the filtered term with `B`.
* `norm_commutator_gaussianFilteredTerm_le_of_disjoint`,
  `norm_groundCompression_commutator_le_graphNeighborhood`: eqs. `lc` and `blecm` for an
  interaction on a finite graph.
* `norm_groundCompression_commutator_le_graphSeparation`,
  `norm_groundCompression_commutator_le_metricSeparation`,
  `norm_groundCompression_commutator_le_metricBalls`: exponential decay in the graph distance,
  without a growth assumption, and in a finite metric space.

Moved from TNLean (`e113e005`): `TNLean/Lattice/LowEnergyCommutator.lean` (ground and graph
sections) and `LowEnergyMetricCommutator.lean`. Changes: namespace `ManyBody`; terms given by
`Φ : Interaction X T` on `Config X`; the gap stated as `IsGapped`, with the Hermiticity of the
Hamiltonian derived from that of the terms.
-/

noncomputable section

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace ManyBody

section Ground

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The compression `P W P` of an operator `W` to the ground eigenspace of `H` at energy `E₀`,
as an operator on the Euclidean space, where `P` is the orthogonal projection onto that
eigenspace. This is `P_low W P_low` in Hastings, arXiv:cond-mat/0508554v3, lines 1562–1601. -/
noncomputable def groundCompression (H : Matrix n n ℂ) (E₀ : ℝ) (W : Matrix n n ℂ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  (groundSpace H E₀).starProjection * toEuclideanCLM (n := n) (𝕜 := ℂ) W *
    (groundSpace H E₀).starProjection

/-- The filtered operator and `W` have the same compression to the ground space:
`P W_tilde P = P W P`. Hastings, arXiv:cond-mat/0508554v3, line 1562. -/
theorem groundCompression_gaussianFilteredTerm {q ΔE : ℝ} (hq : 0 ≤ q) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (E₀ : ℝ) (W : Matrix n n ℂ) :
    groundCompression H E₀ (gaussianFilteredTerm q ΔE H W) = groundCompression H E₀ W := by
  set K := groundSpace H E₀
  ext1 x
  refine ext_inner_left ℂ fun y => ?_
  simp only [groundCompression, mul_apply_eq_comp]
  rw [← K.inner_starProjection_left_eq_right, ← K.inner_starProjection_left_eq_right]
  exact inner_gaussianFilteredTerm_ground hq hH W
    (mem_groundSpace_iff_mulVec.mp (K.starProjection_apply_mem y))
    (mem_groundSpace_iff_mulVec.mp (K.starProjection_apply_mem x))

/-- The filtered operator maps the ground space nearly into itself:
`‖(1 - P) W_tilde P‖ ≤ ‖W‖ e^{-q/2}`. Hastings, arXiv:cond-mat/0508554v3, line 1585,
following eq. `gs`. -/
theorem norm_one_sub_starProjection_mul_gaussianFilteredTerm_mul_le {q ΔE : ℝ} (hq : 0 ≤ q)
    (hΔE : 0 < ΔE) {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : IsGapped H E₀ ΔE) (W : Matrix n n ℂ) :
    ‖(1 - (groundSpace H E₀).starProjection) *
        toEuclideanCLM (n := n) (𝕜 := ℂ) (gaussianFilteredTerm q ΔE H W) *
        (groundSpace H E₀).starProjection‖ ≤ ‖W‖ * Real.exp (-q / 2) := by
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  set K := groundSpace H E₀
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  simp only [mul_apply_eq_comp, _root_.sub_apply, one_apply_eq_self]
  refine (norm_sub_starProjection_gaussianFilteredTerm_le hq hΔE hH hgapE W
    (K.starProjection_apply_mem x)).trans ?_
  gcongr
  exact K.norm_starProjection_apply_le x

/-- The adjoint statement: `‖P W_tilde (1 - P)‖ ≤ ‖W‖ e^{-q/2}`, since the adjoint of
`W_tilde` is the filtered version of `Wᴴ`. Hastings, arXiv:cond-mat/0508554v3, line 1586. -/
theorem norm_starProjection_mul_gaussianFilteredTerm_mul_one_sub_le {q ΔE : ℝ} (hq : 0 ≤ q)
    (hΔE : 0 < ΔE) {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : IsGapped H E₀ ΔE) (W : Matrix n n ℂ) :
    ‖(groundSpace H E₀).starProjection *
        toEuclideanCLM (n := n) (𝕜 := ℂ) (gaussianFilteredTerm q ΔE H W) *
        (1 - (groundSpace H E₀).starProjection)‖ ≤ ‖W‖ * Real.exp (-q / 2) := by
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  set P := (groundSpace H E₀).starProjection
  have hP : star P = P := (isSelfAdjoint_starProjection _).star_eq
  have hstar : star (toEuclideanCLM (n := n) (𝕜 := ℂ) (gaussianFilteredTerm q ΔE H W)) =
      toEuclideanCLM (n := n) (𝕜 := ℂ) (gaussianFilteredTerm q ΔE H Wᴴ) := by
    rw [← map_star, star_eq_conjTranspose]
    exact congrArg _ (gaussianIntertwiner_conjTranspose _ hH hH W)
  have h := norm_one_sub_starProjection_mul_gaussianFilteredTerm_mul_le hq hΔE hH hgap Wᴴ
  rw [l2_opNorm_conjTranspose, ← hstar] at h
  rw [← norm_star]
  simpa only [star_mul, star_sub, star_one, hP, mul_assoc] using h

/-- **The low-energy commutator, eq. `blecm`.** Let every eigenvalue of `H` equal `E₀` or be at
least `E₀ + ΔE`, with `ΔE > 0` and `q ≥ 0`. For all operators `W` and `B`, the compressions to
the ground space satisfy `‖[P W P, P B P]‖ ≤ ‖[W_tilde, B]‖ + 2 ‖W‖ ‖B‖ e^{-q/2}`.
Hastings, arXiv:cond-mat/0508554v3, lines 1562–1593, with `W = M_i` and `B = M_j`: the
compression of `W` equals that of `W_tilde`, and the triangle inequality after line 1566
together with eq. `gs` bounds the difference. -/
theorem norm_groundCompression_commutator_le {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : IsGapped H E₀ ΔE) (W B : Matrix n n ℂ) :
    ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ ≤
      ‖gaussianFilteredTerm q ΔE H W * B - B * gaussianFilteredTerm q ΔE H W‖ +
        2 * ‖W‖ * ‖B‖ * Real.exp (-q / 2) := by
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  have hlow := norm_one_sub_starProjection_mul_gaussianFilteredTerm_mul_le hq hΔE hH hgap W
  have hhigh := norm_starProjection_mul_gaussianFilteredTerm_mul_one_sub_le hq hΔE hH hgap W
  rw [← groundCompression_gaussianFilteredTerm (ΔE := ΔE) hq hH E₀ W]
  set P := (groundSpace H E₀).starProjection
  set A := toEuclideanCLM (n := n) (𝕜 := ℂ) (gaussianFilteredTerm q ΔE H W)
  set B' := toEuclideanCLM (n := n) (𝕜 := ℂ) B
  have hPP : P * P = P := (groundSpace H E₀).isIdempotentElem_starProjection.eq
  have hP : ‖P‖ ≤ 1 := (groundSpace H E₀).starProjection_norm_le
  have hB : ‖B'‖ = ‖B‖ := l2_opNorm_toEuclideanCLM B
  have hWe : 0 ≤ ‖W‖ * Real.exp (-q / 2) := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hAB : ‖A * B' - B' * A‖ =
      ‖gaussianFilteredTerm q ΔE H W * B - B * gaussianFilteredTerm q ΔE H W‖ := by
    rw [← l2_opNorm_toEuclideanCLM, map_sub, map_mul, map_mul]
  have hsplit : P * A * P * (P * B' * P) - P * B' * P * (P * A * P) =
      P * (A * B' - B' * A) * P - P * A * (1 - P) * (B' * P) +
        P * B' * ((1 - P) * A * P) := by
    have h1 : P * A * P * (P * B' * P) = P * A * (P * P) * B' * P := by simp only [mul_assoc]
    have h2 : P * B' * P * (P * A * P) = P * B' * (P * P) * A * P := by simp only [mul_assoc]
    rw [h1, h2, hPP]
    noncomm_ring
  have hC : ‖P * (A * B' - B' * A) * P‖ ≤ ‖A * B' - B' * A‖ := by
    calc ‖P * (A * B' - B' * A) * P‖ ≤ ‖P‖ * ‖A * B' - B' * A‖ * ‖P‖ := norm_mul₃_le
      _ ≤ 1 * ‖A * B' - B' * A‖ * 1 := by gcongr
      _ = _ := by ring
  have hD : ‖P * A * (1 - P) * (B' * P)‖ ≤ ‖W‖ * Real.exp (-q / 2) * ‖B‖ := by
    calc ‖P * A * (1 - P) * (B' * P)‖ ≤ ‖P * A * (1 - P)‖ * (‖B'‖ * ‖P‖) :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖W‖ * Real.exp (-q / 2) * (‖B‖ * 1) := by
          rw [hB]
          exact mul_le_mul hhigh (mul_le_mul_of_nonneg_left hP (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWe
      _ = _ := by rw [mul_one]
  have hE : ‖P * B' * ((1 - P) * A * P)‖ ≤ ‖W‖ * Real.exp (-q / 2) * ‖B‖ := by
    calc ‖P * B' * ((1 - P) * A * P)‖ ≤ ‖P‖ * ‖B'‖ * ‖(1 - P) * A * P‖ := norm_mul₃_le
      _ ≤ 1 * ‖B‖ * (‖W‖ * Real.exp (-q / 2)) := by
          rw [hB]
          exact mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg _)) hlow (norm_nonneg _)
            (mul_nonneg zero_le_one (norm_nonneg _))
      _ = _ := by ring
  simp only [groundCompression]
  rw [hsplit, ← hAB]
  calc _ ≤ ‖P * (A * B' - B' * A) * P - P * A * (1 - P) * (B' * P)‖ +
        ‖P * B' * ((1 - P) * A * P)‖ := norm_add_le _ _
    _ ≤ ‖P * (A * B' - B' * A) * P‖ + ‖P * A * (1 - P) * (B' * P)‖ +
        ‖P * B' * ((1 - P) * A * P)‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith

end Ground

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]
  (G : SimpleGraph V) {T : κ → Finset V}
  (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)

include hHerm hDiam hCard hBudget

/-- **The commutator of a filtered term with a separated operator, eq. `lc`.** Let `W` act on
`S`, and let `B` act on a set `Y` disjoint from the set of sites within graph distance `l` of
`S`. Then `‖[W_tilde, B]‖` is at most `2 ‖B‖` times the bound of
`norm_gaussianFilteredTerm_sub_regionExpectation_le_graphNeighborhood`, for every `τ ≥ 0`: the
partial trace of `W_tilde` onto that neighbourhood commutes with `B`. Hastings,
arXiv:cond-mat/0508554v3, eq. `lc` (lines 1548–1561), with the localization term in place of
`N_M g(c₁ l, l)`. -/
theorem norm_commutator_gaussianFilteredTerm_le_of_disjoint (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (S : Finset V) {W B : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (l : ℕ) (Y : Finset V)
    (hY : Disjoint (S.biUnion fun x => graphBall G x l) Y)
    (hB : B ∈ supportedOperators X Y) {τ : ℝ} (hT : 0 ≤ τ) :
    ‖gaussianFilteredTerm q ΔE Φ.hamiltonian W * B - B
        * gaussianFilteredTerm q ΔE Φ.hamiltonian W‖ ≤
      2 * ‖B‖ *
        ((2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖W‖ * Kg *
            (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
            Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * τ - l / 2) +
          2 * ‖W‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q))) := by
  set F := gaussianFilteredTerm q ΔE Φ.hamiltonian W
  set M := regionExpectation (S.biUnion fun x => graphBall G x l) F
  have hloc := norm_gaussianFilteredTerm_sub_regionExpectation_le_graphNeighborhood G Φ
    hHerm R hDiam vR hCard b₀ hBudget Kg kg hGrowth (ΔE := ΔE) hq S hW l hT
  have hcomm : Commute M B :=
    commute_of_mem_supportedOperators_of_disjoint
        (regionExpectation_mem_supportedOperators _ _) hB hY
  have hsplit : F * B - B * F = (F - M) * B - B * (F - M) := by
    rw [sub_mul, mul_sub, hcomm.eq]; abel
  rw [hsplit]
  calc _ ≤ ‖(F - M) * B‖ + ‖B * (F - M)‖ := norm_sub_le _ _
    _ ≤ ‖F - M‖ * ‖B‖ + ‖B‖ * ‖F - M‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖B‖ * ‖F - M‖ := by ring
    _ ≤ _ := by gcongr

/-- **The low-energy commutator of separated operators, eq. `blecm` on a finite graph.** Let
every eigenvalue of `H = ∑ₖ hₖ` equal `E₀` or be at least `E₀ + ΔE`, let `W` act on `S`, and
let `B` act on a set disjoint from the sites within graph distance `l` of `S`. Then the
compressions to the ground space satisfy
`‖[P W P, P B P]‖ ≤ 2 ‖B‖ (C' |S|² ‖W‖ e^{vT - l/2} + 2 ‖W‖ e^{-(TΔE)²/(2q)}) +
2 ‖W‖ ‖B‖ e^{-q/2}` for all `q ≥ 0` and `τ ≥ 0`, with the constants of
`norm_gaussianFilteredTerm_sub_regionExpectation_le_graphNeighborhood`. Hastings,
arXiv:cond-mat/0508554v3, eq. `blecm` (lines 1562–1601), with `W = M_i` and `B = M_j`; the
source takes `τ = c₁ l` and `q = c₁ l ΔE`. -/
theorem norm_groundCompression_commutator_le_graphNeighborhood (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    (S : Finset V) {W B : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (l : ℕ) (Y : Finset V)
    (hY : Disjoint (S.biUnion fun x => graphBall G x l) Y)
    (hB : B ∈ supportedOperators X Y) {τ : ℝ} (hT : 0 ≤ τ) :
    ‖groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀ B -
        groundCompression Φ.hamiltonian E₀ B * groundCompression Φ.hamiltonian E₀ W‖ ≤
      2 * ‖B‖ *
          ((2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖W‖ * Kg *
              (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
              Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * τ - l / 2) +
            2 * ‖W‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q))) +
        2 * ‖W‖ * ‖B‖ * Real.exp (-q / 2) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  exact
  (norm_groundCompression_commutator_le hq hΔE hH hgap W B).trans <| add_le_add_left
    (norm_commutator_gaussianFilteredTerm_le_of_disjoint G Φ hHerm R hDiam vR
      hCard b₀ hBudget Kg kg hGrowth hq S hW l Y hY hB hT) _

end Graph



end ManyBody

namespace ManyBody


variable {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] {X : V → Type*}
  [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

/-- Exponential low-energy commutator decay needs no growth assumption.
Hastings, arXiv:cond-mat/0508554v3, lines 1548–1601. -/
theorem norm_groundCompression_commutator_le_graphSeparation
    (G : SimpleGraph V) {T : κ → Finset V}
    (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, G.edist x y ≤ R)
    (vR : ℕ) (hvR : 1 ≤ vR) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    {Δ : ℝ} (hΔ : 0 < Δ) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ Δ)
    (S Y : Finset V) {W B : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S)
    (hB : B ∈ supportedOperators X Y) (m : ℕ)
    (hm : ∀ x ∈ S, ∀ y ∈ Y, (m : ℕ∞) ≤ G.edist x y) :
    let v := 4 * vR * |b₀| * Real.exp (2 * (R : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    ‖groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀ B -
        groundCompression Φ.hamiltonian E₀ B * groundCompression Φ.hamiltonian E₀ W‖ ≤
      (4 * (S.card : ℝ) + 4) * ‖W‖ * ‖B‖ * Real.exp (-(γ * m)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  intro v γ
  have hv : 0 < v := by dsimp [v]; positivity
  let τ : ℝ := m / (4 * v)
  let q := τ * Δ
  have hT : 0 ≤ τ := by dsimp [τ]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb := commutator_time_window_exp_bounds hv hΔ (Nat.cast_nonneg m)
  change Real.exp (v * τ - m / 2) ≤ Real.exp (-(γ * m)) ∧
    Real.exp (-(τ * Δ) ^ 2 / (2 * q)) ≤ Real.exp (-(γ * m)) ∧
    Real.exp (-q / 2) ≤ Real.exp (-(γ * m)) at hb
  obtain ⟨e1, e2, e3⟩ := hb
  have hloc (t : ℝ) (ht : t ∈ Set.Icc (-τ) τ) :
      ‖hermitianUnitaryPath Φ.hamiltonian t * W * hermitianUnitaryPath Φ.hamiltonian (-t) * B -
        B *
          (hermitianUnitaryPath Φ.hamiltonian t * W * hermitianUnitaryPath Φ.hamiltonian (-t))‖ ≤
      4 * (S.card : ℝ) * ‖W‖ * ‖B‖ * Real.exp (-(γ * m)) := by
    have hn := norm_heisenberg_commutator_le_graphDistance_finsets_numeric G Φ
      hHerm R hDiam vR hCard b₀ hBudget S hW Y
      hB 1 (by norm_num) m hm t
    refine hn.trans (mul_le_mul_of_nonneg_left (le_trans ?_ e1) (by positivity))
    apply Real.exp_le_exp.mpr
    have htT : |t| ≤ τ := abs_le.mpr ht
    have hvel : 0 ≤ 4 * vR * |b₀| * Real.exp (2 * (R : ℝ)) := by positivity
    have hx := mul_le_mul_of_nonneg_left htT hvel
    change 4 * vR * |b₀| * Real.exp (2 * 1 * R) * |t| - 1 * m ≤ v * τ - m / 2
    simp only [mul_one, one_mul]
    dsimp [v] at *
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hfilter := norm_commutator_gaussianFilteredTerm_le (ΔE := Δ) hq hH W B hT
    (show 0 ≤ 4 * (S.card : ℝ) * ‖W‖ * ‖B‖ * Real.exp (-(γ * m)) by positivity) hloc
  have hfiltered : ‖gaussianFilteredTerm q Δ Φ.hamiltonian W * B -
      B * gaussianFilteredTerm q Δ Φ.hamiltonian W‖ ≤
      (4 * (S.card : ℝ) + 2) * ‖W‖ * ‖B‖ * Real.exp (-(γ * m)) := by
    refine hfilter.trans ?_
    have := mul_le_mul_of_nonneg_left e2 (show 0 ≤ 2 * ‖W‖ * ‖B‖ by positivity)
    nlinarith
  refine (norm_groundCompression_commutator_le hq hΔ hH hgap W B).trans ?_
  have := mul_le_mul_of_nonneg_left e3 (show 0 ≤ 2 * ‖W‖ * ‖B‖ by positivity)
  nlinarith


/-- Physical support separation gives exponential low-energy decay in an arbitrary
finite metric space with the source's local range and cardinality bounds.
Hastings, arXiv:cond-mat/0508554v3, lines 1548–1601. -/
theorem norm_groundCompression_commutator_le_metricSeparation
    [PseudoMetricSpace V] {R J Δ : ℝ} (hR : 0 < R) (S : ℕ) (hJ : 0 ≤ J)
    (Φ : Interaction X (metricRangeBall R)) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (hNorm : ∀ i, ‖Φ.term i‖ ≤ J) (hCard : ∀ i : V, (metricRangeBall R i).card ≤ S)
    (hΔ : 0 < Δ) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ Δ)
    (T Y : Finset V) {W B : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X T)
    (hB : B ∈ supportedOperators X Y) (ℓ : ℝ)
    (hsep : ∀ x ∈ T, ∀ y ∈ Y, ℓ ≤ dist x y) :
    let vR := S + 1
    let v := 4 * vR * |(S : ℝ) * J| * Real.exp (2 * (2 : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    ‖groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀ B -
        groundCompression Φ.hamiltonian E₀ B * groundCompression Φ.hamiltonian E₀ W‖ ≤
      (4 * (T.card : ℝ) + 4) * ‖W‖ * ‖B‖ * Real.exp (-((γ / R) * ℓ)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  intro vR v γ
  have hdist (x : V) (hx : x ∈ T) (y : V) (hy : y ∈ Y) :
      (Nat.ceil (ℓ / R) : ℕ∞) ≤ (metricRangeGraph R).edist x y := by
    apply metricRangeGraph_edist_lower_ceil hR
    have heq : R * (ℓ / R) = ℓ := by field_simp
    rw [heq]
    exact hsep x hx y hy
  have hg := norm_groundCompression_commutator_le_graphSeparation
    (metricRangeGraph R) Φ hHerm 2
    (metricRangeBall_graph_diameter_le_two R) vR (by dsimp [vR]; omega)
    (fun i ↦ (hCard i).trans (by dsimp [vR]; omega)) ((S : ℝ) * J)
    (metricRangeBall_norm_budget_le hCard hJ Φ.term hNorm) hΔ hgap T Y hW hB
    (Nat.ceil (ℓ / R)) hdist
  change ‖groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀ B -
      groundCompression Φ.hamiltonian E₀ B * groundCompression Φ.hamiltonian E₀ W‖ ≤
      (4 * (T.card : ℝ) + 4) * ‖W‖ * ‖B‖ *
        Real.exp (-(γ * (Nat.ceil (ℓ / R) : ℝ))) at hg
  have hv : 0 < v := by dsimp [v]; positivity
  have hγ : 0 < γ := lt_min (by norm_num) (div_pos hΔ (by positivity))
  refine hg.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil (ℓ / R)) hγ.le
  convert neg_le_neg hh using 1
  ring


/-- The source's low-energy estimate for finite-radius observables, with the
second observable's support cardinality explicit and without graph growth.
Hastings, arXiv:cond-mat/0508554v3, lines 1548–1601. -/
theorem norm_groundCompression_commutator_le_metricBalls
    [PseudoMetricSpace V] {R J Δ : ℝ} (hR : 0 < R) (S : ℕ) (hJ : 0 ≤ J)
    (Φ : Interaction X (metricRangeBall R)) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (hNorm : ∀ i, ‖Φ.term i‖ ≤ J) (hCard : ∀ i : V, (metricRangeBall R i).card ≤ S)
    (hΔ : 0 < Δ) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ Δ)
    (ρ : ℝ) (i j : V) {W B : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X (metricRangeBall ρ i))
    (hB : B ∈ supportedOperators X (metricRangeBall ρ j)) :
    let vR := S + 1
    let v := 4 * vR * |(S : ℝ) * J| * Real.exp (2 * (2 : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    ‖groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀ B -
        groundCompression Φ.hamiltonian E₀ B * groundCompression Φ.hamiltonian E₀ W‖ ≤
      (4 * ((metricRangeBall ρ j).card : ℝ) + 4) * ‖W‖ * ‖B‖ *
        Real.exp (2 * (γ / R) * ρ) * Real.exp (-((γ / R) * dist i j)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  intro vR v γ
  have hW' : W ∈ supportedOperators X (metricRangeBall ρ i : Finset V) :=
    hW
  have hB' : B ∈ supportedOperators X (metricRangeBall ρ j : Finset V) :=
    hB
  have hsep (x : V) (hx : x ∈ metricRangeBall ρ j) (y : V)
      (hy : y ∈ metricRangeBall ρ i) : dist i j - 2 * ρ ≤ dist x y := by
    have hx' : dist x j ≤ ρ := by simpa only [dist_comm] using mem_metricRangeBall.mp hx
    have hy' : dist i y ≤ ρ := mem_metricRangeBall.mp hy
    have h1 := dist_triangle i y j
    have h2 := dist_triangle y x j
    rw [dist_comm y x] at h2
    linarith
  have hg := norm_groundCompression_commutator_le_metricSeparation hR S hJ Φ hHerm hNorm hCard
    hΔ hgap
    (metricRangeBall ρ j) (metricRangeBall ρ i)
    hB' hW' (dist i j - 2 * ρ) hsep
  change ‖groundCompression Φ.hamiltonian E₀ B * groundCompression Φ.hamiltonian E₀ W -
      groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀ B‖ ≤
      (4 * ((metricRangeBall ρ j).card : ℝ) + 4) * ‖B‖ * ‖W‖ *
        Real.exp (-((γ / R) * (dist i j - 2 * ρ))) at hg
  rw [norm_sub_rev] at hg
  refine hg.trans_eq ?_
  rw [show -((γ / R) * (dist i j - 2 * ρ)) =
    2 * (γ / R) * ρ + -((γ / R) * dist i j) by ring, Real.exp_add]
  ring

/-- The source's truncated operators satisfy the growth-free low-energy
commutator bound; the second Gaussian filter is independent of their first filter.
Hastings, arXiv:cond-mat/0508554v3, lines 1548–1601. -/
theorem norm_groundCompression_metric_truncated_commutator_le
    [PseudoMetricSpace V] {R J Δ : ℝ} (hR : 0 < R) (S : ℕ) (hJ : 0 ≤ J)
    (Φ : Interaction X (metricRangeBall R)) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (hNorm : ∀ i, ‖Φ.term i‖ ≤ J) (hCard : ∀ i : V, (metricRangeBall R i).card ≤ S)
    (hΔ : 0 < Δ) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ Δ)
    (q ρ : ℝ) (hρ : R ≤ ρ) (i j : V) :
    let vR := S + 1
    let v := 4 * vR * |(S : ℝ) * J| * Real.exp (2 * (2 : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    let Mi := gaussianFilteredTerm q Δ (∑ k ∈ metricRangeBall (ρ - R) i, Φ.term k) (Φ.term i)
    let Mj := gaussianFilteredTerm q Δ (∑ k ∈ metricRangeBall (ρ - R) j, Φ.term k) (Φ.term j)
    ‖groundCompression Φ.hamiltonian E₀ Mi * groundCompression Φ.hamiltonian E₀ Mj -
        groundCompression Φ.hamiltonian E₀ Mj * groundCompression Φ.hamiltonian E₀ Mi‖ ≤
      (4 * ((metricRangeBall ρ j).card : ℝ) + 4) * J ^ 2 *
        Real.exp (2 * (γ / R) * ρ) * Real.exp (-((γ / R) * dist i j)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  intro vR v γ Mi Mj
  obtain ⟨hMi, -, hnMi⟩ := metric_truncated_filter_properties hρ Φ hHerm hNorm q Δ i
  obtain ⟨hMj, -, hnMj⟩ := metric_truncated_filter_properties hρ Φ hHerm hNorm q Δ j
  have hg := norm_groundCompression_commutator_le_metricBalls hR S hJ Φ hHerm
    hNorm hCard hΔ hgap ρ i j hMi hMj
  refine hg.trans ?_
  calc (4 * ((metricRangeBall ρ j).card : ℝ) + 4) * ‖Mi‖ * ‖Mj‖ *
      Real.exp (2 * (γ / R) * ρ) * Real.exp (-((γ / R) * dist i j))
      ≤ (4 * ((metricRangeBall ρ j).card : ℝ) + 4) * J * J *
        Real.exp (2 * (γ / R) * ρ) * Real.exp (-((γ / R) * dist i j)) := by gcongr
    _ = _ := by ring

end ManyBody
