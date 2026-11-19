/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyBasis.Iteration
import QICLean.ManyBody.Dynamics.GraphGrowth
import QICLean.ManyBody.Hamiltonian.LowEnergyCommutator

/-!
# Summing the low-energy commutators

Hastings, arXiv:cond-mat/0508554v3, eq. `oibu` (lines 1689–1694), sums the decaying bound on the
commutators of ground-space compressions over the terms.

* `shellSumConst`, `sum_exp_neg_edist_le`: exponential sums over the shells of a graph of
  polynomial growth.
* `norm_groundCompression_commutator_le_exp(_edist)`: exponential decay of the low-energy
  commutators in the graph distance between anchors.
* `sum_norm_offDiagonalPartFamily_le_oibu(_levels)`: eq. `oibu`.
* `sqrtKernel`, `listKernelSum`, `graphDecayKernel`: the decay kernels of the recursive basis
  construction.

Moved from TNLean (`e113e005`): `TNLean/Lattice/LowEnergyCommutatorSum.lean` and
`LowEnergyDecayKernel.lean`. Changes as in `LowEnergyCommutator`.
-/

noncomputable section

open GaussianFilter Matrix LowEnergyBasis
open scoped Matrix.Norms.L2Operator InnerProductSpace Nat Topology

namespace ManyBody

section ShellSums

/-- **A power against an exponential at rate `γ`.** For `γ > 0` and `x ≥ 0`,
`(x + 1)^k e^{-γ x} ≤ k! (2/γ)^k e^{γ/2} e^{-(γ/2) x}`. -/
theorem add_one_pow_mul_exp_neg_le {γ : ℝ} (hγ : 0 < γ) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) ^ k * Real.exp (-(γ * x)) ≤
      k ! * (2 / γ) ^ k * Real.exp (γ / 2) * Real.exp (-(γ / 2 * x)) := by
  have hfac : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have h := Real.pow_div_factorial_le_exp (x := γ * (x + 1) / 2) (by positivity) k
  rw [div_le_iff₀ hfac] at h
  have hpow : (x + 1) ^ k = (2 / γ) ^ k * (γ * (x + 1) / 2) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc (x + 1) ^ k * Real.exp (-(γ * x))
      = (2 / γ) ^ k * (γ * (x + 1) / 2) ^ k * Real.exp (-(γ * x)) := by rw [hpow]
    _ ≤ (2 / γ) ^ k * (Real.exp (γ * (x + 1) / 2) * k !) * Real.exp (-(γ * x)) := by
        gcongr
    _ = k ! * (2 / γ) ^ k * Real.exp (γ / 2) * Real.exp (-(γ / 2 * x)) := by
        rw [show γ * (x + 1) / 2 = γ / 2 + γ / 2 * x by ring, Real.exp_add]
        have : Real.exp (γ / 2 * x) * Real.exp (-(γ * x)) = Real.exp (-(γ / 2 * x)) := by
          rw [← Real.exp_add]; ring_nf
        calc (2 / γ) ^ k * (Real.exp (γ / 2) * Real.exp (γ / 2 * x) * k !) *
              Real.exp (-(γ * x))
            = k ! * (2 / γ) ^ k * Real.exp (γ / 2) *
                (Real.exp (γ / 2 * x) * Real.exp (-(γ * x))) := by ring
          _ = _ := by rw [this]

/-- The constant `S_{γ,k} = k! (2/γ)^k e^{γ/2} / (1 - e^{-γ/2})` bounding
`∑_{d ≥ 0} (d + 1)^k e^{-γ d}`. -/
noncomputable def shellSumConst (γ : ℝ) (k : ℕ) : ℝ :=
  k ! * (2 / γ) ^ k * Real.exp (γ / 2) / (1 - Real.exp (-(γ / 2)))

theorem shellSumConst_nonneg {γ : ℝ} (hγ : 0 < γ) (k : ℕ) : 0 ≤ shellSumConst γ k := by
  have h1 : Real.exp (-(γ / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold shellSumConst
  have : 0 < 1 - Real.exp (-(γ / 2)) := by linarith
  positivity

/-- **Shell sum at rate `γ`.** For every finite set `τ` of natural numbers,
`∑_{d ∈ τ} (d + 1)^k e^{-γ d} ≤ S_{γ,k}`. -/
theorem sum_add_one_pow_mul_exp_neg_le {γ : ℝ} (hγ : 0 < γ) (k : ℕ) (τ : Finset ℕ) :
    ∑ d ∈ τ, ((d : ℝ) + 1) ^ k * Real.exp (-(γ * d)) ≤ shellSumConst γ k := by
  set r := Real.exp (-(γ / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set M : ℝ := k ! * (2 / γ) ^ k * Real.exp (γ / 2) with hM
  have hM0 : 0 ≤ M := by positivity
  have hterm (d : ℕ) : ((d : ℝ) + 1) ^ k * Real.exp (-(γ * d)) ≤ M * r ^ d := by
    have hrd : r ^ d = Real.exp (-(γ / 2 * d)) := by
      rw [hr, ← Real.exp_nat_mul]; ring_nf
    rw [hrd]
    exact add_one_pow_mul_exp_neg_le hγ k (Nat.cast_nonneg d)
  obtain ⟨m, hm⟩ : ∃ m, τ ⊆ Finset.range m :=
    ⟨τ.sup id + 1, fun d hd => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.le_sup (f := id) hd))⟩
  calc _ ≤ ∑ d ∈ τ, M * r ^ d := Finset.sum_le_sum fun d _ => hterm d
    _ ≤ ∑ d ∈ Finset.range m, M * r ^ d :=
      Finset.sum_le_sum_of_subset_of_nonneg hm fun d _ _ => by positivity
    _ = M * ∑ d ∈ Finset.range m, r ^ d := (Finset.mul_sum _ _ _).symm
    _ ≤ M * (1 / (1 - r)) := by
        gcongr
        have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hr0 hr1
        rw [pow_zero] at h
        rw [Finset.range_eq_Ico]
        exact h
    _ = shellSumConst γ k := by rw [shellSumConst, hM, hr]; ring

/-- **Exponential decay summed over the sites.** If the sphere of radius `d` about `x` has at
most `K_g (d + 1)^k` sites, then `∑_y e^{-γ d(x, y)}` over the sites at finite distance is at
most `K_g S_{γ,k}`. -/
theorem sum_exp_neg_edist_le {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V) (Kg : ℝ)
    (kg : ℕ) (hGrowth : ∀ d : ℕ,
      ((Finset.univ.filter fun y => G.edist x y = d).card : ℝ) ≤ Kg * ((d : ℝ) + 1) ^ kg)
    {γ : ℝ} (hγ : 0 < γ) :
    ∑ y ∈ Finset.univ.filter (fun y => G.edist x y ≠ ⊤),
      Real.exp (-(γ * ((G.edist x y).toNat : ℝ))) ≤ Kg * shellSumConst γ kg := by
  classical
  have hKg : 0 ≤ Kg := by
    have := hGrowth 0
    simp only [CharP.cast_eq_zero, zero_add, one_pow, mul_one] at this
    exact (Nat.cast_nonneg _).trans this
  set S := Finset.univ.filter fun y => G.edist x y ≠ ⊤
  set D : V → ℕ := fun y => (G.edist x y).toNat
  have hfib : ∀ d ∈ S.image D, ((S.filter fun y => D y = d).card : ℝ) ≤
      Kg * ((d : ℝ) + 1) ^ kg := by
    intro d _
    refine le_trans ?_ (hGrowth d)
    exact_mod_cast Finset.card_le_card fun y hy => by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [← hy.2]
      exact (ENat.natCast_toNat hy.1).symm
  calc ∑ y ∈ S, Real.exp (-(γ * (D y : ℝ)))
      = ∑ d ∈ S.image D, ∑ y ∈ S.filter (fun y => D y = d), Real.exp (-(γ * (D y : ℝ))) :=
        (Finset.sum_fiberwise_of_maps_to (fun y hy => Finset.mem_image_of_mem D hy) _).symm
    _ = ∑ d ∈ S.image D, ((S.filter fun y => D y = d).card : ℝ) * Real.exp (-(γ * d)) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.mp hy).2],
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ d ∈ S.image D, Kg * ((d : ℝ) + 1) ^ kg * Real.exp (-(γ * d)) :=
        Finset.sum_le_sum fun d hd =>
          mul_le_mul_of_nonneg_right (hfib d hd) (Real.exp_pos _).le
    _ = Kg * ∑ d ∈ S.image D, ((d : ℝ) + 1) ^ kg * Real.exp (-(γ * d)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => by ring
    _ ≤ Kg * shellSumConst γ kg :=
        mul_le_mul_of_nonneg_left (sum_add_one_pow_mul_exp_neg_le hγ kg _) hKg

end ShellSums

section Compression

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The compression of an operator to the ground space has norm at most that of the operator. -/
theorem norm_groundCompression_le (H : Matrix n n ℂ) (E₀ : ℝ) (W : Matrix n n ℂ) :
    ‖groundCompression H E₀ W‖ ≤ ‖W‖ := by
  set P := (groundSpace H E₀).starProjection
  have hP : ‖P‖ ≤ 1 := (groundSpace H E₀).starProjection_norm_le
  calc ‖groundCompression H E₀ W‖ ≤ ‖P‖ * ‖toEuclideanCLM (n := n) (𝕜 := ℂ) W‖ * ‖P‖ := by
        unfold groundCompression
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * ‖W‖ * 1 := by
        rw [l2_opNorm_toEuclideanCLM]
        gcongr
    _ = ‖W‖ := by ring

/-- The commutator of two compressions has norm at most `2 ‖W‖ ‖B‖`. -/
theorem norm_groundCompression_commutator_le_two_mul (H : Matrix n n ℂ) (E₀ : ℝ)
    (W B : Matrix n n ℂ) :
    ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ ≤ 2 * ‖W‖ * ‖B‖ := by
  have hW := norm_groundCompression_le H E₀ W
  have hB := norm_groundCompression_le H E₀ B
  calc _ ≤ ‖groundCompression H E₀ W * groundCompression H E₀ B‖ +
        ‖groundCompression H E₀ B * groundCompression H E₀ W‖ := norm_sub_le _ _
    _ ≤ ‖W‖ * ‖B‖ + ‖B‖ * ‖W‖ := by
        gcongr
        · exact (norm_mul_le _ _).trans (mul_le_mul hW hB (norm_nonneg _) (norm_nonneg _))
        · exact (norm_mul_le _ _).trans (mul_le_mul hB hW (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖W‖ * ‖B‖ := by ring

/-- The compression of a Hermitian matrix to the ground space is self-adjoint. -/
theorem isSelfAdjoint_groundCompression (H : Matrix n n ℂ) (E₀ : ℝ) {W : Matrix n n ℂ}
    (hW : W.IsHermitian) : IsSelfAdjoint (groundCompression H E₀ W) := by
  have hT : IsSelfAdjoint (toEuclideanCLM (n := n) (𝕜 := ℂ) W) :=
    (hW.isSelfAdjoint).map toEuclideanCLM
  unfold groundCompression
  exact hT.conjugate_self (isSelfAdjoint_starProjection _)

/-- A compression to the ground space maps every vector into the ground space, so in an
orthonormal basis `v` of the ground space it is determined by its matrix elements. -/
theorem groundCompression_apply_eq_sum {H : Matrix n n ℂ} {E₀ : ℝ} {m : ℕ}
    {v : Fin m → EuclideanSpace ℂ n}
    (hspan : ∀ u ∈ groundSpace H E₀, u = ∑ c, ⟪v c, u⟫_ℂ • v c) (W : Matrix n n ℂ)
    (x : EuclideanSpace ℂ n) :
    groundCompression H E₀ W x = ∑ c, ⟪v c, groundCompression H E₀ W x⟫_ℂ • v c :=
  hspan _ ((groundSpace H E₀).starProjection_apply_mem _)

end Compression

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]
  (G : SimpleGraph V) {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
  (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)

/-- The Lieb–Robinson velocity `v = 2 v_R |b₀| e^{2R} + 1` of the terms. -/
noncomputable def lrVelocity (R vR : ℕ) (b₀ : ℝ) : ℝ :=
  2 * vR * |b₀| * Real.exp (2 * R) + 1

theorem one_le_lrVelocity (R vR : ℕ) (b₀ : ℝ) : 1 ≤ lrVelocity R vR b₀ := by
  unfold lrVelocity
  have : 0 ≤ 2 * (vR : ℝ) * |b₀| * Real.exp (2 * R) := by positivity
  linarith

/-- The decay rate `γ = min (1/4) (ΔE / (8 v))` of the low-energy commutators. -/
noncomputable def commutatorRate (R vR : ℕ) (b₀ ΔE : ℝ) : ℝ :=
  min (1 / 4) (ΔE / (8 * lrVelocity R vR b₀))

theorem commutatorRate_pos {ΔE : ℝ} (hΔE : 0 < ΔE) (R vR : ℕ) (b₀ : ℝ) :
    0 < commutatorRate R vR b₀ ΔE := by
  have := one_le_lrVelocity R vR b₀
  exact lt_min (by norm_num) (by positivity)

/-- The constant `2 (2 + 4 |b₀| e^{2R}) v_R² K_g C_k + 6` of the pairwise bound, with
`C_k = 2^k k! e^{1/2} / (1 - e^{-1/2})` the shell constant of the Lieb–Robinson estimate. -/
noncomputable def commutatorConst (R vR : ℕ) (b₀ Kg : ℝ) (kg : ℕ) : ℝ :=
  2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * (vR : ℝ) ^ 2 * Kg *
    (2 ^ kg * kg ! * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) + 6

theorem six_le_commutatorConst (R vR : ℕ) (b₀ : ℝ) {Kg : ℝ} (hKg : 0 ≤ Kg) (kg : ℕ) :
    6 ≤ commutatorConst R vR b₀ Kg kg := by
  have h1 : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have h2 : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by linarith
  unfold commutatorConst
  have : 0 ≤ 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * (vR : ℝ) ^ 2 * Kg *
      (2 ^ kg * kg ! * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) := by positivity
  linarith

omit [Fintype κ] in
include ha hDiam in
/-- If the anchors of two terms are at graph distance more than `2R + l`, then the second term
is disjoint from the sites within distance `l` of the first. -/
theorem disjoint_biUnion_graphBall_of_lt_edist (i j : κ) (l : ℕ)
    (hlt : ((2 * R + l : ℕ) : ℕ∞) < G.edist (a j) (a i)) :
    Disjoint ((T j).biUnion fun x => graphBall G x l) (T i) := by
  rw [Finset.disjoint_left]
  intro y hy hyi
  obtain ⟨x, hx, hxy⟩ := Finset.mem_biUnion.mp hy
  have hxy' := mem_graphBall.mp hxy
  have h1 := hDiam j (a j) (ha j) x hx
  have h2 := hDiam i y hyi (a i) (ha i)
  have htri : G.edist (a j) (a i) ≤ G.edist (a j) x + G.edist x y + G.edist y (a i) :=
    calc G.edist (a j) (a i) ≤ G.edist (a j) y + G.edist y (a i) := SimpleGraph.edist_triangle
      _ ≤ G.edist (a j) x + G.edist x y + G.edist y (a i) := by
          gcongr
          exact SimpleGraph.edist_triangle
  have : G.edist (a j) (a i) ≤ ((2 * R + l : ℕ) : ℕ∞) := by
    refine htri.trans ?_
    calc G.edist (a j) x + G.edist x y + G.edist y (a i) ≤ (R : ℕ∞) + l + R := by
          gcongr
      _ = ((2 * R + l : ℕ) : ℕ∞) := by push_cast; ring
  exact absurd hlt (not_lt.mpr this)

private theorem gaussian_error_prefactor (a w b n g c e : ℝ) :
    2 * b * (a * n ^ 2 * w * g * c * e + 2 * w * e) + 2 * w * b * e =
      (2 * a * n ^ 2 * g * c + 6) * w * b * e := by ring

include ha hHerm hDiam hCard hBudget

set_option maxHeartbeats 400000 in
-- The explicit Gaussian prefactor comparison expands several nested products and real casts.
set_option backward.isDefEq.respectTransparency false in
omit ha in
/-- The exponential low-energy commutator estimate for arbitrary separated local
observables. The observable support cardinality `vObs` is independent of the generator
cardinality `vR`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm`,
lines 1548–1601. -/
theorem norm_groundCompression_observables_commutator_le_exp
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    (S : Finset V) {W B : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (vObs : ℕ) (hSCard : S.card ≤ vObs)
    (l : ℕ) (Y : Finset V)
    (hY : Disjoint (S.biUnion fun x => graphBall G x l) Y)
    (hB : B ∈ supportedOperators X Y) :
    ‖groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀ B -
      groundCompression Φ.hamiltonian E₀ B * groundCompression Φ.hamiltonian E₀ W‖ ≤
        commutatorConst R vObs b₀ |Kg| kg * ‖W‖ * ‖B‖ *
          Real.exp (-(commutatorRate R vR b₀ ΔE * l)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  have hKg : 0 ≤ |Kg| := abs_nonneg Kg
  have hGrowthAbs : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ |Kg| * ((r : ℝ) + 1) ^ kg :=
    fun x r => (hGrowth x r).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  set v := lrVelocity R vR b₀ with hv
  have hv1 : 1 ≤ v := one_le_lrVelocity R vR b₀
  set γ := commutatorRate R vR b₀ ΔE with hγ
  set τ : ℝ := l / (4 * v) with hT
  have hT0 : 0 ≤ τ := by positivity
  set q : ℝ := τ * ΔE with hq
  have hq0 : 0 ≤ q := by positivity
  have hb := norm_groundCompression_commutator_le_graphNeighborhood G Φ hHerm R
    hDiam vR hCard b₀ hBudget |Kg| kg hGrowthAbs hq0 hΔE hgap S hW l Y hY hB hT0
  set A : ℝ := 2 + 4 * |b₀| * Real.exp (2 * R)
  set Ck : ℝ := 2 ^ kg * kg ! * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))
  have hA : 0 ≤ A := by positivity
  have hCk : 0 ≤ Ck := by
    have h1 : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by linarith
    positivity
  have hW0 := norm_nonneg W
  have hB0 := norm_nonneg B
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hbounds := commutator_time_window_exp_bounds
    (lt_of_lt_of_le zero_lt_one hv1) hΔE hl
  change Real.exp (v * τ - l / 2) ≤ Real.exp (-(γ * l)) ∧
    Real.exp (-(τ * ΔE) ^ 2 / (2 * q)) ≤ Real.exp (-(γ * l)) ∧
    Real.exp (-q / 2) ≤ Real.exp (-(γ * l)) at hbounds
  obtain ⟨e1, e2, e3⟩ := hbounds
  have hS : (S.card : ℝ) ^ 2 ≤ (vObs : ℝ) ^ 2 := by
    have : (S.card : ℝ) ≤ vObs := by exact_mod_cast hSCard
    gcongr
  set E := Real.exp (-(γ * l))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine hb.trans ?_
  calc 2 * ‖B‖ * (A * (S.card : ℝ) ^ 2 * ‖W‖ * |Kg| * Ck *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * τ - l / 2) +
        2 * ‖W‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q))) +
        2 * ‖W‖ * ‖B‖ * Real.exp (-q / 2)
      ≤ 2 * ‖B‖ * (A * (vObs : ℝ) ^ 2 * ‖W‖ * |Kg| * Ck * E + 2 * ‖W‖ * E) +
        2 * ‖W‖ * ‖B‖ * E := by
        have hcoef : A * (S.card : ℝ) ^ 2 * ‖W‖ * |Kg| * Ck ≤
            A * (vObs : ℝ) ^ 2 * ‖W‖ * |Kg| * Ck :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hA) hW0) hKg) hCk
        have hc1 : 0 ≤ A * (vObs : ℝ) ^ 2 * ‖W‖ * |Kg| * Ck := by positivity
        have ht1 := mul_le_mul hcoef e1 (Real.exp_pos _).le hc1
        have ht2 := mul_le_mul_of_nonneg_left e2 (by positivity : 0 ≤ 2 * ‖W‖)
        have ht3 := mul_le_mul_of_nonneg_left e3 (by positivity : 0 ≤ 2 * ‖W‖ * ‖B‖)
        exact add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (by positivity : 0 ≤ 2 * ‖B‖)) ht3
    _ = commutatorConst R vObs b₀ |Kg| kg * ‖W‖ * ‖B‖ * E := by
        unfold commutatorConst
        exact gaussian_error_prefactor A ‖W‖ ‖B‖ vObs |Kg| Ck E


set_option backward.isDefEq.respectTransparency false in
omit ha in
/-- Exponential decay between arbitrary local observables in the distance between
anchors. The velocity uses the Hamiltonian generator parameters `R,vR`; the observable
support parameters `Robs,vObs` enter only the prefactor and support-separation correction.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm`, lines 1548–1601,
with the truncated observables `M_i` allowed as the family `W`. -/
theorem norm_groundCompression_observables_commutator_le_exp_edist
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    {η : Type*} (Y : η → Finset V) (c : η → V) (hc : ∀ i, c i ∈ Y i)
    (W : η → Matrix (Config X) (Config X) ℂ)
    (hW : ∀ i, W i ∈ supportedOperators X (Y i : Finset V))
    (Robs : ℕ) (hYDiam : ∀ i, ∀ x ∈ Y i, ∀ y ∈ Y i, G.edist x y ≤ Robs)
    (vObs : ℕ) (hYCard : ∀ i, (Y i).card ≤ vObs) (i j : η) :
    ‖groundCompression Φ.hamiltonian E₀ (W j) * groundCompression Φ.hamiltonian E₀ (W i) -
      groundCompression Φ.hamiltonian E₀ (W i) * groundCompression Φ.hamiltonian E₀ (W j)‖ ≤
        commutatorConst R vObs b₀ |Kg| kg *
          Real.exp (commutatorRate R vR b₀ ΔE * (2 * Robs + 1)) * ‖W j‖ * ‖W i‖ *
          (if G.edist (c j) (c i) = ⊤ then 0 else
            Real.exp (-(commutatorRate R vR b₀ ΔE * ((G.edist (c j) (c i)).toNat : ℝ)))) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  let γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  have hC : 2 ≤ commutatorConst R vObs b₀ |Kg| kg :=
    (by norm_num : (2 : ℝ) ≤ 6).trans (six_le_commutatorConst R vObs b₀ (abs_nonneg Kg) kg)
  apply le_anchorDecay_of_separated_exp hγ hC (norm_nonneg _) (norm_nonneg _)
    Robs (G.edist (c j) (c i)) (norm_groundCompression_commutator_le_two_mul _ _ _ _)
  intro l hlt
  exact norm_groundCompression_observables_commutator_le_exp G Φ hHerm R
    hDiam vR hCard b₀ hBudget Kg kg hGrowth hΔE hgap (Y j) (hW j) vObs (hYCard j)
    l (Y i)
    (disjoint_biUnion_graphBall_of_lt_edist G (T := Y) c hc Robs hYDiam i j l hlt) (hW i)

omit ha in
include a in
/-- **Eq. `blecm` with an exponential rate.** Let every eigenvalue of `H = ∑ₖ hₖ` equal `E₀` or
be at least `E₀ + ΔE`, and let `X_i` be disjoint from the sites within graph distance `l` of
`X_j`. Then `‖[P h_j P, P h_i P]‖ ≤ C ‖h_j‖ ‖h_i‖ e^{-γ l}`, with `C = commutatorConst` and
`γ = commutatorRate`. The time window `τ = l / (4v)` and `q = τ ΔE` of the Gaussian filter are
chosen for the pair, which is allowed because the compression of a filtered term does not depend
on `q`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm` (lines 1562–1601). -/
theorem norm_groundCompression_commutator_le_exp (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE) (i j : κ) (l : ℕ)
    (hY : Disjoint ((T j).biUnion fun x => graphBall G x l) (T i)) :
    ‖groundCompression Φ.hamiltonian E₀ (Φ.term j) * groundCompression Φ.hamiltonian E₀ (Φ.term i) -
        groundCompression Φ.hamiltonian E₀ (Φ.term i) * groundCompression Φ.hamiltonian E₀
            (Φ.term j)‖ ≤
      commutatorConst R vR b₀ Kg kg * ‖Φ.term j‖ * ‖Φ.term i‖ *
        Real.exp (-(commutatorRate R vR b₀ ΔE * l)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  have hKg : 0 ≤ Kg := by
    have := hGrowth (a i) 0
    simp only [CharP.cast_eq_zero, zero_add, one_pow, mul_one] at this
    exact (Nat.cast_nonneg _).trans this
  simpa only [abs_of_nonneg hKg] using
    norm_groundCompression_observables_commutator_le_exp G Φ hHerm R hDiam vR
      hCard b₀ hBudget Kg kg hGrowth hΔE hgap (T j) (Φ.mem j) vR (hCard j) l (T i) hY
      (Φ.mem i)

/-- **Eq. `blecm` in the distance of the anchors.** If the anchors `a_j`, `a_i` are at finite
graph distance `D`, then `‖[P h_j P, P h_i P]‖ ≤ C e^{γ(2R+1)} ‖h_j‖ ‖h_i‖ e^{-γ D}`; at
infinite distance the commutator vanishes. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `blecm` (lines 1562–1601). -/
theorem norm_groundCompression_commutator_le_exp_edist (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE) (i j : κ) :
    ‖groundCompression Φ.hamiltonian E₀ (Φ.term j) * groundCompression Φ.hamiltonian E₀ (Φ.term i) -
        groundCompression Φ.hamiltonian E₀ (Φ.term i) * groundCompression Φ.hamiltonian E₀
            (Φ.term j)‖ ≤
      commutatorConst R vR b₀ Kg kg * Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) *
        ‖Φ.term j‖ * ‖Φ.term i‖ *
        (if G.edist (a j) (a i) = ⊤ then 0 else
          Real.exp (-(commutatorRate R vR b₀ ΔE * ((G.edist (a j) (a i)).toNat : ℝ)))) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  have hKg : 0 ≤ Kg := by
    have := hGrowth (a i) 0
    simp only [CharP.cast_eq_zero, zero_add, one_pow, mul_one] at this
    exact (Nat.cast_nonneg _).trans this
  simpa only [abs_of_nonneg hKg] using
    norm_groundCompression_observables_commutator_le_exp_edist G Φ hHerm R hDiam
      vR hCard b₀ hBudget Kg kg hGrowth hΔE hgap T a ha Φ.term Φ.mem R hDiam vR hCard i j

/-- **The sum of the low-energy commutators over all terms.** Let every eigenvalue of
`H = ∑ₖ hₖ` equal `E₀` or be at least `E₀ + ΔE`, and let the spheres of the graph grow at most
polynomially, `|{y : d(x, y) = r}| ≤ K_g (r + 1)^k`. Then for every term `j`,
`∑_i ‖[P h_j P, P h_i P]‖ ≤ C e^{γ(2R+1)} |b₀| K_g S_{γ,k} ‖h_j‖`, a bound independent of the
number of sites and of terms. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1689–1694: summing the decay of eq. `blecm` over all `i`. -/
theorem sum_norm_groundCompression_commutator_le (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE) (j : κ) :
    ∑ i, ‖groundCompression Φ.hamiltonian E₀ (Φ.term j) * groundCompression Φ.hamiltonian E₀
        (Φ.term i) -
        groundCompression Φ.hamiltonian E₀ (Φ.term i) * groundCompression Φ.hamiltonian E₀
            (Φ.term j)‖ ≤
      commutatorConst R vR b₀ Kg kg * Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) *
        ‖Φ.term j‖ * (|b₀| * (Kg * shellSumConst (commutatorRate R vR b₀ ΔE) kg)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  set γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  have hKg : 0 ≤ Kg := by
    have := hGrowth (a j) 0
    simp only [CharP.cast_eq_zero, zero_add, one_pow, mul_one] at this
    exact (Nat.cast_nonneg _).trans this
  set C := commutatorConst R vR b₀ Kg kg * Real.exp (γ * (2 * R + 1)) * ‖Φ.term j‖
  have hC : 0 ≤ C := by
    have := six_le_commutatorConst R vR b₀ hKg kg
    have : 0 ≤ commutatorConst R vR b₀ Kg kg := by linarith
    positivity
  set w : V → ℝ := fun x => if G.edist (a j) x = ⊤ then 0 else
    Real.exp (-(γ * ((G.edist (a j) x).toNat : ℝ)))
  have hw0 (x : V) : 0 ≤ w x := by
    simp only [w]; split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  -- Each term is at most `C ‖h_i‖ w(a_i)`.
  have hterm (i : κ) :
      ‖groundCompression Φ.hamiltonian E₀ (Φ.term j) * groundCompression Φ.hamiltonian E₀
          (Φ.term i) -
        groundCompression Φ.hamiltonian E₀ (Φ.term i) * groundCompression Φ.hamiltonian E₀
            (Φ.term j)‖ ≤
        C * (‖Φ.term i‖ * w (a i)) := by
    refine (norm_groundCompression_commutator_le_exp_edist G a ha Φ hHerm R hDiam vR
      hCard b₀ hBudget Kg kg hGrowth hΔE hgap i j).trans (le_of_eq ?_)
    simp only [C, w]
    ring
  -- Group the terms by their anchor and use the norm budget of each site.
  have hgroup : ∑ i, ‖Φ.term i‖ * w (a i) ≤ ∑ x, |b₀| * w x := by
    rw [← Finset.mul_sum]
    apply sum_weight_mul_comp_le_budget_mul_sum a (fun i ↦ ‖Φ.term i‖) |b₀| _ w hw0
    intro x
    exact (sum_weight_anchor_le_of_support_budget T a ha (fun i ↦ ‖Φ.term i‖)
      (fun i ↦ norm_nonneg _) b₀ hBudget x).trans (le_abs_self b₀)
  have hsites : ∑ x, w x ≤ Kg * shellSumConst γ kg := by
    have hsplit : ∑ x, w x = ∑ x ∈ Finset.univ.filter (fun x => G.edist (a j) x ≠ ⊤),
        Real.exp (-(γ * ((G.edist (a j) x).toNat : ℝ))) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [w]
      split_ifs <;> simp_all
    rw [hsplit]
    exact sum_exp_neg_edist_le G (a j) Kg kg (hGrowth (a j)) hγ
  calc _ ≤ ∑ i, C * (‖Φ.term i‖ * w (a i)) := Finset.sum_le_sum fun i _ => hterm i
    _ = C * ∑ i, ‖Φ.term i‖ * w (a i) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * ∑ x, |b₀| * w x := mul_le_mul_of_nonneg_left hgroup hC
    _ = C * (|b₀| * ∑ x, w x) := by rw [← Finset.mul_sum]
    _ ≤ C * (|b₀| * (Kg * shellSumConst γ kg)) := by
        gcongr
    _ = _ := by simp only [C]

/-- **Eq. `oibu`.** In an orthonormal eigenbasis `v` of the compression `P M_j P` of the filtered
term `M_j`, with eigenvalues pairwise at least `δ > 0` apart, the off-diagonal parts of the
compressions `P M_i P` of all filtered terms satisfy
`∑_i o(i) ≤ (n - 1) C e^{γ(2R+1)} |b₀| K_g S_{γ,k} ‖h_j‖ / δ`, independently of the number of
sites and terms. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`
(lines 1689–1694). -/
theorem sum_norm_offDiagonalPartFamily_le_oibu (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE) (j : κ) {m : ℕ}
    [NeZero m] {v : Fin m → EuclideanSpace ℂ (Config X)} (hv : Orthonormal ℂ v)
    {r : Fin m → ℝ}
    (hAv : ∀ c, groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm q ΔE Φ.hamiltonian
        (Φ.term j))
      (v c) = (r c : ℂ) • v c) {δ : ℝ} (hδ : 0 < δ) (hgap' : ∀ c c', c ≠ c' → δ ≤ |r c - r c'|) :
    ∑ i, ‖offDiagonalPartFamily v
        (groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm q ΔE Φ.hamiltonian (Φ.term i)))‖ ≤
      (m - 1 : ℕ) * (commutatorConst R vR b₀ Kg kg *
        Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) * ‖Φ.term j‖ *
          (|b₀| * (Kg * shellSumConst (commutatorRate R vR b₀ ΔE) kg)) / δ) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  simp only [groundCompression_gaussianFilteredTerm hq hH] at hAv ⊢
  refine (sum_norm_offDiagonalPartFamily_le Finset.univ
    (isSelfAdjoint_groundCompression _ E₀ (hHerm j)) _ hv hAv hδ hgap').trans ?_
  gcongr
  exact sum_norm_groundCompression_commutator_le G a ha Φ hHerm R hDiam vR hCard b₀
    hBudget Kg kg hGrowth hΔE hgap j

/-- **Eq. `oibu` for a degenerate ground space.** Let `v : Fin m → E` be an orthonormal basis of
the ground space, and record the source's iteration by labels `r ℓ` and the terms `j ℓ` whose
compressions `A ℓ = P h_{j ℓ} P` act diagonally on the classes of level `ℓ`, every pair of basis
vectors being separated below level `L` and every `j ℓ` being one of `j 0, …, j (L - 1)`. If all
terms have norm at most `J`, then the off-diagonal parts of the compressions of all filtered terms
satisfy `∑_i o(i) ≤ (m - 1) β_{L-1} ∑_{ℓ < L} C' ‖h_{j ℓ}‖`, where `β_{L-1} = levelBoundB` with
`K = 2 J²` and `K_B = 1`, and `C'` is the constant of `sum_norm_groundCompression_commutator_le`.
There is no factor counting the number of sites or terms; uniformity also requires uniform
control of the displayed spectral constants and the number of levels. The basis and separation
are hypotheses here. `LowEnergyBasisConstruction.lean` constructs a basis without them and
displays the corresponding commutator conditioning. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eq. `oibu` (lines 1689–1694) and lines 1695–1708. -/
theorem sum_norm_offDiagonalPartFamily_le_oibu_levels (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE) {J : ℝ}
    (hJ : ∀ k, ‖Φ.term k‖ ≤ J) {m : ℕ} [NeZero m] {v : Fin m → EuclideanSpace ℂ (Config X)}
    (hv : Orthonormal ℂ v)
    (hspan : ∀ u ∈ groundSpace Φ.hamiltonian E₀, u = ∑ c, ⟪v c, u⟫_ℂ • v c)
    {L : ℕ} (j : ℕ → κ) (hj : ∀ ℓ, ∃ ℓ' < L, j ℓ' = j ℓ) (r : ℕ → Fin m → ℝ)
    (hdiag : ∀ ℓ a, ∀ c ∈ labelClass r ℓ a, ∀ e ∈ labelClass r ℓ a,
      ⟪v c, groundCompression Φ.hamiltonian E₀ (Φ.term (j ℓ)) (v e)⟫_ℂ =
        if c = e then (r ℓ c : ℂ) else 0)
    (hsep : ∀ a b, a ≠ b → ∃ ℓ < L, r ℓ a ≠ r ℓ b) :
    ∑ i, ‖offDiagonalPartFamily v
        (groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm q ΔE Φ.hamiltonian (Φ.term i)))‖ ≤
      (m - 1 : ℕ) * levelBoundB m r (2 * J ^ 2) 1 (L - 1) *
        ∑ ℓ ∈ Finset.range L, commutatorConst R vR b₀ Kg kg *
          Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) * ‖Φ.term (j ℓ)‖ *
            (|b₀| * (Kg * shellSumConst (commutatorRate R vR b₀ ΔE) kg)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  set A : ℕ → _ := fun ℓ => groundCompression Φ.hamiltonian E₀ (Φ.term (j ℓ))
  set B : κ → _ := fun i => groundCompression Φ.hamiltonian E₀ (Φ.term i)
  set KB : κ → ℝ := fun i => ∑ ℓ ∈ Finset.range L, ‖A ℓ * B i - B i * A ℓ‖
  have hKA : ∀ ℓ ℓ', ‖A ℓ * A ℓ' - A ℓ' * A ℓ‖ ≤ 2 * J ^ 2 := fun ℓ ℓ' => by
    refine (norm_groundCompression_commutator_le_two_mul _ E₀ _ _).trans ?_
    have h1 := hJ (j ℓ)
    have h2 := hJ (j ℓ')
    nlinarith [norm_nonneg (Φ.term (j ℓ)), norm_nonneg (Φ.term (j ℓ'))]
  have hKBB : ∀ i ℓ, ‖A ℓ * B i - B i * A ℓ‖ ≤ KB i := fun i ℓ => by
    obtain ⟨ℓ', hℓ', hjj⟩ := hj ℓ
    have hA : A ℓ = A ℓ' := by simp only [A, hjj]
    rw [hA]
    exact Finset.single_le_sum (f := fun ℓ => ‖A ℓ * B i - B i * A ℓ‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hℓ')
  have hsum := sum_norm_offDiagonalPartFamily_le_levelBoundB A r hv
    (fun ℓ b => groundCompression_apply_eq_sum hspan _ _) hdiag (by positivity) hKA
    Finset.univ B (fun i b => groundCompression_apply_eq_sum hspan _ _) KB
    (fun i => Finset.sum_nonneg fun _ _ => norm_nonneg _) hKBB hsep
  refine hsum.trans ?_
  gcongr
  · exact mul_nonneg (Nat.cast_nonneg _)
      (levelBoundB_nonneg r (by positivity) zero_le_one _)
  · simp only [KB, A, B]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun ℓ _ => ?_
    exact sum_norm_groundCompression_commutator_le G a ha Φ hHerm R hDiam vR hCard b₀
      hBudget Kg kg hGrowth hΔE hgap (j ℓ)

end Graph



end ManyBody

namespace ManyBody


variable {V : Type*}

/-- Successive square roots of a decay kernel. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708, with the cross terms retained. -/
noncomputable def sqrtKernel (k : V → V → ℝ) : ℕ → V → V → ℝ
  | 0 => k
  | n + 1 => fun i j => Real.sqrt (sqrtKernel k n i j)

@[simp]
theorem sqrtKernel_zero (k : V → V → ℝ) (i j : V) : sqrtKernel k 0 i j = k i j := rfl

@[simp]
theorem sqrtKernel_succ (k : V → V → ℝ) (n : ℕ) (i j : V) :
    sqrtKernel k (n + 1) i j = Real.sqrt (sqrtKernel k n i j) := rfl

theorem sqrtKernel_nonneg {k : V → V → ℝ} (hk : ∀ i j, 0 ≤ k i j) :
    ∀ n i j, 0 ≤ sqrtKernel k n i j
  | 0, i, j => hk i j
  | _ + 1, _, _ => Real.sqrt_nonneg _

theorem sqrtKernel_le_one {k : V → V → ℝ} (hk : ∀ i j, k i j ≤ 1) :
    ∀ n i j, sqrtKernel k n i j ≤ 1
  | 0, i, j => hk i j
  | n + 1, i, j => Real.sqrt_le_one.mpr (sqrtKernel_le_one hk n i j)

theorem sqrtKernel_symm {k : V → V → ℝ} (hk : ∀ i j, k i j = k j i) :
    ∀ n i j, sqrtKernel k n i j = sqrtKernel k n j i
  | 0, i, j => hk i j
  | n + 1, i, j => congrArg Real.sqrt (sqrtKernel_symm hk n i j)

theorem sqrtKernel_succ_sq {k : V → V → ℝ} (hk : ∀ i j, 0 ≤ k i j) (n : ℕ) (i j : V) :
    sqrtKernel k (n + 1) i j ^ 2 = sqrtKernel k n i j :=
  Real.sq_sqrt (sqrtKernel_nonneg hk n i j)

theorem sqrtKernel_mono {k : V → V → ℝ} (hk0 : ∀ i j, 0 ≤ k i j)
    (hk1 : ∀ i j, k i j ≤ 1) (i j : V) : Monotone fun n => sqrtKernel k n i j := by
  apply monotone_nat_of_le_succ
  intro n
  rw [sqrtKernel_succ]
  apply Real.le_sqrt_of_sq_le
  have h0 := sqrtKernel_nonneg hk0 n i j
  have h1 := sqrtKernel_le_one hk1 n i j
  nlinarith

/-- The multiplicative triangle inequality persists under taking square roots. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem sqrtKernel_mul_le {k : V → V → ℝ} (hk0 : ∀ i j, 0 ≤ k i j)
    (hmul : ∀ i j l, k i j * k j l ≤ k i l) :
    ∀ n i j l, sqrtKernel k n i j * sqrtKernel k n j l ≤ sqrtKernel k n i l
  | 0, i, j, l => hmul i j l
  | n + 1, i, j, l => by
      rw [sqrtKernel_succ, sqrtKernel_succ, sqrtKernel_succ,
        ← Real.sqrt_mul (sqrtKernel_nonneg hk0 n i j)]
      exact Real.sqrt_le_sqrt (sqrtKernel_mul_le hk0 hmul n i j l)

/-- The sum of a kernel over a finite list of selected terms, allowing repeated selections
at different spectral splits. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1695–1708. -/
def listKernelSum (k : V → V → ℝ) (s : List V) (i : V) : ℝ := (s.map (k i)).sum

@[simp]
theorem listKernelSum_nil (k : V → V → ℝ) (i : V) : listKernelSum k [] i = 0 := rfl

@[simp]
theorem listKernelSum_cons (k : V → V → ℝ) (j : V) (s : List V) (i : V) :
    listKernelSum k (j :: s) i = k i j + listKernelSum k s i := rfl

@[simp]
theorem listKernelSum_append (k : V → V → ℝ) (s t : List V) (i : V) :
    listKernelSum k (s ++ t) i = listKernelSum k s i + listKernelSum k t i := by
  simp only [listKernelSum, List.map_append, List.sum_append]

theorem listKernelSum_nonneg {k : V → V → ℝ} (hk : ∀ i j, 0 ≤ k i j)
    (s : List V) (i : V) : 0 ≤ listKernelSum k s i := by
  induction s with
  | nil => exact le_rfl
  | cons j s hs => exact add_nonneg (hk i j) hs

/-- Exponential graph decay, set to zero between disconnected components. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm` and lines 1689–1708. -/
noncomputable def graphDecayKernel (G : SimpleGraph V) (γ : ℝ) (i j : V) : ℝ :=
  if G.edist i j = ⊤ then 0 else Real.exp (-(γ * ((G.edist i j).toNat : ℝ)))

theorem graphDecayKernel_nonneg (G : SimpleGraph V) (γ : ℝ) (i j : V) :
    0 ≤ graphDecayKernel G γ i j := by
  unfold graphDecayKernel
  split_ifs <;> positivity

theorem graphDecayKernel_le_one (G : SimpleGraph V) {γ : ℝ} (hγ : 0 ≤ γ) (i j : V) :
    graphDecayKernel G γ i j ≤ 1 := by
  unfold graphDecayKernel
  split_ifs
  · norm_num
  · exact Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hγ (Nat.cast_nonneg _)))

theorem graphDecayKernel_symm (G : SimpleGraph V) (γ : ℝ) (i j : V) :
    graphDecayKernel G γ i j = graphDecayKernel G γ j i := by
  simp only [graphDecayKernel, G.edist_comm (u := i) (v := j)]

/-- The graph triangle inequality in multiplicative form, including infinite distances.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem graphDecayKernel_mul_le (G : SimpleGraph V) {γ : ℝ} (hγ : 0 ≤ γ) (i j l : V) :
    graphDecayKernel G γ i j * graphDecayKernel G γ j l ≤ graphDecayKernel G γ i l := by
  classical
  by_cases hij : G.edist i j = ⊤
  · simpa only [graphDecayKernel, hij, ↓reduceIte, zero_mul] using
      graphDecayKernel_nonneg G γ i l
  by_cases hjl : G.edist j l = ⊤
  · simpa only [graphDecayKernel, hjl, ↓reduceIte, mul_zero] using
      graphDecayKernel_nonneg G γ i l
  have hsum : G.edist i j + G.edist j l ≠ ⊤ := by simp [hij, hjl]
  have htri := G.edist_triangle (u := i) (v := j) (w := l)
  have hil : G.edist i l ≠ ⊤ := fun h => hsum (top_le_iff.mp (h ▸ htri))
  have hnat := ENat.toNat_le_toNat htri hsum
  rw [ENat.toNat_add hij hjl] at hnat
  have hreal : ((G.edist i l).toNat : ℝ) ≤
      ((G.edist i j).toNat : ℝ) + ((G.edist j l).toNat : ℝ) := by exact_mod_cast hnat
  simp only [graphDecayKernel, hij, hjl, hil, ↓reduceIte]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hreal hγ]

/-- Taking square roots `n` times divides the graph exponential rate by `2^n`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708, with the
cross terms of each spectral refinement retained. -/
theorem sqrtKernel_graphDecayKernel (G : SimpleGraph V) (γ : ℝ) (n : ℕ) (i j : V) :
    sqrtKernel (graphDecayKernel G γ) n i j = graphDecayKernel G (γ / 2 ^ n) i j := by
  induction n with
  | zero => simp only [sqrtKernel_zero, pow_zero, div_one]
  | succ n ih =>
    rw [sqrtKernel_succ, ih]
    unfold graphDecayKernel
    split_ifs
    · simp
    · rw [← Real.exp_half]
      congr 1
      rw [pow_succ]
      ring

end ManyBody
