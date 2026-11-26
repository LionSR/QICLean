/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import QICLean.Analysis.FunctionalCalculus.ModularExpectation
import QICLean.Entropy.Surprisal.MarginalTails
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Sites.SupportedDecomposition
import QICLean.Spectral.LowEnergy.Coordinates

/-!
# Upper bounds for the gap of an open chain

Changing a unit ground vector `Ω` by a unitary `U` on the first site, chosen with
`Tr (ρ U) = 0` for the regional state `ρ` of `Ω` on that site, gives an orthogonal unit trial
vector. Only the terms meeting the first site change their energy expectation, so the gap above
a unique ground vector is at most `4J` for a range-one interaction with term norms at most `J`
and local dimension at least two. For positive bond terms of norm at most one only the first bond
changes, by at most one, and the gap is at most one.

For positive bond terms of norm at most one and a ground space `G` of any dimension, the argument
is variational. Write the chain as its first `L - m` sites and its last `m` sites. Some slice `φ`
of a ground vector along a configuration of the last `m` sites has energy at most the ground
energy for the bonds inside the first `L - m` sites; every product `φ ⊗ χ` then has energy at
most the ground energy plus `m`, since at most `m` bonds meet the last `m` sites. These products
form a space of dimension `q ^ m`; were it larger than `G`, it would contain a nonzero vector
orthogonal to `G`, of energy at least the ground energy plus `γ`. Hence `q ^ m ≤ dim G` for every
natural `m < γ`, and `γ ≤ 1 + log (dim G) / log q`; a ground space of dimension less than `q`,
in particular a unique ground vector, has `γ ≤ 1`.

## Main results

* `ManyBody.ChainInteraction.gap_le_four_mul_of_range_one` — `Δ ≤ 4J` for a range-one
  interaction.
* `ManyBody.BondInteraction.gap_le_one_of_nonneg_of_le_one` — `Δ ≤ 1` for positive bond terms of
  norm at most one.
* `ManyBody.BondInteraction.pow_le_finrank_ground_of_lt_gap` — `m < γ` implies `m < L` and
  `q ^ m ≤ dim G`.
* `ManyBody.BondInteraction.gap_le_one_of_finrank_lt`,
  `ManyBody.BondInteraction.gap_le_one_add_log_div_log` — `γ ≤ 1` when `dim G < q`, and
  `γ ≤ 1 + log (dim G) / log q`.

## References

* Z. Landau, U. Vazirani and T. Vidick, arXiv:1307.5143v1, `eq:def-ce` and `l:within`,
  `algo53.tex`, lines 291–293 and 509–515.
* I. Arad, A. Kitaev, Z. Landau and U. Vazirani, arXiv:1301.1162v1, Section 5, the normalization
  before equation (4).
* I. Arad, Z. Landau, U. Vazirani and T. Vidick, arXiv:1602.08828v2, Assumption (DG),
  lines 275–279, and the normalization `0 ≤ h_i ≤ 1`, lines 267 and 806.
-/

open Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator ComplexOrder MatrixOrder
  Kronecker

namespace ManyBody

section TrialVector

variable {L q : ℕ} {J E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}

/-- The full-system gap of a nonempty range-one chain with local dimension at least two is
at most four times the interaction norm bound. -/
theorem ChainInteraction.gap_le_four_mul_of_range_one (h : ChainInteraction L q 1)
    (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (hL : 0 < L) (hq : 2 ≤ q) (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) :
    Δ ≤ 4 * J := by
  classical
  let x : Fin L := ⟨0, hL⟩
  obtain ⟨U, hU⟩ := Matrix.IsHermitian.exists_unitary_trace_mul_eq_zero
    (regionState_isHermitian (X := fun _ ↦ Fin q) {x} Ω)
      (by simpa [RegionConfig, Fintype.card_pi] using hq)
  let K := place (X := fun _ ↦ Fin q) {x} (U : Matrix _ _ ℂ)
  have hUunit :
      (U : Matrix (RegionConfig (fun _ ↦ Fin q) {x})
        (RegionConfig (fun _ ↦ Fin q) {x}) ℂ)ᴴ * (U : Matrix _ _ ℂ) = 1 := by
    convert U.property.1 using 1
    ext i j
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  have hK : Kᴴ * K = 1 := by
    simpa only [K, place_mul, place_conjTranspose,
      place_one] using
      congrArg (place (X := fun _ ↦ Fin q) {x}) hUunit
  have hφ : ‖toEuclideanLin K Ω‖ = 1 :=
    (Entropy.norm_toEuclideanLin_of_conjTranspose_mul_self hK Ω).trans hΩ
  have horth : ⟪Ω, toEuclideanLin K Ω⟫_ℂ = 0 := by
    simpa only [K, inner_place] using hU
  have hgap : Δ ≤
      (⟪toEuclideanLin K Ω, toEuclideanLin h.hamiltonian (toEuclideanLin K Ω)⟫_ℂ).re - E₀ := by
    simpa [hφ, horth] using
      (hgap.posSemidef_sub_smul_one (Interaction.isHermitian_hamiltonian hh) hΩ
          hspan).gap_le (toEuclideanLin K Ω)
  have hE : (⟪Ω, toEuclideanLin h.hamiltonian Ω⟫_ℂ).re = E₀ := by
    have heig : toEuclideanLin h.hamiltonian Ω = (E₀ : ℂ) • Ω := by
      rw [← coe_toEuclideanCLM_eq_toEuclideanLin]
      exact (mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self _))
    rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have hnorm (X : ChainSupport L 1) (v : EuclideanSpace ℂ (Fin L → Fin q))
      (hv : ‖v‖ = 1) : |(⟪v, toEuclideanLin (h.term X) v⟫_ℂ).re| ≤ J := by
    calc
      |(⟪v, toEuclideanLin (h.term X) v⟫_ℂ).re|
          ≤ ‖⟪v, toEuclideanLin (h.term X) v⟫_ℂ‖ := Complex.abs_re_le_norm _
      _ ≤ ‖v‖ * ‖toEuclideanLin (h.term X) v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖h.term X‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (Entropy.norm_toEuclideanLin_le _ _) (norm_nonneg _)
      _ ≤ J := by simpa only [hv, mul_one, one_mul] using hhJ X
  have hsame (X : ChainSupport L 1) (hx : x ∉ X.1) :
      ⟪toEuclideanLin K Ω, toEuclideanLin (h.term X) (toEuclideanLin K Ω)⟫_ℂ =
        ⟪Ω, toEuclideanLin (h.term X) Ω⟫_ℂ := by
    have hc := commute_of_mem_supportedOperators_of_disjoint
      (place_mem_supportedOperators (X := fun _ ↦ Fin q) (U : Matrix _ _ ℂ)) (h.mem X)
      (Finset.disjoint_singleton_left.mpr hx)
    rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← Entropy.toEuclideanLin_mul_apply, ← Entropy.toEuclideanLin_mul_apply, Matrix.mul_assoc,
      ← hc.eq, ← Matrix.mul_assoc, hK, Matrix.one_mul]
  have hdiff (X : ChainSupport L 1) :
      (⟪toEuclideanLin K Ω, toEuclideanLin (h.term X) (toEuclideanLin K Ω)⟫_ℂ).re -
        (⟪Ω, toEuclideanLin (h.term X) Ω⟫_ℂ).re ≤ if x ∈ X.1 then 2 * J else 0 := by
    split_ifs with hx
    · linarith [(abs_le.mp (hnorm X (toEuclideanLin K Ω) hφ)).2,
        (abs_le.mp (hnorm X Ω hΩ)).1]
    · simp only [hsame X hx, sub_self, le_refl]
  have hcard : (Finset.univ.filter (fun X : ChainSupport L 1 ↦ x ∈ X.1)).card ≤ 2 := by
    let t := Finset.univ.filter (fun y : Fin L ↦ y.val = 1)
    have ht : t.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb ↦
      Fin.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    have hbound : (Finset.univ.filter (fun X : ChainSupport L 1 ↦ x ∈ X.1)).card ≤
        t.powerset.card := by
      apply Finset.card_le_card_of_injOn (fun X : ChainSupport L 1 ↦ X.1.erase x)
      · refine fun X hX ↦ Finset.mem_powerset.mpr fun y hy ↦ ?_
        have hval := X.2.2 x (Finset.mem_filter.mp hX).2 y (Finset.mem_erase.mp hy).2
        have hy0 : y.val ≠ 0 := fun hy0 ↦ (Finset.mem_erase.mp hy).1 (Fin.ext hy0)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Nat.le_antisymm hval (Nat.one_le_iff_ne_zero.mpr hy0)⟩
      · refine fun X hX Y hY hXY ↦ Subtype.ext ?_
        simpa only [Finset.insert_erase (Finset.mem_filter.mp hX).2,
          Finset.insert_erase (Finset.mem_filter.mp hY).2] using
          congrArg (fun s : Finset (Fin L) ↦ insert x s) hXY
    exact hbound.trans (by
      simpa only [Finset.card_powerset, pow_one] using
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) ht)
  have hsum :
      (∑ X : ChainSupport L 1,
        ((⟪toEuclideanLin K Ω, toEuclideanLin (h.term X) (toEuclideanLin K Ω)⟫_ℂ).re -
          (⟪Ω, toEuclideanLin (h.term X) Ω⟫_ℂ).re)) ≤
        ((Finset.univ.filter (fun X : ChainSupport L 1 ↦ x ∈ X.1)).card : ℝ) * (2 * J) := by
    simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun X _ ↦ hdiff X)
  have hmul : ((Finset.univ.filter (fun X : ChainSupport L 1 ↦ x ∈ X.1)).card : ℝ) *
      (2 * J) ≤ 4 * J := by
    calc
      _ ≤ 2 * (2 * J) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg (by norm_num) (h.norm_bound_nonneg hhJ x))
      _ = 4 * J := by ring
  have henergy :
      (⟪toEuclideanLin K Ω, toEuclideanLin h.hamiltonian (toEuclideanLin K Ω)⟫_ℂ).re - E₀ ≤
        4 * J := by
    rw [← hE]
    simpa only [Interaction.hamiltonian, map_sum, LinearMap.sum_apply, inner_sum,
      Complex.re_sum, Finset.sum_sub_distrib] using hsum.trans hmul
  exact hgap.trans henergy

/-- An open chain with local dimension at least two and positive nearest-neighbour
contractions has gap at most one above a unique ground vector. This proves the
normalization used in Arad–Kitaev–Landau–Vazirani, arXiv:1301.1162v1, Section 5, before
equation (4).
An endpoint unitary gives an orthogonal unit trial vector. Only the first bond can
change its expectation, and the change is at most one because the bond lies between
zero and the identity. The rank-one gap inequality is essential to the conclusion. -/
theorem BondInteraction.gap_le_one_of_nonneg_of_le_one {L q : ℕ} (hL : 0 < L) (hq : 2 ≤ q)
    (Φ : BondInteraction L q) (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped Φ.hamiltonian E₀ Δ)
    (hspan : groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Ω}) : Δ ≤ 1 := by
  classical
  let x : Fin L := ⟨0, hL⟩
  obtain ⟨U, hU⟩ := Matrix.IsHermitian.exists_unitary_trace_mul_eq_zero
    (regionState_isHermitian (X := fun _ ↦ Fin q) {x} Ω)
      (by simpa [RegionConfig, Fintype.card_pi] using hq)
  let K := place (X := fun _ ↦ Fin q) {x} (U : Matrix _ _ ℂ)
  have hUunit :
      (U : Matrix (RegionConfig (fun _ ↦ Fin q) {x})
        (RegionConfig (fun _ ↦ Fin q) {x}) ℂ)ᴴ * (U : Matrix _ _ ℂ) = 1 := by
    convert U.property.1 using 1
    ext i j
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  have hK : Kᴴ * K = 1 := by
    simpa only [K, place_mul, place_conjTranspose,
      place_one] using
      congrArg (place (X := fun _ ↦ Fin q) {x}) hUunit
  have hφ : ‖toEuclideanLin K Ω‖ = 1 :=
    (Entropy.norm_toEuclideanLin_of_conjTranspose_mul_self hK Ω).trans hΩ
  have horth : ⟪Ω, toEuclideanLin K Ω⟫_ℂ = 0 := by
    simpa only [K, inner_place] using hU
  have hgap : Δ ≤
      (⟪toEuclideanLin K Ω, toEuclideanLin Φ.hamiltonian (toEuclideanLin K Ω)⟫_ℂ).re - E₀ := by
    simpa [hφ, horth, Interaction.hamiltonian] using (hgap.posSemidef_sub_smul_one
      (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian hΩ
      hspan).gap_le (toEuclideanLin K Ω)
  have hnonneg (i : Fin (L - 1)) (v : EuclideanSpace ℂ (Fin L → Fin q)) :
      0 ≤ (⟪v, toEuclideanLin (Φ.term i) v⟫_ℂ).re := by
    simpa only [RCLike.re_to_complex] using
      (isPositive_toEuclideanLin_iff.mpr (h0 i).posSemidef).re_inner_nonneg_right v
  have hnorm (i : Fin (L - 1)) (v : EuclideanSpace ℂ (Fin L → Fin q))
      (hv : ‖v‖ = 1) : |(⟪v, toEuclideanLin (Φ.term i) v⟫_ℂ).re| ≤ 1 := by
    calc
      |(⟪v, toEuclideanLin (Φ.term i) v⟫_ℂ).re| ≤ ‖⟪v, toEuclideanLin (Φ.term i) v⟫_ℂ‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖v‖ * ‖toEuclideanLin (Φ.term i) v‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖Φ.term i‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (Entropy.norm_toEuclideanLin_le _ _) (norm_nonneg _)
      _ ≤ 1 := by
        simpa only [hv, mul_one, one_mul] using
          (CStarAlgebra.norm_le_one_iff_of_nonneg _ (h0 i)).mpr (h1 i)
  have hsame (i : Fin (L - 1)) (hi : i.val ≠ 0) :
      ⟪toEuclideanLin K Ω, toEuclideanLin (Φ.term i) (toEuclideanLin K Ω)⟫_ℂ =
        ⟪Ω, toEuclideanLin (Φ.term i) Ω⟫_ℂ := by
    have hx : x ∉ interval L i.val (i.val + 2) := by
      simp only [mem_interval, x]
      omega
    have hc := commute_of_mem_supportedOperators_of_disjoint
      (place_mem_supportedOperators (X := fun _ ↦ Fin q) (U : Matrix _ _ ℂ)) (Φ.mem i)
      (Finset.disjoint_singleton_left.mpr hx)
    rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← Entropy.toEuclideanLin_mul_apply, ← Entropy.toEuclideanLin_mul_apply, Matrix.mul_assoc,
      ← hc.eq, ← Matrix.mul_assoc, hK, Matrix.one_mul]
  have hdiff (i : Fin (L - 1)) :
      (⟪toEuclideanLin K Ω, toEuclideanLin (Φ.term i) (toEuclideanLin K Ω)⟫_ℂ).re -
        (⟪Ω, toEuclideanLin (Φ.term i) Ω⟫_ℂ).re ≤ if i.val = 0 then 1 else 0 := by
    split_ifs with hi
    · linarith [hnonneg i Ω, (abs_le.mp (hnorm i (toEuclideanLin K Ω) hφ)).2]
    · simp only [hsame i hi, sub_self, le_refl]
  have hE : (⟪Ω, toEuclideanLin Φ.hamiltonian Ω⟫_ℂ).re = E₀ := by
    have heig : toEuclideanLin Φ.hamiltonian Ω = (E₀ : ℂ) • Ω := by
      rw [← coe_toEuclideanCLM_eq_toEuclideanLin]
      exact (mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self _))
    rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have hcard : (Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val = 0)).card ≤ 1 :=
    Finset.card_le_one.mpr fun i hi j hj ↦
      Fin.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have hsum :
      (∑ i : Fin (L - 1),
        ((⟪toEuclideanLin K Ω, toEuclideanLin (Φ.term i) (toEuclideanLin K Ω)⟫_ℂ).re -
          (⟪Ω, toEuclideanLin (Φ.term i) Ω⟫_ℂ).re)) ≤
        ((Finset.univ.filter (fun i : Fin (L - 1) ↦ i.val = 0)).card : ℝ) := by
    simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hdiff i)
  have henergy :
      (⟪toEuclideanLin K Ω, toEuclideanLin Φ.hamiltonian (toEuclideanLin K Ω)⟫_ℂ).re - E₀ ≤
        1 := by
    rw [← hE]
    simpa only [Interaction.hamiltonian, map_sum, LinearMap.sum_apply, inner_sum,
      Complex.re_sum, Finset.sum_sub_distrib] using hsum.trans (by exact_mod_cast hcard)
  exact hgap.trans henergy

end TrialVector

section GroundDimension

/-- A nearest-neighbour term has the stated support. -/
private theorem interval_subset_interval_zero {L c : ℕ} {i : ℕ} (hi : i + 2 ≤ c) :
    interval L i (i + 2) ⊆ interval L 0 c := by
  intro v hv
  rw [mem_interval] at hv ⊢
  omega

/-- At most `L - c` of the nearest-neighbour terms meet the last `L - c` sites. -/
private theorem card_filter_not_le_le (L c : ℕ) (hc : c ≤ L) :
    (Finset.univ.filter fun i : Fin (L - 1) ↦ ¬ i.val + 2 ≤ c).card ≤ L - c := by
  have h := Finset.card_le_card_of_injOn (t := Finset.range (L - c))
    (s := Finset.univ.filter fun i : Fin (L - 1) ↦ ¬ i.val + 2 ≤ c)
    (fun i : Fin (L - 1) ↦ i.val + 1 - c)
    (by
      intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      rw [Finset.mem_coe, Finset.mem_range]
      change i.val + 1 - c < L - c
      have := i.isLt
      have hi' := hi.2
      omega)
    (by
      intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_filter] at hi hj
      have hval : i.val + 1 - c = j.val + 1 - c := hij
      exact Fin.ext (by omega))
  simpa using h

/-- **The gap is at most logarithmic in the ground-space dimension.** For a
nearest-neighbour chain of `L` sites with terms `0 ≤ h_i ≤ 1`, a gap `γ` above
the least spectral value `μ`, and ground space `G`, every natural `m < γ`
satisfies `m < L` and `q ^ m ≤ dim G`. The positive-contraction normalization
and the gap are those of Arad–Landau–Vazirani–Vidick, arXiv:1602.08828v2, lines 267, 806 and
Assumption (DG), lines 275–279; the source states no bound on `γ`. -/
theorem BondInteraction.pow_le_finrank_ground_of_lt_gap :
    ∀ (L q : ℕ) (Φ : BondInteraction L q)
      (h0 : ∀ i, 0 ≤ Φ.term i) (_h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ),
      let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
      let hH : H.IsHermitian :=
        (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
      mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
      (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
      let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
      ∀ m : ℕ, (m : ℝ) < gamma → m < L ∧ q ^ m ≤ Module.finrank ℂ G := by
  classical
  intro L q Φ h0 h1 mu nu gamma H hH hmu hnu hmunu hgap G
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  set Hc := (toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) H).toLinearMap
  -- The ground space misses an eigenvector at `nu`, so it is proper.
  have hGlt : Module.finrank ℂ G < q ^ L := by
    obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hnu
    have hnot : hH.eigenvectorBasis j ∉ G := by
      intro hmem
      have h0' := (Submodule.mem_spectralSpanLE_iff _ _ _ _).mp hmem j (by rw [hj]; exact hmunu)
      simp [OrthonormalBasis.repr_self] at h0'
    have hne : G ≠ ⊤ := fun htop ↦ hnot (htop ▸ Submodule.mem_top)
    have := Submodule.finrank_lt hne
    simpa [finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin] using this
  -- The main estimate for cuts with `m ≤ L`.
  have hmain : ∀ m : ℕ, m ≤ L → (m : ℝ) < gamma → q ^ m ≤ Module.finrank ℂ G := by
    intro m hmL hmγ
    set c := L - m with hc
    set B : Finset (Fin L) := interval L 0 c
    set e := cutEquiv (fun _ ↦ Fin q) B
    set S : Finset (Fin (L - 1)) := Finset.univ.filter fun i ↦ i.val + 2 ≤ c
    let cut : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ →
        Matrix ((({v // v ∈ B}) → Fin q) × (({v // v ∉ B}) → Fin q))
          ((({v // v ∈ B}) → Fin q) × (({v // v ∉ B}) → Fin q)) ℂ :=
      fun X ↦ cutOperator (X := fun _ ↦ Fin q) B X
    have hcut_sum : ∀ (s : Finset (Fin (L - 1))),
        cut (Φ.partialHamiltonian s) = ∑ i ∈ s, cut (Φ.term i) := by
      intro s
      exact map_sum (reindexLinearEquiv ℂ ℂ e e) _ s
    have hcut_psd : ∀ X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ, X.PosSemidef →
        (cut X).PosSemidef := fun X hX ↦ hX.submatrix _
    have hcut_one : cut 1 = 1 := submatrix_one_equiv e.symm
    obtain ⟨σ₀⟩ : Nonempty (Fin L → Fin q) := ⟨fun _ ↦ ⟨0, by omega⟩⟩
    set y₀ := (e σ₀).2
    -- Left part in Kronecker form.
    set M := ∑ i ∈ S, fun x x' ↦ cut (Φ.term i) (x, y₀) (x', y₀)
    have hleft : cut (Φ.partialHamiltonian S) = M ⊗ₖ (1 : Matrix _ _ ℂ) := by
      rw [hcut_sum]
      have hterm : ∀ i ∈ S, cut (Φ.term i) =
          (fun x x' ↦ cut (Φ.term i) (x, y₀) (x', y₀)) ⊗ₖ (1 : Matrix _ _ ℂ) := by
        intro i hi
        exact IsSupportedOn.cutOperator_eq_kronecker_one (Φ.mem i)
          (interval_subset_interval_zero (Finset.mem_filter.mp hi).2) y₀
      rw [Finset.sum_congr rfl hterm]
      ext p p'
      simp only [kroneckerMap, Matrix.of_apply, Matrix.sum_apply, M, Finset.sum_apply,
        Finset.sum_mul]
    -- Right part bounded by the number of right terms.
    set N := cut (Φ.partialHamiltonian Sᶜ)
    have hN0 : N.PosSemidef :=
      hcut_psd _ (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun i _ ↦ h0 i))
    have hcard : (Sᶜ).card ≤ m := by
      have := card_filter_not_le_le L c (by omega)
      rw [Finset.compl_filter]
      omega
    have hNle : ∑ i ∈ Sᶜ, Φ.term i ≤ ((m : ℝ) : ℂ) • (1 : Matrix (Fin L → Fin q) _ ℂ) := by
      calc ∑ i ∈ Sᶜ, Φ.term i ≤ ∑ _i ∈ Sᶜ, (1 : Matrix (Fin L → Fin q) _ ℂ) :=
            Finset.sum_le_sum fun i _ ↦ h1 i
        _ = ((Sᶜ).card : ℂ) • (1 : Matrix (Fin L → Fin q) _ ℂ) := by
            rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
        _ ≤ ((m : ℝ) : ℂ) • (1 : Matrix (Fin L → Fin q) _ ℂ) := by
            rw [Matrix.le_iff, ← sub_smul]
            refine Matrix.PosSemidef.one.smul ?_
            have : ((Sᶜ).card : ℝ) ≤ m := by exact_mod_cast hcard
            rw [show ((m : ℝ) : ℂ) - ((Sᶜ).card : ℂ) = (((m : ℝ) - (Sᶜ).card : ℝ) : ℂ) by
              push_cast; ring]
            exact Complex.zero_le_real.mpr (by linarith)
    have hN1 : (((m : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) - N).PosSemidef := by
      have h' := hcut_psd _ (Matrix.le_iff.mp hNle)
      have hlin : cut (((m : ℝ) : ℂ) • (1 : Matrix (Fin L → Fin q) _ ℂ) - ∑ i ∈ Sᶜ, Φ.term i) =
          ((m : ℝ) : ℂ) • cut 1 - N :=
        rfl
      rwa [hlin, hcut_one] at h'
    have hHc : cut H = M ⊗ₖ (1 : Matrix _ _ ℂ) + N := by
      rw [← hleft]
      change cut (∑ i, Φ.term i) = cut (∑ i ∈ S, Φ.term i) + cut (∑ i ∈ Sᶜ, Φ.term i)
      rw [← Finset.sum_add_sum_compl S Φ.term]
      exact map_add (reindexLinearEquiv ℂ ℂ e e) _ _
    -- A nonzero ground vector and its energy.
    have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
    obtain ⟨ψ, hψG, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hGne
    have hψE : (inner ℂ ψ (Hc ψ)).re ≤ mu * ‖ψ‖ ^ 2 :=
      Submodule.re_inner_apply_le_of_mem_spectralSpanLE hH.eigenvectorBasis hH.eigenvalues Hc
        (fun j ↦ hH.toEuclideanCLM_eigenvectorBasis j) mu hψG
    -- Quadratic forms in cut coordinates.
    have hform : ∀ x : EuclideanSpace ℂ (Fin L → Fin q),
        (inner ℂ x (Hc x)).re =
          (star (fun p ↦ x (e.symm p)) ⬝ᵥ (cut H *ᵥ fun p ↦ x (e.symm p))).re := by
      intro x
      have h' := Entropy.inner_cutOperator (n := fun _ : Fin L ↦ q) B H x
      have hl : inner ℂ x (Hc x) = inner ℂ x (toEuclideanLin H x) := rfl
      rw [hl, ← h', EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rfl
    have hnormc : ∀ x : EuclideanSpace ℂ (Fin L → Fin q),
        ‖x‖ ^ 2 = (star (fun p ↦ x (e.symm p)) ⬝ᵥ fun p ↦ x (e.symm p)).re := by
      intro x
      rw [← norm_cutVector (X := fun _ : Fin L ↦ Fin q) B x, @norm_sq_eq_re_inner ℂ,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rfl
    set Ψ : _ → ℂ := fun p ↦ ψ (e.symm p)
    have hΨ0 : Ψ ≠ 0 := by
      intro hzero
      apply hψ0
      ext x
      simpa [Ψ] using congrFun hzero (e x)
    have hΨE : (star Ψ ⬝ᵥ ((M ⊗ₖ (1 : Matrix _ _ ℂ) + N) *ᵥ Ψ)).re ≤
        mu * (star Ψ ⬝ᵥ Ψ).re := by
      rw [← hHc, ← hform, ← hnormc]
      exact hψE
    obtain ⟨φ, hφ0, hφ⟩ := Matrix.exists_slice_product_energy_le M N hN0 hN1 Ψ hΨ0 hΨE
    -- The product space in the original coordinates.
    let T : ((({v // v ∉ B}) → Fin q) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin L → Fin q) :=
      { toFun := fun χ ↦ WithLp.toLp 2 fun x ↦ φ (e x).1 * χ (e x).2
        map_add' := by
          intro χ χ'
          ext x
          simp [mul_add]
        map_smul' := by
          intro t χ
          ext x
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, PiLp.smul_apply]
          ring }
    have hT : ∀ χ, (fun p ↦ T χ (e.symm p)) = fun p ↦ φ p.1 * χ p.2 := by
      intro χ
      funext p
      simp [T]
    have hTinj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro χ hχ
      rw [LinearMap.mem_ker] at hχ
      obtain ⟨a₀, ha₀⟩ := Function.ne_iff.mp hφ0
      funext y
      have h' := congrFun (hT χ) (a₀, y)
      rw [hχ] at h'
      simp only [PiLp.zero_apply, Pi.zero_apply] at h' ⊢
      exact (mul_eq_zero.mp h'.symm).resolve_left ha₀
    have hrange : Module.finrank ℂ (LinearMap.range T) = q ^ m := by
      rw [LinearMap.finrank_range_of_inj hTinj, Module.finrank_fintype_fun_eq_card,
        Fintype.card_pi]
      simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
      have hB : B.card = c := by
        have : B = Finset.univ.filter fun i : Fin L ↦ i.val < c := by
          ext i
          simp [B, mem_interval]
        rw [this, Fin.card_filter_val_lt]
        omega
      omega
    rw [← hrange]
    refine Submodule.finrank_le_finrank_of_quadratic_window Hc G (LinearMap.range T)
      (μ := mu) (c := m) hmγ
      (fun w hw ↦ hH.mul_norm_sq_le_re_inner_of_mem_orthogonal_ground hgap hw) ?_
    rintro _ ⟨χ, rfl⟩
    rw [hform, hnormc, hT, hHc]
    exact hφ χ
  intro m hmγ
  have hmL : m < L := by
    by_contra hLm
    push Not at hLm
    have hLγ : (L : ℝ) < gamma := lt_of_le_of_lt (by exact_mod_cast hLm) hmγ
    have := hmain L le_rfl hLγ
    omega
  exact ⟨hmL, hmain m hmL.le hmγ⟩

/-- **A ground space of dimension below the local dimension has gap at most
one.** In particular a unique ground state has gap at most one.
Arad–Landau–Vazirani–Vidick, arXiv:1602.08828v2, Assumption (DG), lines 275–279. -/
theorem BondInteraction.gap_le_one_of_finrank_lt (L q : ℕ)
    (Φ : BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    Module.finrank ℂ G < q → gamma ≤ 1 := by
  intro H hH hmu hnu hmunu hgap G hlt
  by_contra hγ
  push Not at hγ
  have := (BondInteraction.pow_le_finrank_ground_of_lt_gap L q Φ h0 h1 mu nu gamma hmu hnu
    hmunu hgap 1 (by exact_mod_cast hγ)).2
  rw [pow_one] at this
  exact (not_le.mpr hlt) this

/-- **Logarithmic gap bound.** The gap above the ground space of dimension `r`
satisfies `γ ≤ 1 + log r / log q`. Arad–Landau–Vazirani–Vidick, arXiv:1602.08828v2,
Assumption (DG), lines 275–279, with the normalization `0 ≤ h_i ≤ 1` of lines 267 and 806. -/
theorem BondInteraction.gap_le_one_add_log_div_log (L q : ℕ)
    (Φ : BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1) (mu nu gamma : ℝ) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.hamiltonian
    let hH : H.IsHermitian :=
      (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
    mu ∈ spectrum ℝ H → nu ∈ spectrum ℝ H → mu < nu →
    (∀ z ∈ spectrum ℝ H, z = mu ∨ mu + gamma ≤ z) →
    let G := Submodule.spectralSpanLE hH.eigenvectorBasis hH.eigenvalues mu
    gamma ≤ 1 + Real.log (Module.finrank ℂ G : ℝ) / Real.log q := by
  intro H hH hmu hnu hmunu hgap G
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hnu (ne_of_lt hmunu)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hGne : G ≠ ⊥ := hH.spectralSpanLE_ne_bot_of_mem_spectrum hmu le_rfl
  have hr : 1 ≤ Module.finrank ℂ G := Submodule.one_le_finrank_iff.mpr hGne
  have hlogr : 0 ≤ Real.log (Module.finrank ℂ G : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hr)
  rcases le_or_gt gamma 0 with hγ | hγ
  · have := div_nonneg hlogr hlogq.le
    linarith
  set m := ⌈gamma⌉₊ - 1
  have hceil : 1 ≤ ⌈gamma⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hγ).ne'
  have hm : (m : ℝ) = ⌈gamma⌉₊ - 1 := by
    rw [Nat.cast_sub hceil, Nat.cast_one]
  have hmγ : (m : ℝ) < gamma := by
    rw [hm]
    linarith [Nat.ceil_lt_add_one hγ.le]
  have hpow := (BondInteraction.pow_le_finrank_ground_of_lt_gap L q Φ h0 h1 mu nu gamma hmu
    hnu hmunu hgap m hmγ).2
  have hlog : (m : ℝ) * Real.log q ≤ Real.log (Module.finrank ℂ G : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have hdiv : (m : ℝ) ≤ Real.log (Module.finrank ℂ G : ℝ) / Real.log q :=
    (le_div_iff₀ hlogq).mpr hlog
  have hceil_le : gamma ≤ ⌈gamma⌉₊ := Nat.le_ceil gamma
  linarith

end GroundDimension

end ManyBody
