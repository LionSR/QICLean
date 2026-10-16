/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import QICLean.Entropy.BufferDiscount

/-!
# Excitation energy of a maximizing product without a positive floor

An optimal nested product of positive semidefinite filters can be chosen so that its
normalized output obeys the same energy estimate as the positive-floor maximizers.
The proof takes a convergent subsequence in the compact set of zero-floor feasible
families. The energy inequality is first written homogeneously, so it is closed even
at zero output. A fixed strictly positive feasible competitor proves that the limiting
maximizer has nonzero output before it is normalized.

## Main results

* `exists_max_feasible_chain_mem_of_pos_floor`: a closed condition satisfied by a
  maximizing family at every positive floor persists for some zero-floor maximizer.
* `exists_max_feasible_chain_zero_floor_energy`: a zero-floor maximizer with nonzero
  output and the homogeneous single-split energy estimate.
* `exists_max_feasible_chain_zero_floor_normalized_energy`: its normalized energy estimate.

## References

The compact-limit argument adapts OpenAI's
`lean/OAI/MathematicalPhysics/PEPSFilters/EnergyOptimizer.lean`,
`exists_maximizer_energy`, at revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The coordinate-family argument is replaced by compactness of QICLean's existing feasible
sets and its passage from positive-floor norm bounds to zero floor. The result is stated
for arbitrary finite sites and supported interactions. It retains the weight restriction
and energy coefficient of `re_inner_sub_le_of_max`; it does not assert the upstream sharp
nearest-neighbor coefficient or the complete geometric-optimizer conclusion.
-/

open Complex Matrix Filter Topology
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {m : ℕ}

/-- A closed condition attained by maximizers at every positive floor is attained by
some zero-floor maximizer. No nesting or nonvanishing assumption is required.

A derived compactness statement; compare the maximizing-limit step of OpenAI's
`EnergyOptimizer.lean`, lines 77–97, at the source revision cited above. -/
theorem exists_max_feasible_chain_mem_of_pos_floor (D : ℕ → Finset V)
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hne : ∀ j : Fin m, Nonempty (RegionConfig n (D j)))
    (Ω : EuclideanSpace ℂ (SiteConfig n))
    (T : Set ((j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ))
    (hT : IsClosed T)
    (hpos : ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
        (∀ j : Fin m,
          IsFeasibleFilter (δ / Fintype.card (RegionConfig n (D j))) (a j) (K j)) ∧
        (∀ K' : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
          (∀ j : Fin m,
            IsFeasibleFilter (δ / Fintype.card (RegionConfig n (D j))) (a j) (K' j)) →
          ‖toEuclideanLin (liftProd (chainList D K' fun _ ↦ True)) Ω‖ ≤
            ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖) ∧ K ∈ T) :
    ∃ K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
      (∀ j : Fin m, IsFeasibleFilter 0 (a j) (K j)) ∧
      (∀ K' : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
        (∀ j : Fin m, IsFeasibleFilter 0 (a j) (K' j)) →
        ‖toEuclideanLin (liftProd (chainList D K' fun _ ↦ True)) Ω‖ ≤
          ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖) ∧ K ∈ T := by
  classical
  let δ : ℕ → ℝ := fun k ↦ (1 / 2) * (1 / ((k : ℝ) + 1))
  have hδ0 (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hδ1 (k : ℕ) : δ k < 1 := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hle : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
      linarith
    dsimp [δ]
    linarith
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
  choose K hK hmax hKT using fun k ↦ hpos (δ k) (hδ0 k) (hδ1 k)
  let S := Set.pi Set.univ fun j : Fin m ↦
    {L : Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ |
      IsFeasibleFilter 0 (a j) L}
  have hS : IsCompact S :=
    isCompact_univ_pi fun j ↦ isCompact_setOf_isFeasibleFilter (by rfl) (ha j)
  have hKS (k : ℕ) : K k ∈ S := by
    intro j _
    exact (hK k j).mono_floor (by positivity)
  obtain ⟨K₀, hK₀, u, hu, hlim⟩ := hS.tendsto_subseq hKS
  have hnorm := (continuous_norm_liftProd_chainList D (fun _ ↦ True) Ω).tendsto K₀
    |>.comp hlim
  have hclosed : K₀ ∈ T := hT.mem_of_tendsto hlim
    (Filter.Eventually.of_forall fun k ↦ hKT (u k))
  refine ⟨K₀, fun j ↦ hK₀ j (Set.mem_univ j), ?_, hclosed⟩
  intro K' hK'
  let a' : ℕ → ℝ := fun j ↦ if hj : j < m then a ⟨j, hj⟩ else 0
  have ha' : ∀ j, 0 ≤ a' j := by
    intro j
    dsimp [a']
    split_ifs with hj
    · exact ha ⟨j, hj⟩
    · rfl
  apply norm_le_of_forall_floor D a' ha' hne Ω
  · intro ε hε0 hε1 L hL
    apply ge_of_tendsto hnorm
    have hevent : ∀ᶠ k in atTop, δ (u k) < ε :=
      (hδ.comp hu.tendsto_atTop).eventually_lt_const hε0
    filter_upwards [hevent] with k hk
    apply hmax (u k) L
    intro j
    have hj : IsFeasibleFilter (ε / Fintype.card (RegionConfig n (D j))) (a j) (L j) := by
      simpa [a', j.isLt] using hL j
    exact hj.mono_floor (div_le_div_of_nonneg_right hk.le (by positivity))
  · intro j
    simpa [a', j.isLt] using hK' j

/-- Any family dominating every zero-floor feasible output norm has nonzero output
if the input is nonzero. Its own feasibility and the signs of the weights are not
required. A fixed positive-floor uniform family supplies a nonzero competitor.

This comparison lemma supplies the nonvanishing step corresponding to OpenAI's
`EnergyOptimizer.lean`, line 98, at the source revision cited above. -/
lemma norm_liftProd_pos_of_zero_floor_max (D : ℕ → Finset V) (a : Fin m → ℝ)
    (hne : ∀ j : Fin m, Nonempty (RegionConfig n (D j)))
    {Ω : EuclideanSpace ℂ (SiteConfig n)} (hΩ : Ω ≠ 0)
    {K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ}
    (hmax : ∀ K' : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
      (∀ j : Fin m, IsFeasibleFilter 0 (a j) (K' j)) →
      ‖toEuclideanLin (liftProd (chainList D K' fun _ ↦ True)) Ω‖ ≤
        ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖) :
    0 < ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖ := by
  classical
  let f : Fin m → ℝ := fun j ↦ 1 / (2 * Fintype.card (RegionConfig n (D j)))
  have hd (j : Fin m) : (0 : ℝ) < Fintype.card (RegionConfig n (D j)) := by
    let := hne j
    exact_mod_cast Fintype.card_pos
  have hf (j : Fin m) : 0 < f j := by
    dsimp [f]
    exact one_div_pos.mpr (mul_pos (by norm_num) (hd j))
  have hcard (j : Fin m) : Fintype.card (RegionConfig n (D j)) * f j ≤ 1 := by
    dsimp [f]
    have heq : (Fintype.card (RegionConfig n (D j)) : ℝ) *
        (1 / (2 * Fintype.card (RegionConfig n (D j)))) = 1 / 2 := by
      field_simp [(hd j).ne']
    rw [heq]
    norm_num
  choose U hU using fun j : Fin m ↦ show
      ∃ U : Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
        IsFeasibleFilter (f j) (a j) U from by
    let := hne j
    exact ⟨_, isFeasibleFilter_uniform (a := a j) (hcard j)⟩
  have hU0 := toEuclideanLin_liftProd_chainList_ne_zero D hf hU (fun _ ↦ True) hΩ
  exact (norm_pos_iff.mpr hU0).trans_le (hmax U fun j ↦ (hU j).mono_floor (hf j).le)

/-- Normalized and homogeneous energy bounds agree at every nonzero vector. -/
private theorem normalized_energy_le_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) {ψ : EuclideanSpace ℂ ι} (hψ : ψ ≠ 0) (E₀ B : ℝ) :
    (⟪((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ,
        toEuclideanLin H (((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ)⟫_ℂ).re - E₀ ≤ B ↔
      (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2 ≤ B * ‖ψ‖ ^ 2 := by
  have hr : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
  have hpair : (⟪((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ,
        toEuclideanLin H (((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ)⟫_ℂ).re =
      ‖ψ‖⁻¹ ^ 2 * (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re := by
    simp [map_smul, inner_smul_left, inner_smul_right, Complex.mul_re, pow_two]
    ring
  rw [hpair]
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg ‖ψ‖)
    have hi : ‖ψ‖ ^ 2 * ‖ψ‖⁻¹ ^ 2 = 1 := by field_simp [hr]
    rw [mul_sub, ← mul_assoc, hi, one_mul] at hmul
    simpa [mul_comm] using hmul
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg ‖ψ‖⁻¹)
    have hi : ‖ψ‖⁻¹ ^ 2 * ‖ψ‖ ^ 2 = 1 := by field_simp [hr]
    rw [mul_sub] at hmul
    have hleft : ‖ψ‖⁻¹ ^ 2 * (E₀ * ‖ψ‖ ^ 2) = E₀ := by
      calc
        _ = E₀ * (‖ψ‖⁻¹ ^ 2 * ‖ψ‖ ^ 2) := by ring
        _ = E₀ := by rw [hi, mul_one]
    have hright : ‖ψ‖⁻¹ ^ 2 * (B * ‖ψ‖ ^ 2) = B := by
      calc
        _ = B * (‖ψ‖⁻¹ ^ 2 * ‖ψ‖ ^ 2) := by ring
        _ = B := by rw [hi, mul_one]
    rwa [hleft, hright] at hmul

/-- Some zero-floor norm maximizer satisfies the homogeneous excitation-energy estimate.
The filters may be singular. Each original interaction is split by at most one region;
neither a spectral gap nor a normalized input is needed for this energy statement.

**Scope restriction (weights and coefficient):** This is an arbitrary-site analogue
of OpenAI's `EnergyOptimizer.lean`, lines 62–109, with `a ≤ 1/2` and the coarse
`4 * supportDim²` coefficient from `re_inner_sub_le_of_max`. The source permits
`a ≤ 1` with the sharp nearest-neighbor coefficient. See
`docs/paper-gaps/oai26_zero_floor_energy_scope.tex`; removal requires a sharp
positive-floor maximizing-family estimate before applying the same compact limit. -/
theorem exists_max_feasible_chain_zero_floor_energy (D : ℕ → Finset V)
    (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha2 : ∀ j, a j ≤ 1 / 2)
    {Ω : EuclideanSpace ℂ (SiteConfig n)} (hΩ : Ω ≠ 0)
    {ι : Type*} [Fintype ι] (h : ι → Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (S : ι → Finset V) (hsupp : ∀ i, IsSupportedOn (h i) (S i))
    (hherm : ∀ i, (h i).IsHermitian) {c₀ : ℝ} (hnorm : ∀ i, ‖h i‖ ≤ c₀)
    (hsingle : ∀ i, ∀ j ∈ splitIndices (S i) D m,
      ∀ j' ∈ splitIndices (S i) D m, j = j')
    {E₀ : ℝ} (heig : toEuclideanLin (∑ i, h i) Ω = (E₀ : ℂ) • Ω) :
    ∃ K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
      (∀ j : Fin m, IsFeasibleFilter 0 (a j) (K j)) ∧
      (∀ K' : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
        (∀ j : Fin m, IsFeasibleFilter 0 (a j) (K' j)) →
        ‖toEuclideanLin (liftProd (chainList D K' fun _ ↦ True)) Ω‖ ≤
          ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖) ∧
      let ψ := toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω
      0 < ‖ψ‖ ∧ (⟪ψ, toEuclideanLin (∑ i, h i) ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2 ≤
        (∑ j : Fin m, 4 * a j ^ 2 *
          ∑ i ∈ crossingTerms S (D j), supportDim n (S i) ^ 2 * c₀) * ‖ψ‖ ^ 2 := by
  classical
  obtain ⟨σ₀, -⟩ : ∃ σ : SiteConfig n, Ω σ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hΩ (by ext σ; exact hcon σ)
  have hne (j : Fin m) : Nonempty (RegionConfig n (D j)) := ⟨fun v ↦ σ₀ v⟩
  let B := ∑ j : Fin m, 4 * a j ^ 2 *
    ∑ i ∈ crossingTerms S (D j), supportDim n (S i) ^ 2 * c₀
  let Ψ := fun K : (j : Fin m) →
      Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ ↦
    toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω
  have hΨ : Continuous Ψ := by
    simp_rw [Ψ, liftProd_chainList_eq]
    have hp : Continuous fun K : (j : Fin m) →
        Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ ↦
        ((((List.finRange m).filter fun _ ↦ decide True).reverse).map
          fun j : Fin m ↦ localLift (D j) (K j)).prod :=
      continuous_list_prod _ fun j _ ↦
        ((localLiftₗ (D j)).continuous_of_finiteDimensional).comp (continuous_apply j)
    simp only [toLpLin_apply]
    exact (PiLp.continuous_toLp 2 _).comp (hp.matrix_mulVec continuous_const)
  let T := {K | (⟪Ψ K, toEuclideanLin (∑ i, h i) (Ψ K)⟫_ℂ).re -
    E₀ * ‖Ψ K‖ ^ 2 ≤ B * ‖Ψ K‖ ^ 2}
  have hT : IsClosed T := by
    apply isClosed_le
    · exact (Complex.continuous_re.comp
        (hΨ.inner ((toEuclideanLin (∑ i, h i)).continuous_of_finiteDimensional.comp hΨ))).sub
          (continuous_const.mul (hΨ.norm.pow 2))
    · exact continuous_const.mul (hΨ.norm.pow 2)
  have hpos (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
      ∃ K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
        (∀ j : Fin m,
          IsFeasibleFilter (δ / Fintype.card (RegionConfig n (D j))) (a j) (K j)) ∧
        (∀ K' : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
          (∀ j : Fin m,
            IsFeasibleFilter (δ / Fintype.card (RegionConfig n (D j))) (a j) (K' j)) →
          ‖toEuclideanLin (liftProd (chainList D K' fun _ ↦ True)) Ω‖ ≤
            ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖) ∧ K ∈ T := by
    let f : Fin m → ℝ := fun j ↦ δ / Fintype.card (RegionConfig n (D j))
    have hd (j : Fin m) : (0 : ℝ) < Fintype.card (RegionConfig n (D j)) := by
      let := hne j
      exact_mod_cast Fintype.card_pos
    have hf (j : Fin m) : 0 < f j := div_pos hδ0 (hd j)
    have hcard (j : Fin m) : Fintype.card (RegionConfig n (D j)) * f j < 1 := by
      dsimp [f]
      rwa [mul_div_cancel₀ _ (hd j).ne']
    obtain ⟨K, hK, hmax⟩ := exists_max_feasible_chain D f a (fun j ↦ (hf j).le)
      (fun j ↦ (ha j).le) hne (fun j ↦ (hcard j).le) Ω
    refine ⟨K, hK, hmax, ?_⟩
    exact (normalized_energy_le_iff (∑ i, h i)
      (toEuclideanLin_liftProd_chainList_ne_zero D hf hK (fun _ ↦ True) hΩ) E₀ B).mp
      (re_inner_sub_le_of_max D hD f a hf ha ha2 hcard K hK hΩ σ₀ hmax
        h S hsupp hherm hnorm hsingle heig)
  obtain ⟨K, hK, hmax, henergy⟩ := exists_max_feasible_chain_mem_of_pos_floor D a
    (fun j ↦ (ha j).le) hne Ω T hT hpos
  exact ⟨K, hK, hmax, norm_liftProd_pos_of_zero_floor_max D a hne hΩ hmax, henergy⟩

/-- Some zero-floor norm maximizer has unit normalized output and the single-split
excitation-energy bound. Normalization occurs only after positivity of the output norm.

**Scope restriction (weights and coefficient):** This consequence retains the
`a ≤ 1/2` and coarse dimension coefficient of the homogeneous theorem, rather than
OpenAI's full `EnergyOptimizer.lean`, lines 62–109, conclusion. See
`docs/paper-gaps/oai26_zero_floor_energy_scope.tex` for the sharp positive-floor
estimate and source-representation comparison still required. -/
theorem exists_max_feasible_chain_zero_floor_normalized_energy (D : ℕ → Finset V)
    (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha2 : ∀ j, a j ≤ 1 / 2)
    {Ω : EuclideanSpace ℂ (SiteConfig n)} (hΩ : Ω ≠ 0)
    {ι : Type*} [Fintype ι] (h : ι → Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (S : ι → Finset V) (hsupp : ∀ i, IsSupportedOn (h i) (S i))
    (hherm : ∀ i, (h i).IsHermitian) {c₀ : ℝ} (hnorm : ∀ i, ‖h i‖ ≤ c₀)
    (hsingle : ∀ i, ∀ j ∈ splitIndices (S i) D m,
      ∀ j' ∈ splitIndices (S i) D m, j = j')
    {E₀ : ℝ} (heig : toEuclideanLin (∑ i, h i) Ω = (E₀ : ℂ) • Ω) :
    ∃ K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
      (∀ j : Fin m, IsFeasibleFilter 0 (a j) (K j)) ∧
      (∀ K' : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
        (∀ j : Fin m, IsFeasibleFilter 0 (a j) (K' j)) →
        ‖toEuclideanLin (liftProd (chainList D K' fun _ ↦ True)) Ω‖ ≤
          ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖) ∧
      let ψ := toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω
      let φ := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
      0 < ‖ψ‖ ∧ ‖φ‖ = 1 ∧ (⟪φ, toEuclideanLin (∑ i, h i) φ⟫_ℂ).re - E₀ ≤
        ∑ j : Fin m, 4 * a j ^ 2 *
          ∑ i ∈ crossingTerms S (D j), supportDim n (S i) ^ 2 * c₀ := by
  obtain ⟨K, hK, hmax, hpos, henergy⟩ := exists_max_feasible_chain_zero_floor_energy
    D hD a ha ha2 hΩ h S hsupp hherm hnorm hsingle heig
  refine ⟨K, hK, hmax, hpos, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hpos.ne']
  · exact (normalized_energy_le_iff _ (norm_pos_iff.mp hpos) _ _).mpr henergy

end Entropy
