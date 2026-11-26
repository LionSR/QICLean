/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.NormComparison.Data
import QICLean.Representation.Bell.LabelDimensionRemainder
import QICLean.Analysis.Parameter.RoughLowerCoefficient
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# The four norm comparisons for a status family

The rough upper, rough lower, sharp upper and sharp lower comparisons of the area-law paper,
Proposition 8.1, for the band product of a status family on a finite product system. Each is
the corresponding comparison for nested regional metrics, read through the band factorization
of the mean-tree root. Each remainder is uniform in the tree, its terminal probabilities and
the isometric coordinates of the symmetric space; the lower comparisons are uniform in the
symmetric vector carrying the common label.

## Main results

* `ManyBody.NormComparison.exists_rough_upper`: `comparator:rough-upper`.
* `ManyBody.NormComparison.exists_rough_lower`: `comparator:rough-lower`, coefficient four.
* `ManyBody.NormComparison.exists_sharp_upper`: `comparator:sharp-upper`.
* `ManyBody.NormComparison.exists_sharp_lower`: `comparator:sharp-lower`.
* `ManyBody.NormComparison.ComparatorsStatement`, `ManyBody.NormComparison.comparatorsStatement`:
  upper and lower norm comparisons from an auxiliary pair.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Proposition 8.1 (`prop:comparators`), `07-comparators.tex`, lines 154–214, 332–418 and
550–651, revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The proofs are written from the
manuscript; no Lean declaration of the accompanying development is reused.
-/

section Bounds

noncomputable section

open Filter Topology Matrix TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  symmDiff
namespace ManyBody.NormComparison

/-- A band-and-tree average times the total weight is the weight times the weighted sum. -/
private theorem mul_avg_eq {St : Type} [Fintype St] [DecidableEq St] {K : ℕ} (a : ℝ)
    (T : MeanTree St) (f : St → Fin K → ℝ) :
    a * K * ((1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * f j l) = a * ∑ l, ∑ j, T.weight j * f j l := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · field_simp

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (β : ι → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

open Classical in
/-- The rough lower comparison `comparator:rough-lower` (`07-comparators.tex`,
lines 162–169 and 585–651) for the band product of a status family, with coefficient four
and one remainder for every tree, isometric coordinates and symmetric vector of norm at
most one carrying the label `λ_k` on both auxiliary systems. Neither prefix nor moment
data are used. -/
theorem exists_rough_lower [∀ v, Nonempty (β v)]
    (H : Matrix ((v : ι) → β v) ((v : ι) → β v) ℂ) (Ω : EuclideanSpace ℂ ((v : ι) → β v))
    (E₀ gap : ℝ) (hgap : (H - (E₀ : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ω.ofLp (star Ω.ofLp))).PosSemidef)
    (hΩ : ‖Ω‖ = 1) (hgap_pos : 0 < gap) {d : ℕ} [NeZero d]
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (hSent : 0 ≤ Sent)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) * Sent) (fun k : ℕ ↦ (k : ℝ)))
    {St : Type} [Finite St] {K : ℕ} (X : Finset ι)
    (U Y V : St → Fin K → Finset ι) (hfam : IsStatusFamily X U Y V)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
      ∀ (n : ℕ) (Z : Matrix (TensorPower.Config k (siteSpace β d)) (Fin n) ℂ),
        Zᴴ * Z = 1 →
        Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) →
        ∀ (T : MeanTree St) (ξ : EuclideanSpace ℂ (TensorPower.Config k (siteSpace β d))),
        ξ ≠ 0 → ‖ξ‖ ≤ 1 →
        symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) *ᵥ ξ = ξ →
        labelProj (subsystemPerm k (siteSpace β d) {some none}) (ell k) *ᵥ ξ = ξ →
        labelProj (subsystemPerm k (siteSpace β d) {none}) (ell k) *ᵥ ξ = ξ →
        let w := toEuclideanLin ((meanRoot β d k (a / 2) X U Y V Z T) ^ (-(1 / 4 : ℝ)))
          (toEuclideanLin Zᴴ ξ)
        let N := ‖w‖
        let v := toEuclideanLin Z ((N⁻¹ : ℂ) • w)
        let Edef := ((star v ⬝ᵥ
          (globalReplicaMeanHamiltonian β (Fin d) (Fin d) H k *ᵥ v)).re - E₀) / gap
        0 < N ∧ ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
          2 * (1 / 4) * (a * K) * (2 * Sent - 4 * (τ * Real.log d + Real.binEntropy τ / a) -
              4 * (Edef / τ) * Sent) -
            ρ k ≤ -Real.log (N ^ 2) / k := by
  classical
  have := Fintype.ofFinite St
  obtain ⟨c, Cf, hc, hCf, hlow⟩ :=
    exists_replicaMetric_symProj_bandProduct_rough_lower_norm β (Fin d) (Fin d)
      (t := a / 2) (by positivity) (by linarith)
  refine ⟨roughLowerRemainderAtWeight K a c Cf ell Sent,
    tendsto_roughLowerRemainderAtWeight_of_label_dimension ell Sent hdim K a c Cf, ?_⟩
  intro k hk n Z hZ hZZ T ξ hξ hξn hsym hC hR
  have hroot := meanRoot_eq_listProd β (le_of_lt (half_pos ha)) X U Y V
    hfam.disjoint_inner_middle hfam.far_eq_compl hfam.nesting Z hZ hZZ T
    (fun j l ↦ insert none (((X ∪ U j l ∪ Y j l)ᶜ).image fun x ↦ some (some x)))
    (fun j l ↦ (Y j l).image fun x ↦ some (some x))
    (fun j l ↦ by rw [hfam.far_eq_compl j l]) (fun _ _ ↦ rfl)
  rw [hroot]
  intro w N v Edef
  have hΩ' : ‖WithLp.toLp 2 Ω.ofLp‖ = 1 := by simpa using hΩ
  obtain ⟨hw, -, hδ, hτb⟩ := hlow k n hk H Ω.ofLp E₀ gap hgap hΩ' hgap_pos Z hZ hZZ St K
    (fun j l ↦ X ∪ U j l) Y hfam.disjoint_inner_middle hfam.nesting T (ell k) (ell k) Sent
    (labelDimensionDefect ell Sent k) (1 / 4)
    (labelDimensionDefect_label_bound ell Sent k).2 (by norm_num)
    ξ hξ hξn hsym hC hR
  refine ⟨norm_pos_iff.mpr hw, fun τ hτ hτ1 ↦ ?_⟩
  have h1 := hτb τ hτ hτ1.le
  simp only [Fintype.card_fin] at h1
  have hb : |Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)| =
      Cf * Real.log ((k : ℝ) + 2) + Real.log 2 := by
    have hlog : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
    rw [Real.log_div (by positivity) two_ne_zero, Real.log_rpow (by positivity),
      abs_of_nonpos (by nlinarith [Real.log_pos (one_lt_two : (1 : ℝ) < 2)])]
    ring
  rw [hb] at h1
  have hrem : roughLowerRemainderAtWeight K a c Cf ell Sent k =
      (K / 2 * (2 * |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
        2 * (a / 2) * labelDimensionDefect ell Sent k| +
        (Cf * Real.log ((k : ℝ) + 2) + Real.log 2) + Real.log 2 + Real.log (3 / 2))) / k := by
    rw [roughLowerRemainderAtWeight, show 2 * (a / 2) = a by ring]
    ring
  rw [hrem]
  exact Real.rough_lower_coefficient_four_div K a k Sent (Real.log d) (Real.binEntropy τ) Edef τ _ _
    (Nat.cast_nonneg K) ha (by linarith) (Nat.cast_pos.mpr hk) hSent
    (Real.log_natCast_nonneg d) (Real.binEntropy_nonneg hτ.le (by linarith)) hδ hτ h1

open Classical in
/-- The rough upper comparison `comparator:rough-upper` (`07-comparators.tex`,
lines 154–161 and 332–381) for `pre_k` under the prefix data, with a remainder uniform in the
tree and the isometric coordinates. -/
theorem exists_rough_upper (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (hΩ : ‖Ω‖ = 1)
    [∀ v, Nonempty (β v)] (X : Finset ι) (E : Finset (ManyBody.RegionConfig β X))
    [NeZero E.card]
    (hz : 0 < (ManyBody.regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass
      E)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    (hmass :
      let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv β X) Ω
      let ψ : ManyBody.ComplConfig β X × Fin E.card → ℂ := fun x ↦
        compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
      ∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → ManyBody.ComplConfig β X)
              (Fin k → ManyBody.ComplConfig β X) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
              (fun x : (Fin k → ManyBody.ComplConfig β X) ×
                (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2)
    {St : Type} [Finite St] {K : ℕ}
    (U Y V : St → Fin K → Finset ι) (hfam : IsStatusFamily X U Y V)
    (a : ℝ) (ha : 0 < a) (R : Finset (Finset ι)) (Bsh Bexc : ℝ)
    (hpre : IsPrefixData β Ω X U Y R Bsh Bexc) :
    let d := E.card
    let z := ∑ i ∈ E, (ManyBody.regionState_posSemidef X Ω).isHermitian.eigenvalues i
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (n : ℕ) (Z : Matrix (TensorPower.Config k (siteSpace β d)) (Fin n) ℂ),
        Zᴴ * Z = 1 →
        Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) →
        ∀ T : MeanTree St,
        let N := ‖toEuclideanLin ((meanRoot β d k (a / 2) X U Y V Z T) ^ (-(1 / 4 : ℝ)))
          (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖
        0 < N ∧ -Real.log (N ^ 2) / k ≤
          2 * Real.log d - Real.log z + 2 * (1 / 4) * (a * K) * (2 * Bsh / z + 2 * Bexc) +
            ρ k := by
  intro d z
  have hu := ManyBody.eventually_suppliedReplicaPrevector_rough_upper (S := St) β Ω X E
    hΩ hz R.toList
    (List.pairwise_of_forall_mem_list fun B hB B' hB' ↦
      hpre.nested B (Finset.mem_toList.mp hB) B' (Finset.mem_toList.mp hB'))
    (fun B hB ↦ hpre.disjoint B (Finset.mem_toList.mp hB)) ell (t := a / 2) (half_pos ha)
    (hmass.mono fun k hk ↦ by
      simpa only [Nat.cast_pow, one_div,
        TensorPower.norm_sq_labelProj_compressedTypicalSite_prod β X k Ω E (ell k)] using! hk)
  obtain ⟨c, hc, hu⟩ := hu
  refine ⟨Real.bellOverlapRemainder d c K, Real.tendsto_bellOverlapRemainder d c K,
    hu.mono fun k hk n Z hZ hZZ T ↦ ?_⟩
  have hY : ∀ j l, Y j l \ X = Y j l := fun j l ↦
    Finset.sdiff_eq_self_of_disjoint (hfam.disjoint_XY j l).symm
  have hroot := meanRoot_eq_listProd β (le_of_lt (half_pos ha)) X U Y V
    hfam.disjoint_inner_middle hfam.far_eq_compl hfam.nesting Z hZ hZZ T
    (fun j l ↦ insert none (((X ∪ (U j l ∪ Y j l))ᶜ).image fun x ↦ some (some x)))
    (fun j l ↦ (Y j l \ X).image fun x ↦ some (some x))
    (fun j l ↦ by rw [hfam.far_eq_compl j l, Finset.union_assoc]) (fun j l ↦ by rw [hY j l])
  intro N
  obtain ⟨hpos, hle⟩ := hk n Z hZ hZZ K U Y hfam.disjoint_UY hfam.union_subset_later
    (fun j l ↦ Finset.disjoint_union_right.mpr ⟨hfam.disjoint_XU j l, hfam.disjoint_XY j l⟩)
    T Bsh Bexc (fun B hB ↦ hpre.entropy_le B (Finset.mem_toList.mp hB))
    (fun j l Q hQ ↦ by
      obtain ⟨B, hB, hBQ⟩ := hpre.matched j l Q hQ
      exact ⟨B, Finset.mem_toList.mpr hB, hBQ⟩)
    (1 / 4) (by norm_num)
  have hN : N ^ 2 = ‖toEuclideanLin ((List.ofFn fun l ↦ T.eval fun j ↦ Zᴴ *
      ((replicaMetric (siteSpace β d) (a / 2) k
        (insert (some none) ((X ∪ U j l).image fun x ↦ some (some x))))⁻¹ *
        (replicaMetric (siteSpace β d) (a / 2) k
          (insert none (((X ∪ (U j l ∪ Y j l))ᶜ).image fun x ↦ some (some x))))⁻¹ *
        replicaMetric (siteSpace β d) (a / 2) k ((Y j l \ X).image fun x ↦ some (some x))) ^ 2 *
        Z).prod ^ (-(1 / 4 : ℝ))) (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖ ^ 2 := by
    simp only [N, hroot]
  refine ⟨?_, ?_⟩
  · have hsq : 0 < N ^ 2 := hN ▸ hpos
    have hN0 : 0 ≤ N := norm_nonneg _
    exact lt_of_le_of_ne hN0 fun h ↦ by rw [← h] at hsq; simp at hsq
  · rw [hN]
    have hcoef : 8 * (1 / 4 : ℝ) * (a / 2) * (K : ℝ) * (Bsh / z + Bexc) =
        2 * (1 / 4) * (a * K) * (2 * Bsh / z + 2 * Bexc) := by ring
    rw [← hcoef]
    exact hle

open Classical in
/-- The sharp upper comparison `comparator:sharp-upper` (`07-comparators.tex`,
lines 171–188 and 383–418) for `pre_k` under the moment data, without prefix data, with a
remainder uniform in the tree and the isometric coordinates. -/
theorem exists_sharp_upper (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (hΩ : ‖Ω‖ = 1)
    [∀ v, Nonempty (β v)] (X : Finset ι) (E : Finset (ManyBody.RegionConfig β X))
    [NeZero E.card]
    (hz : 0 < (ManyBody.regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass
      E)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    (hmass :
      let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv β X) Ω
      let ψ : ManyBody.ComplConfig β X × Fin E.card → ℂ := fun x ↦
        compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
      ∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → ManyBody.ComplConfig β X)
              (Fin k → ManyBody.ComplConfig β X) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
              (fun x : (Fin k → ManyBody.ComplConfig β X) ×
                (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2)
    {St : Type} [Fintype St] [DecidableEq St] {K : ℕ}
    (U Y V : St → Fin K → Finset ι) (hfam : IsStatusFamily X U Y V)
    (C₀ c₀ B C' : ℝ) (hC' : 12 * C₀ ≤ C') (hC'1 : 1 ≤ C')
    (hmom : IsMarginalMomentData β Ω X U Y V C₀ c₀ B)
    (a : ℝ) (ha : 0 < a) (har : 6 * a ≤ c₀ / Real.sqrt B) (ha1 : 6 * a ≤ 1) :
    let d := E.card
    let z := ∑ i ∈ E, (ManyBody.regionState_posSemidef X Ω).isHermitian.eigenvalues i
    let S := ManyBody.regionEntropy Ω
    let gpost := fun j l ↦ S (U j l) + S (U j l ∪ Y j l) - S (Y j l)
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (n : ℕ) (Z : Matrix (TensorPower.Config k (siteSpace β d)) (Fin n) ℂ),
        Zᴴ * Z = 1 →
        Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) →
        ∀ T : MeanTree St,
        let N := ‖toEuclideanLin ((meanRoot β d k (a / 2) X U Y V Z T) ^ (-(1 / 4 : ℝ)))
          (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖
        0 < N ∧ -Real.log (N ^ 2) / k ≤
          2 * Real.log d - Real.log z +
            2 * (1 / 4) * (a * K) * ((1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * gpost j l +
              C' * (a * B + |Real.log z| / a)) + ρ k := by
  intro d z S gpost
  obtain ⟨c, hc, hlim, hu⟩ := ManyBody.eventually_suppliedReplicaPrevector_sharp_upper β Ω X E
    hΩ hz (K := C₀ * B) (r := c₀ / Real.sqrt B) ha har ha1 ell hmass
  refine ⟨Real.bellOverlapRemainder d c K, hlim K, hu.mono fun k hk n Z hZ hZZ T ↦ ?_⟩
  have hY : ∀ j l, Y j l \ X = Y j l := fun j l ↦
    Finset.sdiff_eq_self_of_disjoint (hfam.disjoint_XY j l).symm
  have hroot := meanRoot_eq_listProd β (le_of_lt (half_pos ha)) X U Y V
    hfam.disjoint_inner_middle hfam.far_eq_compl hfam.nesting Z hZ hZZ T
    (fun j l ↦ insert none (((X ∪ (U j l ∪ Y j l))ᶜ).image fun x ↦ some (some x)))
    (fun j l ↦ (Y j l \ X).image fun x ↦ some (some x))
    (fun j l ↦ by rw [hfam.far_eq_compl j l, Finset.union_assoc]) (fun j l ↦ by rw [hY j l])
  intro N
  obtain ⟨hpos, hle⟩ := hk n Z hZ hZZ K U Y hfam.disjoint_XU hfam.disjoint_XY
    hfam.disjoint_UY hfam.union_subset_later
    (fun j l Q hQ u hu ↦ hmom.surprisalMoment_le β j l Q (by tauto) u hu)
    T (1 / 4) (by norm_num)
  have hN : N ^ 2 = ‖toEuclideanLin ((List.ofFn fun l ↦ T.eval fun j ↦ Zᴴ *
      ((replicaMetric (siteSpace β d) (a / 2) k
        (insert (some none) ((X ∪ U j l).image fun x ↦ some (some x))))⁻¹ *
        (replicaMetric (siteSpace β d) (a / 2) k
          (insert none (((X ∪ (U j l ∪ Y j l))ᶜ).image fun x ↦ some (some x))))⁻¹ *
        replicaMetric (siteSpace β d) (a / 2) k ((Y j l \ X).image fun x ↦ some (some x))) ^ 2 *
        Z).prod ^ (-(1 / 4 : ℝ))) (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖ ^ 2 := by
    simp only [N, hroot]
  refine ⟨?_, ?_⟩
  · have hsq : 0 < N ^ 2 := hN ▸ hpos
    have hN0 : 0 ≤ N := norm_nonneg _
    exact lt_of_le_of_ne hN0 fun h ↦ by rw [← h] at hsq; simp at hsq
  · rw [hN]
    refine le_trans (b := 2 * Real.log d - Real.log z +
      2 * (1 / 4) * a * (∑ l, ∑ j, T.weight j * gpost j l) +
        24 * (1 / 4) * K * (C₀ * B) * a ^ 2 - 2 * (1 / 4) * K * Real.log z +
          Real.bellOverlapRemainder d c K k) hle ?_
    have havg := mul_avg_eq a T gpost
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hB0 : 0 ≤ B := zero_le_one.trans hmom.one_le
    have h1 : 24 * (1 / 4 : ℝ) * K * (C₀ * B) * a ^ 2 ≤
        2 * (1 / 4) * (a * K) * (C' * (a * B)) := by
      have : 0 ≤ (K : ℝ) * B * a ^ 2 := by positivity
      nlinarith
    have h2 : -(2 * (1 / 4 : ℝ) * K * Real.log z) ≤
        2 * (1 / 4) * (a * K) * (C' * (|Real.log z| / a)) := by
      have heq : 2 * (1 / 4) * (a * K) * (C' * (|Real.log z| / a)) =
          (1 / 2) * K * (C' * |Real.log z|) := by field_simp; ring
      rw [heq]
      have h3 := mul_nonneg (mul_nonneg hK0 (abs_nonneg (Real.log z))) (sub_nonneg.mpr hC'1)
      have h4 := mul_le_mul_of_nonneg_left (neg_le_abs (Real.log z)) hK0
      nlinarith
    have hsplit : 2 * (1 / 4) * (a * K) * ((1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * gpost j l +
        C' * (a * B + |Real.log z| / a)) = 2 * (1 / 4) * a * (∑ l, ∑ j, T.weight j * gpost j l) +
          2 * (1 / 4) * (a * K) * (C' * (a * B)) +
          2 * (1 / 4) * (a * K) * (C' * (|Real.log z| / a)) := by
      have : 2 * (1 / 4) * (a * K) * ((1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * gpost j l) =
          2 * (1 / 4) * a * (∑ l, ∑ j, T.weight j * gpost j l) := by
        rw [mul_assoc (2 * (1 / 4 : ℝ)), havg]
        ring
      rw [mul_add, this, mul_add]
      ring
    rw [hsplit]
    linarith

open Classical in
/-- The sharp lower comparison `comparator:sharp-lower` (`07-comparators.tex`,
lines 171–196 and 550–651) under the moment data, with one remainder for every tree,
isometric coordinates and symmetric vector of norm at most one carrying the label `λ_k` on
both auxiliary systems. The maximum `g_max` runs over the leaf labels of the tree. -/
theorem exists_sharp_lower [∀ v, Nonempty (β v)]
    (H : Matrix ((v : ι) → β v) ((v : ι) → β v) ℂ) (Ω : EuclideanSpace ℂ ((v : ι) → β v))
    (E₀ gap : ℝ) (hgap : (H - (E₀ : ℂ) • 1 -
      (gap : ℂ) • (1 - vecMulVec Ω.ofLp (star Ω.ofLp))).PosSemidef)
    (hΩ : ‖Ω‖ = 1) (hgap_pos : 0 < gap) {d : ℕ} [NeZero d]
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (hSent : 0 ≤ Sent)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) * Sent) (fun k : ℕ ↦ (k : ℝ)))
    {St : Type} [Fintype St] [DecidableEq St] {K : ℕ} (X : Finset ι)
    (U Y V : St → Fin K → Finset ι) (hfam : IsStatusFamily X U Y V)
    (C₀ c₀ B C' : ℝ) (hC₀ : 0 ≤ C₀) (hC'4 : 4 ≤ C') (hC'0 : 25 * C₀ ≤ C')
    (hmom : IsMarginalMomentData β Ω X U Y V C₀ c₀ B)
    (a : ℝ) (ha : 0 < a) (har : 10 * a ≤ c₀ / Real.sqrt B) (ha1 : 10 * a ≤ 1) :
    let S := ManyBody.regionEntropy Ω
    let gpre := fun j l ↦ S (X ∪ U j l) + S (V j l) - S (Y j l)
    ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
      ∀ (n : ℕ) (Z : Matrix (TensorPower.Config k (siteSpace β d)) (Fin n) ℂ),
        Zᴴ * Z = 1 →
        Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) →
        ∀ (T : MeanTree St) (ξ : EuclideanSpace ℂ (TensorPower.Config k (siteSpace β d))),
        ξ ≠ 0 → ‖ξ‖ ≤ 1 →
        symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k) *ᵥ ξ = ξ →
        labelProj (subsystemPerm k (siteSpace β d) {some none}) (ell k) *ᵥ ξ = ξ →
        labelProj (subsystemPerm k (siteSpace β d) {none}) (ell k) *ᵥ ξ = ξ →
        let gmax := (insert (0 : ℝ) ((Finset.univ : Finset (T.labels.toFinset × Fin K)).image
          fun x ↦ gpre x.1.val x.2)).max' (Finset.insert_nonempty _ _)
        let w := toEuclideanLin ((meanRoot β d k (a / 2) X U Y V Z T) ^ (-(1 / 4 : ℝ)))
          (toEuclideanLin Zᴴ ξ)
        let N := ‖w‖
        let v := toEuclideanLin Z ((N⁻¹ : ℂ) • w)
        let Edef := ((star v ⬝ᵥ
          (globalReplicaMeanHamiltonian β (Fin d) (Fin d) H k *ᵥ v)).re - E₀) / gap
        0 < N ∧ ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
          2 * (1 / 4) * (a * K) * (2 * Sent + (1 - τ) *
              ((1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * gpre j l) -
              C' * (τ * Real.log d + Real.binEntropy τ / a + a * B) -
              C' * (Edef / τ) * (Sent + gmax)) - ρ k ≤ -Real.log (N ^ 2) / k := by
  intro S gpre
  obtain ⟨c, Cf, hc, hCf, hlow⟩ :=
    exists_replicaMetric_symProj_bandProduct_sharp_lower_norm β (Fin d) (Fin d)
      (t := a / 2) (half_pos ha)
  refine ⟨roughLowerRemainderAtWeight K a c Cf ell Sent,
    tendsto_roughLowerRemainderAtWeight_of_label_dimension ell Sent hdim K a c Cf, ?_⟩
  intro k hk n Z hZ hZZ T ξ hξ hξn hsym hC hR
  let T' := T.restrict T.labels.toFinset fun _ hj ↦ List.mem_toFinset.mpr hj
  have hroot := meanRoot_eq_listProd β (le_of_lt (half_pos ha)) X U Y V
    hfam.disjoint_inner_middle hfam.far_eq_compl hfam.nesting Z hZ hZZ T
    (fun j l ↦ insert none (((X ∪ U j l ∪ Y j l)ᶜ).image fun x ↦ some (some x)))
    (fun j l ↦ (Y j l).image fun x ↦ some (some x))
    (fun j l ↦ by rw [hfam.far_eq_compl j l]) (fun _ _ ↦ rfl)
  simp only [← MeanTree.eval_restrict _ T.labels.toFinset T
    fun _ hj ↦ List.mem_toFinset.mpr hj] at hroot
  rw [hroot]
  intro gmax w N v Edef
  have hΩ' : ‖WithLp.toLp 2 Ω.ofLp‖ = 1 := by simpa using hΩ
  have hmomQ : ∀ (j : T.labels.toFinset) (l : Fin K) (b : Fin 3) (u : ℝ), |u| ≤ c₀ / Real.sqrt B →
      let Q := ManyBody.regionalPhysicalRegion (X ∪ U j.val l) (Y j.val l) b
      Real.log (Entropy.surprisalMoment (ManyBody.regionState_posSemidef
        Q (WithLp.toLp 2 Ω.ofLp)).isHermitian.eigenvalues u) ≤
          u * ManyBody.regionEntropy (WithLp.toLp 2 Ω.ofLp) Q + C₀ * B * u ^ 2 := by
    intro j l b u hu Q
    have hQ : Q = X ∪ U j.val l ∨ Q = V j.val l ∨ Q = Y j.val l ∨ Q = U j.val l ∨
        Q = U j.val l ∪ Y j.val l := by
      fin_cases b
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl (hfam.far_eq_compl j.val l).symm)
    exact hmom.surprisalMoment_le β j.val l Q hQ u hu
  obtain ⟨hw, -, hδ, hτb⟩ := hlow k n hk H Ω.ofLp E₀ gap hgap hΩ' hgap_pos Z hZ hZZ
    T.labels.toFinset K (fun j l ↦ X ∪ U j.val l) (fun j l ↦ Y j.val l)
    (fun j l ↦ hfam.disjoint_inner_middle j.val l)
    (fun j j' l l' hll ↦ hfam.nesting j.val j'.val l l' hll)
    (C₀ * B) (c₀ / Real.sqrt B) hmomQ (by linarith) (by linarith)
    (mul_nonneg hC₀ (zero_le_one.trans hmom.one_le)) T' (ell k) (ell k) Sent
    (labelDimensionDefect ell Sent k) (1 / 4)
    (labelDimensionDefect_label_bound ell Sent k).2 (by norm_num)
    ξ hξ hξn hsym hC hR
  refine ⟨norm_pos_iff.mpr hw, fun τ hτ hτ1 ↦ ?_⟩
  have h1 := hτb τ hτ hτ1.le
  let gmax' := (insert (0 : ℝ) ((Finset.univ : Finset (T.labels.toFinset × Fin K)).image
    fun x ↦ S (X ∪ U x.1.val x.2) + S ((X ∪ U x.1.val x.2 ∪ Y x.1.val x.2)ᶜ) -
      S (Y x.1.val x.2))).max' (Finset.insert_nonempty _ _)
  have h1' : 2 * (1 / 4) * ∑ l : Fin K, (2 * (a / 2) * k * ((2 * Sent + (1 - τ) *
      (∑ j : T.labels.toFinset, T'.weight j * (S (X ∪ U j.val l) +
        S ((X ∪ U j.val l ∪ Y j.val l)ᶜ) -
        S (Y j.val l))) - τ * (Real.log (Fintype.card (Fin d)) +
          Real.log (Fintype.card (Fin d))) - (3 + 1 / (2 * (a / 2))) * Real.binEntropy τ -
          50 * (C₀ * B) * (a / 2)) - Edef / τ * max 0 (2 * Sent + gmax')) -
      (2 * |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
        2 * (a / 2) * labelDimensionDefect ell Sent k| +
        |Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)| + Real.log 2 + Real.log (3 / 2))) ≤
      -Real.log (N ^ 2) := h1
  have hsum : ∀ l : Fin K, ∑ j : T.labels.toFinset, T'.weight j * (S (X ∪ U j.val l) +
      S ((X ∪ U j.val l ∪ Y j.val l)ᶜ) - S (Y j.val l)) = ∑ j, T.weight j * gpre j l :=
    fun l ↦ (MeanTree.sum_weight_restrict_mul T (fun j ↦ S (X ∪ U j l) +
      S ((X ∪ U j l ∪ Y j l)ᶜ) - S (Y j l))).trans
        (Finset.sum_congr rfl fun j _ ↦ by simp only [gpre, hfam.far_eq_compl])
  have hgm : gmax' = gmax := by simp only [gmax', gmax, gpre, hfam.far_eq_compl]
  have hb : |Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)| =
      Cf * Real.log ((k : ℝ) + 2) + Real.log 2 := by
    have hlog : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
    rw [Real.log_div (by positivity) two_ne_zero, Real.log_rpow (by positivity),
      abs_of_nonpos (by nlinarith [Real.log_pos (one_lt_two : (1 : ℝ) < 2)])]
    ring
  simp only [hsum, hgm, hb, Fintype.card_fin] at h1'
  have hrem : roughLowerRemainderAtWeight K a c Cf ell Sent k =
      (K / 2 * (2 * |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
        2 * (a / 2) * labelDimensionDefect ell Sent k| +
        (Cf * Real.log ((k : ℝ) + 2) + Real.log 2) + Real.log 2 + Real.log (3 / 2))) / k := by
    rw [roughLowerRemainderAtWeight, show 2 * (a / 2) = a by ring]
    ring
  have hgm0 : 0 ≤ gmax := Finset.le_max' _ 0 (Finset.mem_insert_self _ _)
  rw [hrem]
  exact Real.sharp_lower_coefficient_div a k Sent (Real.log d) τ (Real.binEntropy τ) Edef gmax
    C₀ B C' _ _
    (fun l ↦ ∑ j, T.weight j * gpre j l) ha (by linarith) (Nat.cast_pos.mpr hk) hSent
    (Real.log_natCast_nonneg d) (Real.binEntropy_nonneg hτ.le (by linarith)) hδ hτ hgm0
    (zero_le_one.trans hmom.one_le) hC'4 hC'0 h1'

end ManyBody.NormComparison

end

end Bounds

section Statement

/-!
## Upper and lower norm comparisons from an auxiliary pair

The norm comparisons of the area-law paper, Proposition 8.1, for a finite product system. A
unit ground vector of a positive gapped Hamiltonian, a physical target `X` and a typical
Schmidt set of `X` determine one sequence of common auxiliary labels. The projected vectors
`pre_k = π_R^{λ_k}(Ω ⊗ Bell_{CR})^{⊗k}` are nonzero, symmetric, of norm at most one,
exact mean-energy eigenvectors, and carry the same label on both auxiliary systems.
For every finite collection of nested status partitions, every weight `0 < a ≤ a₀`
and every mean tree, the inverse-power norm of the band product satisfies the rough
and sharp upper and lower comparisons, with remainders uniform in the tree, its
terminal probabilities and the symmetric coordinates. The entropy identity and the
nonnegativity of the pre-comparison entropy expression hold exactly.

The rough upper bound uses the nested prefix data; the rough lower bound uses neither
the prefix data nor the marginal moment data; both sharp bounds use the marginal moment
data and `a ≤ c / √𝓑`, and the sharp upper bound uses no prefix data. The rough
constant is universal, the sharp constant depends only on `C₀`, and the threshold `c`
depends only on `c₀`. The lower comparisons hold for every symmetric vector of norm at
most one carrying the common label on both auxiliary systems, in particular for
`pre_k`, with one remainder for all of them.

The physical sites carry arbitrary finite local spaces. The band factorization of the
mean-tree root is the commuting-band factorization of the leaves.

### Main definitions

* `ManyBody.NormComparison.ComparatorsStatement`: Proposition 8.1, with the data of
  `QICLean.ManyBody.Replica.NormComparison.Data`.

### Main result

* `ManyBody.NormComparison.comparatorsStatement`: Proposition 8.1 holds.

### References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Proposition 8.1 (`prop:comparators`), `07-comparators.tex`, lines 125–214, with the
standing data of lines 13–123. Source revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The proofs are written from the
manuscript; no Lean declaration of the accompanying development is reused.
-/

noncomputable section

open Filter Topology Matrix TensorPower PermutationRepresentation

open ManyBody (IsGapped groundSpace)
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  symmDiff
namespace ManyBody.NormComparison

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (β : ι → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

open Classical in
/-- **Proposition 8.1** (`prop:comparators`, `07-comparators.tex`, lines 125–214).

There are an absolute `a₀ > 0` and a universal rough constant `C`, and for all `C₀, c₀ > 0`
a sharp constant `C'` and a threshold `c > 0`, with the following property. Let `Ω` be the
unit ground vector, with energy `E₀` and gap `g > 0`, of a positive Hamiltonian `H` on a
finite product system (lines 15–19), let `X` be a physical target and `E` a typical Schmidt
set of width `w` (`comparator:typical-set`). Put `d_* = |E|`, `z = ∑_{i ∈ E} p_i` and
`S' = -∑_{i ∈ E} p'_i log p'_i`. There are common auxiliary labels `λ_k` such that
`pre_k = π_R^{λ_k}(Ω ⊗ Bell_{CR})^{⊗k} ∈ 𝒮_k` is nonzero, has norm at most one, is a
physical mean-energy eigenvector of eigenvalue `E₀` and has label `λ_k` on both `C` and `R`
(`comparator:prevector`, lines 131–142). The labels precede the statuses and the weight.

The entropy identity `comparator:entropy-identity` holds for every physical partition
(lines 198–202). For every finite status family obeying `comparator:nesting`,
`g^pre_{j,g} ≥ 0` (line 181), and for every `0 < a ≤ a₀`, with `t = a/2`, `s = 1/4` and
`W = aK` (lines 99–100), every mean tree with metrics `comparator:metrics`, `N = ‖𝓜^{-s} ξ‖`
and `E_def = (⟨v, Hbar v⟩ - E₀)/g` for `v = 𝓜^{-s} ξ / N` (lines 143–153):

* the rough upper bound `comparator:rough-upper` for `ξ = pre_k` holds under the prefix
  data (lines 154–161);
* the rough lower bound `comparator:rough-lower` holds for every `0 < τ < 1/2`, without
  the prefix or moment data (lines 162–169);
* under the moment data and `a ≤ c/√𝓑`, the sharp upper bound `comparator:sharp-upper` for
  `ξ = pre_k` holds without the prefix data, and the sharp lower bound
  `comparator:sharp-lower` holds for every `0 < τ < 1/2` (lines 171–197).

Every remainder `o_k(1)` is one sequence tending to zero, chosen with the physical system,
the auxiliary dimensions, the status family, `a` and the respective data fixed, and uniform
over the tree, its terminal probabilities, the isometric coordinates `Z` of the symmetric
space and, for the lower bounds, over every symmetric vector `ξ` of norm at most one with
label `λ_k` on both `C` and `R`, which includes `pre_k` (lines 205–213). The maximum
`g_max` is taken over the bands and the labels occurring at the leaves of the tree; since
`g^pre ≥ 0`, inserting `0` changes it only for `K = 0`. -/
def ComparatorsStatement : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 < C ∧
  ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ → ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (β : ι → Type) [∀ v, Fintype (β v)]
    [∀ v, DecidableEq (β v)] (H : Matrix ((v : ι) → β v) ((v : ι) → β v) ℂ)
    (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (E₀ gap : ℝ),
    H.PosSemidef → ‖Ω‖ = 1 → IsGapped H E₀ gap →
    groundSpace H E₀ = Submodule.span ℂ {Ω} → 0 < gap →
  ∀ (X : Finset ι) (E : Finset (ManyBody.RegionConfig β X)) (w : ℝ),
    IsTypicalSchmidtSet β Ω X E w →
    let p := (ManyBody.regionState_posSemidef X Ω).isHermitian.eigenvalues
    let S := ManyBody.regionEntropy Ω
    let z := ∑ i ∈ E, p i
    let d := E.card
    let S' := ∑ i ∈ E, Real.negMulLog (p i / z)
    let Hbar := fun k : ℕ ↦ globalReplicaMeanHamiltonian β (Fin d) (Fin d) H k
    let Psym := fun k : ℕ ↦ symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k)
    let LC := fun (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) ↦
      labelProj (subsystemPerm k (siteSpace β d) {some none}) l
    let LR := fun (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) ↦
      labelProj (subsystemPerm k (siteSpace β d) {none}) l
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let pre := prevector β Ω d ell k
        pre ≠ 0 ∧ ‖pre‖ ≤ 1 ∧ Psym k *ᵥ pre = pre ∧ Hbar k *ᵥ pre = (E₀ : ℂ) • pre.ofLp ∧
          LC k (ell k) *ᵥ pre = pre ∧ LR k (ell k) *ᵥ pre = pre) ∧
      (∀ U Y V : Finset ι, Disjoint X U → Disjoint X Y → Disjoint X V → Disjoint U Y →
        Disjoint U V → Disjoint Y V → X ∪ U ∪ Y ∪ V = Finset.univ →
        2 * S X + (S (X ∪ U) + S V - S Y) - (S U + S (U ∪ Y) - S Y) =
          ManyBody.regionMutualInformation Ω X V +
            ManyBody.regionMutualInformation Ω X (Y ∪ V)) ∧
      ∀ (St : Type) [Fintype St] [DecidableEq St] (K : ℕ) (U Y V : St → Fin K → Finset ι),
        IsStatusFamily X U Y V →
        let gpre := fun j l ↦ S (X ∪ U j l) + S (V j l) - S (Y j l)
        let gpost := fun j l ↦ S (U j l) + S (U j l ∪ Y j l) - S (Y j l)
        (∀ j l, 0 ≤ gpre j l) ∧
        ∀ a : ℝ, 0 < a → a ≤ a₀ →
        let s : ℝ := 1 / 4
        let t := a / 2
        let W := a * K
        let avg := fun (T : MeanTree St) (f : St → Fin K → ℝ) ↦
          (1 / (K : ℝ)) * ∑ l, ∑ j, T.weight j * f j l
        (∀ (R : Finset (Finset ι)) (Bsh Bexc : ℝ), IsPrefixData β Ω X U Y R Bsh Bexc →
          ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
            ∀ (n : ℕ) (Z : Matrix (TensorPower.Config k (siteSpace β d)) (Fin n) ℂ),
              Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ T : MeanTree St,
              let N := ‖toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
                (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖
              0 < N ∧ -Real.log (N ^ 2) / k ≤
                2 * Real.log d - Real.log z + 2 * s * W * (2 * Bsh / z + 2 * Bexc) + ρ k) ∧
        (∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
          ∀ (n : ℕ) (Z : Matrix (TensorPower.Config k (siteSpace β d)) (Fin n) ℂ),
            Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ (T : MeanTree St)
            (ξ : EuclideanSpace ℂ (TensorPower.Config k (siteSpace β d))), ξ ≠ 0 → ‖ξ‖ ≤ 1 →
            Psym k *ᵥ ξ = ξ → LC k (ell k) *ᵥ ξ = ξ → LR k (ell k) *ᵥ ξ = ξ →
            let w := toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
              (toEuclideanLin Zᴴ ξ)
            let N := ‖w‖
            let v := toEuclideanLin Z ((N⁻¹ : ℂ) • w)
            let Edef := ((star v ⬝ᵥ (Hbar k *ᵥ v)).re - E₀) / gap
            0 < N ∧ ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
              2 * s * W * (2 * S' - C * (τ * Real.log d + Real.binEntropy τ / a) -
                  C * (Edef / τ) * S') - ρ k ≤ -Real.log (N ^ 2) / k) ∧
        (∀ B : ℝ, IsMarginalMomentData β Ω X U Y V C₀ c₀ B → a ≤ c / Real.sqrt B →
          (∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k : ℕ in atTop,
            ∀ (n : ℕ) (Z : Matrix (TensorPower.Config k (siteSpace β d)) (Fin n) ℂ),
              Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ T : MeanTree St,
              let N := ‖toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
                (toEuclideanLin Zᴴ (prevector β Ω d ell k))‖
              0 < N ∧ -Real.log (N ^ 2) / k ≤
                2 * Real.log d - Real.log z +
                  2 * s * W * (avg T gpost + C' * (a * B + |Real.log z| / a)) + ρ k) ∧
          (∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧ ∀ k : ℕ, 0 < k →
            ∀ (n : ℕ) (Z : Matrix (TensorPower.Config k (siteSpace β d)) (Fin n) ℂ),
              Zᴴ * Z = 1 → Z * Zᴴ = Psym k → ∀ (T : MeanTree St)
              (ξ : EuclideanSpace ℂ (TensorPower.Config k (siteSpace β d))), ξ ≠ 0 → ‖ξ‖ ≤ 1 →
              Psym k *ᵥ ξ = ξ → LC k (ell k) *ᵥ ξ = ξ → LR k (ell k) *ᵥ ξ = ξ →
              let gmax := (insert (0 : ℝ) ((Finset.univ : Finset (T.labels.toFinset × Fin K)).image
                fun x ↦ gpre x.1.val x.2)).max' (Finset.insert_nonempty _ _)
              let w := toEuclideanLin ((meanRoot β d k t X U Y V Z T) ^ (-s))
                (toEuclideanLin Zᴴ ξ)
              let N := ‖w‖
              let v := toEuclideanLin Z ((N⁻¹ : ℂ) • w)
              let Edef := ((star v ⬝ᵥ (Hbar k *ᵥ v)).re - E₀) / gap
              0 < N ∧ ∀ τ : ℝ, 0 < τ → τ < 1 / 2 →
                2 * s * W * (2 * S' + (1 - τ) * avg T gpre -
                    C' * (τ * Real.log d + Real.binEntropy τ / a + a * B) -
                    C' * (Edef / τ) * (S' + gmax)) - ρ k ≤ -Real.log (N ^ 2) / k))

/-- **Proposition 8.1** (`prop:comparators`, `07-comparators.tex`, lines 125–214) holds,
with `a₀ = 1/10`, rough constant `4`, sharp constant `4 + 25 C₀` and threshold `c = c₀/10`. -/
theorem comparatorsStatement : ComparatorsStatement := by
  refine ⟨1 / 10, by norm_num, 4, by norm_num, fun C₀ c₀ hC₀ hc₀ ↦
    ⟨c₀ / 10, 4 + 25 * C₀, by positivity, by positivity, ?_⟩⟩
  intro ι _ _ β _ _ H Ω E₀ gap hHpos hΩ hgap hspan hgap_pos X E w htyp p S z d S' Hbar Psym LC LR
  have hE := ManyBody.mulVec_eq_of_groundSpace_eq_span hspan
  have hgapM := hgap.posSemidef_sub_smul_one hHpos.isHermitian hΩ hspan
  have hz : 0 < (ManyBody.regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass
      E := htyp.mass_pos
  have : NeZero d := ⟨htyp.nonempty.card_pos.ne'⟩
  have : NeZero E.card := ⟨htyp.nonempty.card_pos.ne'⟩
  have : ∀ v, Nonempty (β v) := fun v ↦ by
    by_contra hv
    rw [not_nonempty_iff] at hv
    have h0 : Ω = 0 := by
      ext x
      exact (hv.false (x v)).elim
    simp [h0] at hΩ
  obtain ⟨ell, hpre, hmass, hdim⟩ := exists_prevector_labels β H Ω E₀ hΩ hE X E hz
  rw [ManyBody.vonNeumannEntropy_compressedTypicalPureState_eq_sum β Ω X E hz] at hdim
  have hS' : 0 ≤ S' := Finset.sum_nonneg fun i hi ↦ Real.negMulLog_nonneg
    (div_nonneg ((ManyBody.regionState_posSemidef X Ω).eigenvalues_nonneg i) hz.le)
    ((div_le_one hz).mpr (Finset.single_le_sum (fun j _ ↦
      (ManyBody.regionState_posSemidef X Ω).eigenvalues_nonneg j) hi))
  refine ⟨ell, hpre, fun U Y V hXU hXY hXV hUY hUV hYV hc ↦
    ManyBody.auxiliaryPair_regionEntropyIdentity β Ω X U Y V hXU hXY hXV hUY hUV hYV hc, ?_⟩
  intro St _ _ K U Y V hfam gpre gpost
  refine ⟨fun j l ↦ ManyBody.auxiliaryPair_pre_nonneg β Ω hΩ X (U j l) (Y j l) (V j l)
    (hfam.disjoint_XY j l) (hfam.disjoint_XV j l) (hfam.disjoint_UY j l)
    (hfam.disjoint_UV j l) (hfam.disjoint_YV j l) (hfam.cover j l), ?_⟩
  intro a ha ha₀ s t W avg
  refine ⟨fun R Bsh Bexc hR ↦ exists_rough_upper β Ω hΩ X E hz ell hmass U Y V hfam a ha
      R Bsh Bexc hR,
    exists_rough_lower β H Ω E₀ gap hgapM hΩ hgap_pos ell S' hS' hdim X U Y V hfam a ha
      (by linarith), fun B hmom hac ↦ ?_⟩
  have hB : 0 < Real.sqrt B := Real.sqrt_pos.mpr (zero_lt_one.trans_le hmom.one_le)
  have h10 : 10 * a ≤ c₀ / Real.sqrt B := by
    rw [div_right_comm] at hac
    linarith
  exact ⟨exists_sharp_upper β Ω hΩ X E hz ell hmass U Y V hfam C₀ c₀ B (4 + 25 * C₀)
      (by linarith) (by linarith) hmom a ha (by linarith) (by linarith),
    exists_sharp_lower β H Ω E₀ gap hgapM hΩ hgap_pos ell S' hS' hdim X U Y V hfam
      C₀ c₀ B (4 + 25 * C₀) hC₀.le (by linarith) (by linarith) hmom a ha h10 (by linarith)⟩

end ManyBody.NormComparison

end

end Statement
