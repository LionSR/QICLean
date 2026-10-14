/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaPinnedMetricUpper
import QICLean.Representation.ReplicaLaminarBandMetrics
import QICLean.Representation.CompressedTypicalExponentialDomination
import QICLean.Representation.BellInsertionSymmetry
import QICLean.Entropy.TypicalBellPin
import QICLean.Entropy.IidSchurExponentialMoments
import QICLean.Entropy.FilterMoment
import QICLean.Analysis.WeightedTraceHolder

/-!
# A sharp upper estimate for one actual pinned replica factor

The three signed moments occur once each, on U, U ∪ Y, and Y. The trace
weight is the actual selected Bell postvector from the supplied physical
vector and the supplied positive-mass spectral selection. Three-factor
Hölder reduces their three inverse-mass powers to a single inverse-mass
power. The replica weights remain those of the original augmented family.

The coefficient of the quadratic error is 12 times the one-copy moment
coefficient. The only other dimensional cost is logarithmic in the copy
number. Its coefficient is selected before the copy number and the regions.
This result does not select an auxiliary sector or assemble a mean tree.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, 07-comparators.tex, lines 383–418, in particular
comparator:pinned-metric and comparator:sharp-upper, immutable revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently written from the manuscript; no upstream Lean text is reused.
-/

open Matrix PermutationRepresentation FiniteProduct
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace TensorPower

local instance replicaPinnedSharpLeafRegionDecidableEq
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (X : Finset V) : DecidableEq (Configuration β X) :=
  Fintype.decidablePiFintype

local instance replicaPinnedSharpLeafSiteDecidableEq
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (X : Finset V) (E : Finset (Configuration β X)) (f : Option (Option V)) :
    DecidableEq (addedSiteSpace (addedSiteSpace β E) (Fin E.card) f) := by
  cases f with
  | none => exact (inferInstance : DecidableEq (Fin E.card))
  | some f =>
    cases f with
    | none => exact (inferInstance : DecidableEq E)
    | some v => exact (inferInstance : DecidableEq (β v))

local instance replicaPinnedSharpLeafConfigDecidableEq
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (X : Finset V) (E : Finset (Configuration β X)) (k : ℕ) :
    DecidableEq (Config k (addedSiteSpace (addedSiteSpace β E) (Fin E.card))) := by
  let instCopy : DecidableEq ((f : Option (Option V)) →
      addedSiteSpace (addedSiteSpace β E) (Fin E.card) f) :=
    @Fintype.decidablePiFintype _ _ (replicaPinnedSharpLeafSiteDecidableEq β X E) inferInstance
  exact @Fintype.decidablePiFintype _ _ (fun _ ↦ instCopy) inferInstance

/-- Three-factor Hölder for the actual nested/disjoint label observables.
The trace weight need not be normalized or commute with the observables.
Source: OpenAI area-law manuscript, 07-comparators.tex, lines 405–412. -/
theorem re_trace_mul_exp_pinnedLabels_le
    {F : Type*} [Fintype F] [DecidableEq F]
    (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (k : ℕ) (U Y : Finset F) (hUY : Disjoint U Y)
    {ρ : Matrix (Config k ι) (Config k ι) ℂ} (hρ : ρ.PosSemidef) (a : ℝ) :
    let L := fun Q : Finset F ↦ labelEntropy (subsystemPerm k ι Q)
    (ρ * NormedSpace.exp ((a : ℂ) • (L U + L (U ∪ Y) - L Y))).trace.re ≤
      (ρ * NormedSpace.exp (((3 * a : ℝ) : ℂ) • L U)).trace.re ^ (1 / 3 : ℝ) *
      (ρ * NormedSpace.exp (((3 * a : ℝ) : ℂ) • L (U ∪ Y))).trace.re ^ (1 / 3 : ℝ) *
      (ρ * NormedSpace.exp (((-3 * a : ℝ) : ℂ) • L Y)).trace.re ^ (1 / 3 : ℝ) := by
  classical
  intro L
  let A : Fin 3 → Matrix (Config k ι) (Config k ι) ℂ := ![L U, L (U ∪ Y), -L Y]
  have hL (Q : Finset F) : (L Q).IsHermitian := isHermitian_labelObservable _ _
  have hA (i : Fin 3) : (A i).IsHermitian := by
    fin_cases i
    · exact hL U
    · exact hL (U ∪ Y)
    · exact (hL Y).neg
  have hUV : Commute (L U) (L (U ∪ Y)) :=
    commute_labelObservables_subsystemPerm_of_laminar ι k
      (Or.inl Finset.subset_union_left) _ _
  have hUY' : Commute (L U) (L Y) :=
    commute_labelObservables_subsystemPerm_of_laminar ι k
      (Or.inr (Or.inr hUY)) _ _
  have hVY : Commute (L (U ∪ Y)) (L Y) :=
    commute_labelObservables_subsystemPerm_of_laminar ι k
      (Or.inr (Or.inl Finset.subset_union_right)) _ _
  have hcomm (i j : Fin 3) : Commute (A i) (A j) := by
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · exact hUV
    · exact hUY'.neg_right
    · exact hUV.symm
    · exact Commute.refl _
    · exact hVY.neg_right
    · exact hUY'.symm.neg_left
    · exact hVY.symm.neg_left
    · exact Commute.refl _
  have h := hρ.re_trace_mul_exp_sum_le_prod 2 A hA hcomm a
  simpa [A, Fin.sum_univ_succ, Fin.prod_univ_succ, sub_eq_add_neg,
    neg_smul, smul_neg, Complex.ofReal_neg, add_assoc, mul_assoc] using h

private theorem exp_smul_labelEntropy_eq_labelObservable
    {G n : Type*} [Group G] [Fintype G] [Fintype n] [DecidableEq n]
    (φ : G →* Equiv.Perm n) (u : ℝ) :
    NormedSpace.exp ((u : ℂ) • labelEntropy φ) =
      labelObservable φ (fun l ↦ Real.exp (u * Real.log l.dim)) := by
  rw [labelEntropy, labelObservable_eq_hom, ← map_smul,
    Matrix.IsOrthogonalResolution.exp_hom, labelObservable_eq_hom]
  congr 1
  funext l
  simp only [Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_exp]

/-- The original exterior exponential expectation is exactly the compressed
expectation after the literal Bell insertion. Only the label observable is
transported; this theorem does not replace the original replica weights.
Source: OpenAI area-law manuscript, 07-comparators.tex, lines 299–308 and 405–412. -/
theorem re_inner_exp_labelEntropy_bellInsertion
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (X : Finset V) (C R : Type) [Fintype C] [DecidableEq C]
    [Fintype R] [DecidableEq R] (k : ℕ)
    (b : Configuration β X × C → ℂ) (hb : ‖WithLp.toLp 2 b‖ = 1)
    (Ψ : EuclideanSpace ℂ (Config k (compressedSiteSpace β X R)))
    (Q : Finset V) (u : ℝ) :
    let ι₀ := addedSiteSpace (addedSiteSpace β C) R
    let J := (addedSiteInsertion (compressedSiteSpace β X R)
      (Configuration β X × C) k b).submatrix (bellInsertionCopyEquiv β X C R k) id
    let p := WithLp.toLp 2 (J *ᵥ WithLp.ofLp Ψ)
    (⟪p, Matrix.toEuclideanLin (NormedSpace.exp ((u : ℂ) •
      labelEntropy (subsystemPerm k ι₀ ((Q \ X).image fun v ↦ some (some v))))) p⟫_ℂ).re =
    (⟪Ψ, Matrix.toEuclideanLin (NormedSpace.exp ((u : ℂ) •
      labelEntropy (subsystemPerm k (compressedSiteSpace β X R)
        (exteriorRegion X Q)))) Ψ⟫_ℂ).re := by
  classical
  intro ι₀ J p
  have hJ : Jᴴ * J = 1 := isIsometry_bellInsertion β X C R k b hb
  have hE := labelObservable_mul_bellInsertion_exterior β X C R k Q
    (fun l ↦ Real.exp (u * Real.log l.dim)) b
  rw [← exp_smul_labelEntropy_eq_labelObservable,
    ← exp_smul_labelEntropy_eq_labelObservable] at hE
  simp only [p, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply]
  rw [dotProduct_comm _ (star (J *ᵥ WithLp.ofLp Ψ)), Matrix.star_mulVec,
    ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hE,
    ← Matrix.mul_assoc, hJ, Matrix.one_mul, dotProduct_comm]

private theorem re_inner_exp_labelEntropy_selectedBellPost_le
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X Q : Finset V)
    (hXQ : Disjoint X Q) (E : Finset (Configuration β X))
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    (k : ℕ) (u : ℝ) :
    let z := (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
    let χ : Fin E.card × Configuration β Xᶜ → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
    let Ψ := WithLp.toLp 2
      (fun x : Config k (compressedSiteSpace β X (Fin E.card)) ↦
        ∏ j, χ (Equiv.piOptionEquivProd (x j)))
    let ι₀ := addedSiteSpace (addedSiteSpace β E) (Fin E.card)
    let b : Configuration β X × E → ℂ := Matrix.selectedBellVector ΩX E
    let J := (addedSiteInsertion (compressedSiteSpace β X (Fin E.card))
      (Configuration β X × E) k b).submatrix
        (bellInsertionCopyEquiv β X E (Fin E.card) k) id
    let p := WithLp.toLp 2 (J *ᵥ WithLp.ofLp Ψ)
    (⟪p, Matrix.toEuclideanLin (NormedSpace.exp ((u : ℂ) •
      labelEntropy (subsystemPerm k ι₀ ((Q \ X).image fun v ↦ some (some v))))) p⟫_ℂ).re ≤
      z⁻¹ ^ k * (Matrix.finKronecker (fun _ : Fin k ↦ reducedPure β Ω Q) *
        NormedSpace.exp ((u : ℂ) • labelEntropy (copyPerm (Configuration β Q) k))).trace.re := by
  classical
  intro z ΩX χ Ψ ι₀ b J p
  have hzX : 0 < Matrix.IsHermitian.spectralRestrictionMass
      (Matrix.posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E := hz
  have hb : ‖WithLp.toLp 2 b‖ = 1 := by
    simpa only [b, WithLp.toLp_ofLp] using Matrix.norm_selectedBellVector ΩX E hzX
  calc
    _ = (⟪Ψ, Matrix.toEuclideanLin (NormedSpace.exp ((u : ℂ) •
        labelEntropy (subsystemPerm k (compressedSiteSpace β X (Fin E.card))
          (exteriorRegion X Q)))) Ψ⟫_ℂ).re :=
      re_inner_exp_labelEntropy_bellInsertion β X E (Fin E.card) k b hb Ψ Q u
    _ ≤ _ := re_inner_exp_labelEntropy_compressedTypicalSiteState_prod_le
      β Ω X Q hXQ E hz k u

private theorem compressedTypicalSiteTensor_ne_zero
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (Configuration β X))
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    (k : ℕ) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
    let χ : Fin E.card × Configuration β Xᶜ → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
    let Ψ := WithLp.toLp 2
      (fun x : Config k (compressedSiteSpace β X (Fin E.card)) ↦
        ∏ j, χ (Equiv.piOptionEquivProd (x j)))
    WithLp.ofLp Ψ ≠ 0 := by
  classical
  intro ΩX χ Ψ
  have hzX : 0 < Matrix.IsHermitian.spectralRestrictionMass
      (Matrix.posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E := hz
  have hχne : ∃ c, Matrix.compressedTypicalPureState ΩX E c ≠ 0 := by
    by_contra! h
    have hzero : Matrix.compressedTypicalPureState ΩX E = 0 := by
      ext c
      exact h c
    have hn := Matrix.norm_compressedTypicalPureState ΩX E hzX
    rw [hzero, norm_zero] at hn
    norm_num at hn
  obtain ⟨c, hc⟩ := hχne
  let x₀ : (v : Option ↥(Xᶜ)) → compressedSiteSpace β X (Fin E.card) v :=
    Equiv.piOptionEquivProd.symm ((Finset.equivFin E) c.1, c.2)
  intro h
  have hval := congrFun h (fun _ : Fin k ↦ x₀)
  simp only [Ψ, χ, x₀, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Pi.zero_apply] at hval
  exact pow_ne_zero k hc hval

private theorem inv_pow_mul_exp_eq (z : ℝ) (hz : 0 < z) (k : ℕ) (b : ℝ) :
    z⁻¹ ^ k * Real.exp b = Real.exp (b - (k : ℝ) * Real.log z) := by
  have hpow : z⁻¹ ^ k = Real.exp (-(k : ℝ) * Real.log z) := by
    rw [← Real.exp_log (pow_pos (inv_pos.mpr hz) k), Real.log_pow, Real.log_inv]
    congr 1
    ring
  rw [hpow, ← Real.exp_add]
  congr 1
  ring

private theorem signed_moments_of_marginal_domination
    {n : Type*} [Fintype n] [DecidableEq n] {σ : Matrix n n ℂ}
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) {K r : ℝ}
    (hmoment : ∀ v : ℝ, |v| ≤ r →
      Real.log (Entropy.surprisalMoment hσ.isHermitian.eigenvalues v) ≤
        v * vonNeumannEntropy σ hσ.isHermitian + K * v ^ 2)
    (k : ℕ) (M : ℝ → ℝ) {z u : ℝ} (hz : 0 < z)
    (hu : 0 ≤ u) (hur : 2 * u ≤ r) (hu1 : 2 * u ≤ 1)
    (htransfer : ∀ v : ℝ, M v ≤ z⁻¹ ^ k *
      (Matrix.finKronecker (fun _ : Fin k ↦ σ) *
        NormedSpace.exp ((v : ℂ) • labelEntropy (copyPerm n k))).trace.re) :
    let S := vonNeumannEntropy σ hσ.isHermitian
    M u ≤ Real.exp (u * ((k : ℝ) * S) + k * K * u ^ 2 - k * Real.log z) ∧
    M (-u) ≤ Real.exp ((-u) * ((k : ℝ) * S) +
      (2 * k * K * u ^ 2 + ((Fintype.card n : ℝ) ^ 2 / 2) *
        Real.log ((k : ℝ) + 1)) - k * Real.log z) := by
  intro S
  have hiid := Matrix.PosSemidef.re_trace_finKronecker_exp_signed_labelEntropy_le
    hσ htr hmoment k hu hur hu1
  constructor
  · have h := (htransfer u).trans
      (mul_le_mul_of_nonneg_left hiid.1 (pow_nonneg (inv_nonneg.mpr hz.le) k))
    simpa only [inv_pow_mul_exp_eq z hz, S] using h
  · have h := (htransfer (-u)).trans
      (mul_le_mul_of_nonneg_left hiid.2 (pow_nonneg (inv_nonneg.mpr hz.le) k))
    simpa only [inv_pow_mul_exp_eq z hz, S, Nat.cast_pow] using h

private theorem three_rpow_exp_bound {x y z A B C : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hA : x ≤ Real.exp A) (hB : y ≤ Real.exp B) (hC : z ≤ Real.exp C) :
    x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) ≤
      Real.exp ((A + B + C) / 3) := by
  have h1 := Real.rpow_le_rpow hx hA (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h2 := Real.rpow_le_rpow hy hB (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h3 := Real.rpow_le_rpow hz hC (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have h := mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg hy _) (by positivity)) h3
    (Real.rpow_nonneg hz _) (by positivity)
  convert h using 1
  simp only [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
  congr 1
  ring

/-- A same-vector, same-selection sharp upper bound for the actual pinned
factor. The original augmented family supplies every replica weight. The
constant is chosen before the copy number, either region, and their moment
data. Its dimensional dependence contributes only a logarithmic remainder.

The three one-copy surprisal bounds concern the original physical marginals,
not the selected marginals. Singular marginals and empty regions are allowed.
No label choice, tree, terminal probability, or target estimate is a premise.
Source: OpenAI area-law manuscript, 07-comparators.tex, lines 405–415. -/
theorem exists_log_re_inner_replicaPinnedFactor_post_le
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (hΩ : ‖Ω‖ = 1)
    (X : Finset V) (E : Finset (Configuration β X))
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    {a K r : ℝ} (ha : 0 < a) (har : 6 * a ≤ r) (ha1 : 6 * a ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (U Y : Finset V),
      Disjoint X U → Disjoint X Y → Disjoint U Y →
      (∀ Q : Finset V, Q = U ∨ Q = U ∪ Y ∨ Q = Y →
        ∀ v : ℝ, |v| ≤ r →
          Real.log (Entropy.surprisalMoment
            (reducedPure_posSemidef β Ω Q).isHermitian.eigenvalues v) ≤
            v * vonNeumannEntropy (reducedPure β Ω Q)
              (reducedPure_posSemidef β Ω Q).isHermitian + K * v ^ 2) →
      let z := (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E
      let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
      let χ : Fin E.card × Configuration β Xᶜ → ℂ := fun x ↦
        Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
      let Ψ := WithLp.toLp 2
        (fun x : Config k (compressedSiteSpace β X (Fin E.card)) ↦
          ∏ j, χ (Equiv.piOptionEquivProd (x j)))
      let ι₀ := addedSiteSpace (addedSiteSpace β E) (Fin E.card)
      let b : Configuration β X × E → ℂ := Matrix.selectedBellVector ΩX E
      let J := (addedSiteInsertion (compressedSiteSpace β X (Fin E.card))
        (Configuration β X × E) k b).submatrix
          (bellInsertionCopyEquiv β X E (Fin E.card) k) id
      let p := WithLp.toLp 2 (J *ᵥ WithLp.ofLp Ψ)
      let W := replicaMetric ι₀ (a / 2) k
      let ext := fun Q : Finset V ↦ (Q \ X).image fun v ↦ some (some v)
      let D := ((W (ext U))⁻¹ * (W (ext (U ∪ Y)))⁻¹ * W (ext Y)) ^ 2
      let S := fun Q : Finset V ↦ vonNeumannEntropy (reducedPure β Ω Q)
        (reducedPure_posSemidef β Ω Q).isHermitian
      Real.log (⟪p, Matrix.toEuclideanLin D p⟫_ℂ).re ≤
        (k : ℝ) * a * (S U + S (U ∪ Y) - S Y) + 12 * K * k * a ^ 2 -
          k * Real.log z + C * Real.log ((k : ℝ) + 2) +
          ((Fintype.card (Configuration β Y) : ℝ) ^ 2 / 6) *
            Real.log ((k : ℝ) + 1) := by
  classical
  obtain ⟨x, _⟩ : ∃ x, Ω x ≠ 0 := by
    by_contra! h
    have hzero : Ω = 0 := by
      ext x
      exact h x
    simp only [hzero, norm_zero, zero_ne_one] at hΩ
  let : ∀ v, Nonempty (β v) := fun v ↦ ⟨x v⟩
  have hE : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun he ↦ by
    simp [he, Matrix.IsHermitian.spectralRestrictionMass] at hz
  let : Nonempty E := ⟨⟨Classical.choose hE, Classical.choose_spec hE⟩⟩
  let : Nonempty (Fin E.card) := ⟨⟨0, Finset.card_pos.mpr hE⟩⟩
  let ι₀ := addedSiteSpace (addedSiteSpace β E) (Fin E.card)
  let : ∀ v, Nonempty (ι₀ v) := fun v ↦ by
    cases v with
    | none => exact (inferInstance : Nonempty (Fin E.card))
    | some v =>
      cases v with
      | none => exact (inferInstance : Nonempty E)
      | some v => exact (inferInstance : Nonempty (β v))
  obtain ⟨C, hC, hweight⟩ := exists_replicaPinnedFactor_le_exp ι₀
    (show 0 < a / 2 from div_pos ha (by norm_num))
  refine ⟨C, hC, ?_⟩
  intro k U Y hXU hXY hUY hmoment z ΩX χ Ψ ι₀' b J p W ext D S
  have hzX : 0 < Matrix.IsHermitian.spectralRestrictionMass
      (Matrix.posSemidef_vecMulVec_self_star ΩX).partialTraceRight.isHermitian E := hz
  have hb : ‖WithLp.toLp 2 b‖ = 1 := by
    simpa only [b, WithLp.toLp_ofLp] using Matrix.norm_selectedBellVector ΩX E hzX
  have hJ : Jᴴ * J = 1 := isIsometry_bellInsertion β X E (Fin E.card) k b hb
  have hextunion : ext (U ∪ Y) = ext U ∪ ext Y := by
    simp only [ext, Finset.union_sdiff_distrib, Finset.image_union]
  have hextdisj : Disjoint (ext U) (ext Y) := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvY
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hvU
    obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp hvY
    have hyu' : y = u := Option.some.inj (Option.some.inj hyu)
    subst y
    exact Finset.disjoint_left.mp hUY (Finset.mem_sdiff.mp hu).1
      (Finset.mem_sdiff.mp hy).1
  let ρ := Matrix.vecMulVec (WithLp.ofLp p) (star (WithLp.ofLp p))
  have hρ : ρ.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  let L := fun Q : Finset V ↦ labelEntropy (subsystemPerm k ι₀ (ext Q))
  let M := fun (Q : Finset V) (v : ℝ) ↦
    (ρ * NormedSpace.exp ((v : ℂ) • L Q)).trace.re
  have hMnonneg (Q : Finset V) (v : ℝ) : 0 ≤ M Q v :=
    hρ.re_trace_mul_exp_nonneg
      ((isHermitian_labelObservable _ _).smul (by simp [IsSelfAdjoint]))
  have hmoment_post (Q : Finset V) (hXQ : Disjoint X Q)
      (hQ : Q = U ∨ Q = U ∪ Y ∨ Q = Y) :
      M Q (3 * a) ≤ Real.exp (3 * a * ((k : ℝ) * S Q) +
        k * K * (3 * a) ^ 2 - k * Real.log z) ∧
      M Q (-3 * a) ≤ Real.exp ((-3 * a) * ((k : ℝ) * S Q) +
        (2 * k * K * (3 * a) ^ 2 +
          ((Fintype.card (Configuration β Q) : ℝ) ^ 2 / 2) *
            Real.log ((k : ℝ) + 1)) - k * Real.log z) := by
    have htransfer (v : ℝ) : M Q v ≤ z⁻¹ ^ k *
        (Matrix.finKronecker (fun _ : Fin k ↦ reducedPure β Ω Q) *
          NormedSpace.exp ((v : ℂ) •
            labelEntropy (copyPerm (Configuration β Q) k))).trace.re := by
      have hpair : M Q v =
          (⟪p, Matrix.toEuclideanLin (NormedSpace.exp ((v : ℂ) • L Q)) p⟫_ℂ).re :=
        (congrArg Complex.re (Entropy.inner_toEuclideanLin_eq_trace _ p)).symm
      exact hpair.trans_le
        (re_inner_exp_labelEntropy_selectedBellPost_le β Ω X Q hXQ E hz k v)
    simpa only [S, neg_mul] using signed_moments_of_marginal_domination
      (reducedPure_posSemidef β Ω Q) (trace_reducedPure β Ω hΩ Q)
      (hmoment Q hQ) k (M Q) hz
      (show 0 ≤ 3 * a from mul_nonneg (by norm_num) ha.le) (by linarith only [har])
      (by linarith only [ha1]) htransfer
  have hU := (hmoment_post U hXU (Or.inl rfl)).1
  have hV := (hmoment_post (U ∪ Y) (Finset.disjoint_union_right.mpr ⟨hXU, hXY⟩)
    (Or.inr (Or.inl rfl))).1
  have hY := (hmoment_post Y hXY (Or.inr (Or.inr rfl))).2
  have hthree := three_rpow_exp_bound (hMnonneg U (3 * a))
    (hMnonneg (U ∪ Y) (3 * a)) (hMnonneg Y (-3 * a)) hU hV hY
  have hholder := re_trace_mul_exp_pinnedLabels_le ι₀ k (ext U) (ext Y) hextdisj hρ a
  rw [← hextunion] at hholder
  have hupper := hρ.re_trace_mul_le_re_trace_mul
    (hweight k (ext U) (ext Y) hextdisj)
  rw [← hextunion] at hupper
  have hscale : (2 : ℝ) * (a / 2) = a := by ring
  simp only [hscale, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hupper
  have hbound := hupper.trans (mul_le_mul_of_nonneg_left (hholder.trans hthree)
    (Real.rpow_nonneg (by positivity : 0 ≤ (k : ℝ) + 2) C))
  have hΨne : WithLp.ofLp Ψ ≠ 0 :=
    compressedTypicalSiteTensor_ne_zero β Ω X E hz k
  have hpne : J *ᵥ WithLp.ofLp Ψ ≠ 0 := by
    intro h
    have hh := congrArg (fun v ↦ Jᴴ *ᵥ v) h
    rw [Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec, Matrix.mulVec_zero] at hh
    exact hΨne hh
  have hD : D.PosDef := by
    simpa only [D, W, hextunion] using
      posDef_replicaPinnedFactor ι₀' (show 0 ≤ a / 2 from div_nonneg ha.le (by norm_num)) k
        (ext U) (ext Y) hextdisj
  have hpos : 0 < (⟪p, Matrix.toEuclideanLin D p⟫_ℂ).re := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, dotProduct_comm]
    exact hD.re_dotProduct_pos hpne
  apply (Real.log_le_iff_le_exp hpos).2
  rw [Entropy.inner_toEuclideanLin_eq_trace]
  convert hbound using 1
  rw [Real.rpow_def_of_pos (by positivity : 0 < (k : ℝ) + 2), ← Real.exp_add]
  congr 1
  ring

end TensorPower
