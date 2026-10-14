/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaPinnedSharpLeaf
import QICLean.Analysis.MeanTreeProjectionMultibandUpper

/-!
# Terminal-weighted sharp bounds for the actual selected Bell postvector

The physical vector, spectral selection and auxiliary label are supplied.
Every replica metric uses the original full augmented family. Positivity,
cross-band commutation and commutation with the auxiliary label are derived
from the actual metrics and regions. The selected Bell postvector is the
literal one used in the sharp leaf theorem, not a separate state witness.

One nonnegative logarithmic remainder coefficient is chosen before the copy
number, number of bands, terminal labels, regions and weighted tree. The
leading entropy term retains all terminal weights. The exact supplied
projection mass is retained in both the logarithmic and inverse-power bounds.
No polynomial lower bound or choice of that mass is proved here, and the
comparison with the original physical inverse-metric vector remains separate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 383–418, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation FiniteProduct
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TensorPower

local instance sharpTreeRegionDecidableEq
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (X : Finset V) : DecidableEq (Configuration β X) :=
  Fintype.decidablePiFintype

local instance sharpTreeSiteDecidableEq
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

local instance sharpTreeConfigDecidableEq
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (X : Finset V) (E : Finset (Configuration β X)) (k : ℕ) :
    DecidableEq (Config k (addedSiteSpace (addedSiteSpace β E) (Fin E.card))) := by
  let instCopy : DecidableEq ((f : Option (Option V)) →
      addedSiteSpace (addedSiteSpace β E) (Fin E.card) f) :=
    @Fintype.decidablePiFintype _ _ (sharpTreeSiteDecidableEq β X E) inferInstance
  exact @Fintype.decidablePiFintype _ _ (fun _ ↦ instCopy) inferInstance

variable {V : Type} [Fintype V] [DecidableEq V]
  (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The literal selected Bell postvector in the original augmented copy
coordinates, using the supplied physical vector and spectral selection.
Source: `07-comparators.tex`, lines 283–308 and 383–415. -/
def selectedBellPost
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (Configuration β X)) (k : ℕ) :
    EuclideanSpace ℂ (Config k (addedSiteSpace (addedSiteSpace β E) (Fin E.card))) :=
  let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
  let χ : Fin E.card × Configuration β Xᶜ → ℂ := fun x ↦
    Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
  let Ψ := WithLp.toLp 2
    (fun x : Config k (compressedSiteSpace β X (Fin E.card)) ↦
      ∏ j, χ (Equiv.piOptionEquivProd (x j)))
  let b : Configuration β X × E → ℂ := Matrix.selectedBellVector ΩX E
  let J := (addedSiteInsertion (compressedSiteSpace β X (Fin E.card))
    (Configuration β X × E) k b).submatrix
      (bellInsertionCopyEquiv β X E (Fin E.card) k) id
  WithLp.toLp 2 (J *ᵥ WithLp.ofLp Ψ)

private theorem weighted_sum_affine {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : MeanTree ι) (f : ι → ℝ) (b c : ℝ) :
    (∑ j, T.weight j * (b * f j + c)) = b * (∑ j, T.weight j * f j) + c := by
  calc
    _ = ∑ j, (b * (T.weight j * f j) + T.weight j * c) :=
      Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
        T.sum_weight, one_mul]

/-- The actual selected Bell postvector in its supplied auxiliary-label
sector satisfies the terminal-weighted sharp logarithmic bound and its
inverse-power consequence. The uniform remainder is selected before all
copy numbers, bands, regions and tree parameters. The three physical moments
are used by the leaf theorem, with one mass cost per averaged band.

The squared sector norm is the same positive number throughout; its
polynomial lower bound and the physical-vector transport are not hypotheses
or conclusions of this finite-copy result.
Source: `07-comparators.tex`, lines 383–418. -/
theorem exists_selectedBellPost_sharp_tree_bounds
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (hΩ : ‖Ω‖ = 1)
    (X : Finset V) (E : Finset (Configuration β X))
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    {a K r : ℝ} (ha : 0 < a) (har : 6 * a ≤ r) (ha1 : 6 * a ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k G : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
      (U Y : ι → Fin G → Finset V),
      (∀ j g, Disjoint X (U j g)) → (∀ j g, Disjoint X (Y j g)) →
      (∀ j g, Disjoint (U j g) (Y j g)) →
      (∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) →
      (∀ j g (Q : Finset V), Q = U j g ∨ Q = U j g ∪ Y j g ∨ Q = Y j g →
        ∀ v : ℝ, |v| ≤ r →
          Real.log (Entropy.surprisalMoment
            (reducedPure_posSemidef β Ω Q).isHermitian.eigenvalues v) ≤
            v * vonNeumannEntropy (reducedPure β Ω Q)
              (reducedPure_posSemidef β Ω Q).isHermitian + K * v ^ 2) →
      ∀ (T : MeanTree ι) (ell : IrrepLabel (Equiv.Perm (Fin k))),
      let ι₀ := addedSiteSpace (addedSiteSpace β E) (Fin E.card)
      let p := selectedBellPost β Ω X E k
      let P := labelProj (subsystemPerm k ι₀ {none}) ell
      let q := ‖toEuclideanLin P p‖ ^ 2
      0 < q →
      let W := replicaMetric ι₀ (a / 2) k
      let ext := fun Q : Finset V ↦ (Q \ X).image fun v ↦ some (some v)
      let D := fun j g ↦
        ((W (ext (U j g)))⁻¹ * (W (ext (U j g ∪ Y j g)))⁻¹ * W (ext (Y j g))) ^ 2
      let M := (List.ofFn fun g ↦ T.eval (D · g)).prod
      let φ := (‖toEuclideanLin P p‖⁻¹ : ℂ) • toEuclideanLin P p
      let S := fun Q : Finset V ↦ vonNeumannEntropy (reducedPure β Ω Q)
        (reducedPure_posSemidef β Ω Q).isHermitian
      let L := (k : ℝ) * a * (∑ g, ∑ j, T.weight j *
          (S (U j g) + S (U j g ∪ Y j g) - S (Y j g))) +
        (G : ℝ) * (12 * K * k * a ^ 2 - k * Real.log
          ((reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E) +
            C * Real.log ((k : ℝ) + 2))
      (inner ℂ φ (toEuclideanLin (CFC.log M) φ)).re ≤ -(G : ℝ) * Real.log q + L ∧
      ∀ s : ℝ, 0 ≤ s →
        q ^ (1 + 2 * s * G) * Real.exp (-2 * s * L) ≤
          ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin P p)‖ ^ 2 := by
  classical
  obtain ⟨C₀, hC₀, hleaf⟩ :=
    exists_log_re_inner_replicaPinnedFactor_post_le β Ω hΩ X E hz ha har ha1
  let d : ℝ := ∑ Q : Finset V, (Fintype.card (Configuration β Q) : ℝ) ^ 2 / 6
  have hd : 0 ≤ d := Finset.sum_nonneg fun _ _ ↦ by positivity
  refine ⟨C₀ + d, add_nonneg hC₀ hd, ?_⟩
  intro k G ι _ _ U Y hXU hXY hUY hnest hmoment T ell ι₀ p P q hq W ext D M φ S L
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
  let : ∀ v, Nonempty (ι₀ v) := fun v ↦ by
    cases v with
    | none => exact (inferInstance : Nonempty (Fin E.card))
    | some v =>
      cases v with
      | none => exact (inferInstance : Nonempty E)
      | some v => exact (inferInstance : Nonempty (β v))
  have hextunion (A B : Finset V) : ext (A ∪ B) = ext A ∪ ext B := by
    simp only [ext, Finset.union_sdiff_distrib, Finset.image_union]
  have hextmono {A B : Finset V} (hAB : A ⊆ B) : ext A ⊆ ext B := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨u,
      Finset.mem_sdiff.mpr ⟨hAB (Finset.mem_sdiff.mp hu).1, (Finset.mem_sdiff.mp hu).2⟩, rfl⟩
  have hextdisj (j : ι) (g : Fin G) : Disjoint (ext (U j g)) (ext (Y j g)) := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvY
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hvU
    obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp hvY
    have hyu' : y = u := Option.some.inj (Option.some.inj hyu)
    subst y
    exact Finset.disjoint_left.mp (hUY j g) (Finset.mem_sdiff.mp hu).1
      (Finset.mem_sdiff.mp hy).1
  have hextnest (j j' : ι) (g h : Fin G) (hgh : g < h) :
      ext (U j g) ∪ ext (Y j g) ⊆ ext (U j' h) := by
    rw [← hextunion]
    exact hextmono (hnest j j' g h hgh)
  have ht : 0 ≤ a / 2 := div_nonneg ha.le (by norm_num)
  have hbands := replicaPinnedBands_posDef_commute ι₀ ht k G
    (fun j g ↦ ext (U j g)) (fun j g ↦ ext (Y j g)) hextdisj hextnest
  have hD : ∀ j g, (D j g).PosDef := by
    simpa only [D, W, hextunion] using hbands.1
  have hcross : ∀ j j' g h, g ≠ h → Commute (D j g) (D j' h) := by
    simpa only [D, W, hextunion] using hbands.2
  have hroots : ∀ g h, g ≠ h → Commute (T.eval (D · g)) (T.eval (D · h)) :=
    fun _ _ hgh ↦ T.commute_eval_band hD hcross hgh
  have hP : IsStarProjection P :=
    ⟨labelProj_mul_self _ ell, (isHermitian_labelProj _ ell).isSelfAdjoint⟩
  have hinv (Q : Finset (Option (Option V))) : (W Q)⁻¹ =
      labelObservable (subsystemPerm k ι₀ Q) (fun l ↦ (replicaLabelWeight ι₀ (a / 2) l)⁻¹) :=
    labelObservable_inv _ (fun l ↦ (replicaLabelWeight_pos ι₀ ht l).ne')
  have hPL (Q : Finset (Option (Option V)))
      (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
      Commute P (labelObservable (subsystemPerm k ι₀ Q) f) :=
    commute_labelProj_singleton_labelObservable ι₀ k none ell Q f
  have hPD (j : ι) (g : Fin G) : Commute P (D j g) := by
    dsimp only [D]
    rw [hinv, hinv]
    exact (((hPL (ext (U j g)) _).mul_right (hPL (ext (U j g ∪ Y j g)) _)).mul_right
      (hPL (ext (Y j g)) (replicaLabelWeight ι₀ (a / 2)))).pow_right 2
  let c := 12 * K * k * a ^ 2 - k * Real.log
    ((reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E) +
      (C₀ + d) * Real.log ((k : ℝ) + 2)
  have hleaf' (j : ι) (g : Fin G) :
      Real.log (inner ℂ p (toEuclideanLin (D j g) p)).re ≤
        (k : ℝ) * a * (S (U j g) + S (U j g ∪ Y j g) - S (Y j g)) + c := by
    have hb := hleaf k (U j g) (Y j g) (hXU j g) (hXY j g) (hUY j g) (hmoment j g)
    change Real.log (inner ℂ p (toEuclideanLin (D j g) p)).re ≤
      (k : ℝ) * a * (S (U j g) + S (U j g ∪ Y j g) - S (Y j g)) +
        12 * K * k * a ^ 2 - k * Real.log
          ((reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E) +
            C₀ * Real.log ((k : ℝ) + 2) +
              ((Fintype.card (Configuration β (Y j g)) : ℝ) ^ 2 / 6) *
                Real.log ((k : ℝ) + 1) at hb
    have hdim : (Fintype.card (Configuration β (Y j g)) : ℝ) ^ 2 / 6 ≤ d :=
      Finset.single_le_sum (fun Q _ ↦ by positivity) (Finset.mem_univ (Y j g))
    have hlog1 : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by positivity)
    have hlog12 : Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith only)
    have hdimlog := (mul_le_mul_of_nonneg_right hdim hlog1).trans
      (mul_le_mul_of_nonneg_left hlog12 hd)
    dsimp only [c]
    nlinarith only [hb, hdimlog]
  have hsum : (∑ g, ∑ j, T.weight j *
      Real.log (inner ℂ p (toEuclideanLin (D j g) p)).re) ≤ L := by
    calc
      _ ≤ ∑ g, ∑ j, T.weight j * ((k : ℝ) * a *
          (S (U j g) + S (U j g ∪ Y j g) - S (Y j g)) + c) :=
        Finset.sum_le_sum fun g _ ↦ Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_left (hleaf' j g) (T.weight_nonneg j)
      _ = L := by
        simp_rw [weighted_sum_affine]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rfl
  have hlog := MeanTree.re_inner_log_eval_prod_le_of_projection
    (fun _ : Fin G ↦ T) hD hroots hP hPD p hq
  refine ⟨hlog.trans (add_le_add_left hsum _), ?_⟩
  intro s hs
  have hnorm := MeanTree.mass_rpow_mul_exp_le_norm_rpow_neg_eval_prod_projection_sq
    (fun _ : Fin G ↦ T) hD hroots hP hPD p hq hs
  exact (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsum
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num : (-2 : ℝ) ≤ 0) hs)))
    (Real.rpow_nonneg hq.le _)).trans hnorm

end TensorPower
