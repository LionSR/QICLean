/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SelectedBellPostInverseTransport
import QICLean.Analysis.SharpBellOverlapLogBound

/-!
# The sharp physical upper rate for a supplied Schmidt--Bell label sequence

The physical prevector theorem supplies one sequence with inverse-polynomial
auxiliary mass, energy, symmetry, both auxiliary labels and entropy asymptotics.
This theorem consumes that very sequence's mass conclusion. The exact insertion
identity transfers it to the selected postvector, and the actual sharp tree and
pin transport estimates give the physical inverse-metric rate. No label or
state is selected again, and no target norm estimate is assumed.

The entropy sum retains every terminal weight. One nonnegative logarithmic
error coefficient is chosen before the copy number, symmetric coordinates,
band count, regions and weighted tree. For fixed dimensions and band count its
vanishing limit is the accepted Bell overlap remainder theorem.

The left selected auxiliary register is still E. The two-enumerated-register
coordinate wrapper and the later geometric entropy comparison are separate.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 240--308
and 383--418, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Topology Matrix PermutationRepresentation FiniteProduct
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TensorPower

attribute [local instance] sharpTreeRegionDecidableEq sharpTreeSiteDecidableEq
  sharpTreeConfigDecidableEq

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The same supplied physical label sequence satisfies the sharp logarithmic
upper estimate once its existing inverse-polynomial mass conclusion holds.
The physical norm lower bound, pin coefficient and postvector mass identity
are all derived. The constant and eventual threshold precede every band and
tree choice. Source: area-law manuscript, `07-comparators.tex`,
`comparator:sharp-upper`, lines 383--418. -/
theorem eventually_suppliedSchmidtBell_sharp_upper
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (hΩ : ‖Ω‖ = 1)
    (X : Finset V) (E : Finset (Configuration β X))
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    {a K r : ℝ} (ha : 0 < a) (har : 6 * a ≤ r) (ha1 : 6 * a ≤ 1)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
    let ψ : Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    (∀ᶠ k : ℕ in atTop,
      (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
        ‖WithLp.toLp 2
          (((1 : Matrix (Fin k → Configuration β Xᶜ)
            (Fin k → Configuration β Xᶜ) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
            (fun x : (Fin k → Configuration β Xᶜ) × (Fin k → Fin E.card) ↦
              ∏ j, ψ (x.1 j, x.2 j)))‖ ^ 2) →
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ G : ℕ, Tendsto (Real.bellOverlapRemainder E.card C G) atTop (𝓝 0)) ∧
      ∀ᶠ k : ℕ in atTop,
      ∀ (n : ℕ)
        (Z : Matrix (Config k (addedSiteSpace (addedSiteSpace β E) (Fin E.card)))
          (Fin n) ℂ),
      Zᴴ * Z = 1 →
      Z * Zᴴ = symProj (copyPerm
        ((o : Option (Option V)) → addedSiteSpace (addedSiteSpace β E)
          (Fin E.card) o) k) →
      ∀ (G : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
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
      ∀ (T : MeanTree ι) (s : ℝ), 2 * s ∈ Set.Icc (0 : ℝ) 1 →
      let ι₀ := addedSiteSpace (addedSiteSpace β E) (Fin E.card)
      let z := (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E
      let v : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2
        (schmidtBellSitePrevector β X E k ΩX (ell k) ∘ schmidtBellWitnessEquiv β X E k)
      let W := replicaMetric ι₀ (a / 2) k
      let Q := fun j g ↦ insert (some none)
        ((X ∪ U j g).image fun v ↦ some (some v))
      let F := fun j g ↦ insert none
        (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
      let ext := fun B : Finset V ↦ (B \ X).image fun v ↦ some (some v)
      let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (ext (Y j g))) ^ 2
      let M := (List.ofFn fun g ↦ T.eval (fun j ↦ Zᴴ * A j g * Z)).prod
      let Nsq := ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ v)‖ ^ 2
      let S := fun Q : Finset V ↦ vonNeumannEntropy (reducedPure β Ω Q)
        (reducedPure_posSemidef β Ω Q).isHermitian
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
        2 * Real.log (E.card : ℝ) - Real.log z +
          2 * s * a * (∑ g, ∑ j, T.weight j *
            (S (U j g) + S (U j g ∪ Y j g) - S (Y j g))) +
          24 * s * G * K * a ^ 2 - 2 * s * G * Real.log z +
            Real.bellOverlapRemainder E.card C G k := by
  intro ΩX ψ hmass
  obtain ⟨C, hC, htree⟩ :=
    exists_selectedBellPost_sharp_tree_bounds (K := K) β Ω hΩ X E hz ha har ha1
  have hE : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun he ↦ by
    simp [he, Matrix.IsHermitian.spectralRestrictionMass] at hz
  refine ⟨C + (E.card : ℝ) ^ 2 + 1, by positivity,
    (fun G ↦ Real.tendsto_bellOverlapRemainder E.card (C + (E.card : ℝ) ^ 2 + 1) G),
    (hmass.and (eventually_ge_atTop 1)).mono ?_⟩
  rintro k ⟨hmassk, hk⟩ n Z hZ hZZ G ι instF instD U Y hXU hXY hUY hnest hmom T s hs
  intro ι₀ z v W Q F ext A M Nsq S
  let p := selectedBellPost β Ω X E k
  let P := labelProj (subsystemPerm k ι₀ {none}) (ell k)
  let q := ‖toEuclideanLin P p‖ ^ 2
  have hmassq : 1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ q := by
    simpa only [one_div, Nat.cast_pow] using hmassk.trans_eq
      (norm_sq_labelProj_selectedBellPost_prod β Ω X E hz k (ell k)).symm
  have hq : 0 < q := (show 0 < 1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2)))
    by positivity).trans_le hmassq
  let D := fun j g ↦ ((W (ext (U j g)))⁻¹ *
    (W (ext (U j g ∪ Y j g)))⁻¹ * W (ext (Y j g))) ^ 2
  let N := (List.ofFn fun g ↦ T.eval (D · g)).prod
  let Sigma := ∑ g, ∑ j, T.weight j *
    (S (U j g) + S (U j g ∪ Y j g) - S (Y j g))
  let L := (k : ℝ) * a * Sigma +
    (G : ℝ) * (12 * K * k * a ^ 2 - k * Real.log z + C * Real.log ((k : ℝ) + 2))
  have hs0 : 0 ≤ s := by linarith only [hs.1]
  have hlower := (htree k G U Y hXU hXY hUY hnest hmom T (ell k) hq).2 s hs0
  change q ^ (1 + 2 * s * G) * Real.exp (-2 * s * L) ≤
    ‖toEuclideanLin (N ^ (-s)) (toEuclideanLin P p)‖ ^ 2 at hlower
  have htransport := selectedBellPost_inverse_norm_le_physical
    β Ω hΩ X E hz k n Z hZ hZZ
    (show 0 ≤ a / 2 from div_nonneg ha.le (by norm_num)) G U Y hUY hnest T (ell k) s
  change (z / (E.card : ℝ) ^ 2) ^ k *
      ‖toEuclideanLin (N ^ (-s)) (toEuclideanLin P p)‖ ^ 2 ≤ Nsq at htransport
  have hfinite : (z / (E.card : ℝ) ^ 2) ^ k *
      q ^ (1 + 2 * s * G) * Real.exp (-2 * s * L) ≤ Nsq := by
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left hlower
        (show 0 ≤ (z / (E.card : ℝ) ^ 2) ^ k by positivity)).trans htransport
  exact Real.neg_log_div_le_of_sharp_bell_bound E.card G k (Finset.card_pos.mpr hE) hk
    z C K a Sigma s q Nsq hz hC hs hmassq hfinite

end TensorPower
