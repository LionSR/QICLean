/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SelectedBellPostPin
import QICLean.Representation.BellPinnedCompressedPowers
import QICLean.Representation.BellSymmetricPinProjection
import QICLean.Analysis.ProjectionIntertwiningNorm

/-!
# Physical inverse-metric norm transport with the exact selected pin cost

The original physical prevector and the original full-family band metric use
the same supplied symmetric coordinates. Its inverse norm dominates the
inverse exterior-metric norm of the same auxiliary sector of selectedBellPost,
with exactly `(z / E.card^2)^k`. Positivity, power intertwining and contraction
are obtained from the accepted actual-metric APIs, not supplied as premises.

This finite-copy bridge does not select a label, impose an entropy bound,
choose a new physical state or take an asymptotic limit.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 283--308,
370--381 and 383--418, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation FiniteProduct
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TensorPower

attribute [local instance] sharpTreeRegionDecidableEq sharpTreeSiteDecidableEq
  sharpTreeConfigDecidableEq

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- Exact finite-copy transport from the literal selected postvector sector to
its original physical prevector, using the same actual compressed metric.
Every real exponent is allowed. The sharp leaf/tree estimate can be inserted
on the left for nonnegative exponents without any further operator premise. -/
theorem selectedBellPost_inverse_norm_le_physical
    {S : Type*} (Ω : EuclideanSpace ℂ ((v : V) → β v)) (hΩ : ‖Ω‖ = 1)
    (X : Finset V) (E : Finset (Configuration β X))
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    (k n : ℕ)
    (Z : Matrix (Config k (addedSiteSpace (addedSiteSpace β E) (Fin E.card)))
      (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj
      (copyPerm ((o : Option (Option V)) → addedSiteSpace (addedSiteSpace β E)
        (Fin E.card) o) k))
    {t : ℝ} (ht : 0 ≤ t) (G : ℕ) (U Y : S → Fin G → Finset V)
    (hdisj : ∀ j g, Disjoint (U j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h)
    (T : MeanTree S) (ell : IrrepLabel (Equiv.Perm (Fin k))) (s : ℝ) :
    let ι₀ := addedSiteSpace (addedSiteSpace β E) (Fin E.card)
    let z := (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
    let v : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2
      (schmidtBellSitePrevector β X E k ΩX ell ∘ schmidtBellWitnessEquiv β X E k)
    let W := replicaMetric ι₀ t k
    let Q := fun j g ↦ insert (some none)
      ((X ∪ U j g).image fun v ↦ some (some v))
    let F := fun j g ↦ insert none
      (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
    let ext := fun B : Finset V ↦ (B \ X).image fun v ↦ some (some v)
    let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (ext (Y j g))) ^ 2
    let D := fun j g ↦ ((W (ext (U j g)))⁻¹ *
      (W (ext (U j g ∪ Y j g)))⁻¹ * W (ext (Y j g))) ^ 2
    let M := (List.ofFn fun g ↦ T.eval (fun j ↦ Zᴴ * A j g * Z)).prod
    let N := (List.ofFn fun g ↦ T.eval (D · g)).prod
    let R := labelProj (subsystemPerm k ι₀ {none}) ell
    (z / (E.card : ℝ) ^ 2) ^ k *
      ‖toEuclideanLin (N ^ (-s))
        (toEuclideanLin R (selectedBellPost β Ω X E k))‖ ^ 2 ≤
      ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ v)‖ ^ 2 := by
  intro ι₀ z ΩX v W Q F ext A D M N R
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
  let : ∀ o, Nonempty (ι₀ o) := fun o ↦ by
    cases o with
    | none => exact (inferInstance : Nonempty (Fin E.card))
    | some o =>
      cases o with
      | none => exact (inferInstance : Nonempty E)
      | some v => exact (inferInstance : Nonempty (β v))
  let b : Configuration β X × E → ℂ := selectedBellVector ΩX E
  let J := (addedSiteInsertion (compressedSiteSpace β X (Fin E.card))
    (Configuration β X × E) k b).submatrix
      (bellInsertionCopyEquiv β X E (Fin E.card) k) id
  let Pe := symProj (copyPerm
    ((o : Option ↥(Xᶜ)) → compressedSiteSpace β X (Fin E.card) o) k)
  let P := J * Pe * Jᴴ
  let c : ℂ := ((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k
  have hb : ‖WithLp.toLp 2 b‖ = 1 := by
    simpa only [b, WithLp.toLp_ofLp] using Matrix.norm_selectedBellVector ΩX E hz
  have hp := replicaMetric_compressed_bandProduct_bellPin_rpow
    β X E (Fin E.card) k n Z hZ hZZ ht G U Y hdisj hnest b T
  have hn := (replicaMetric_bandProduct_bellPin
    β X E (Fin E.card) ht k G U Y hdisj hnest b T).1
  have hnorm := Matrix.norm_projected_le_of_isometric_intertwine
    (hp.1.rpow_isHermitian (-s)) (hn.rpow_isHermitian (-s))
    (isStarProjection_bellInsertion_symProj β X E (Fin E.card) k b hb)
    hZ (hp.2 (-s)) v
  change ‖toEuclideanLin (N ^ (-s)) (toEuclideanLin P v)‖ ≤
    ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ v)‖ at hnorm
  have hpin : toEuclideanLin P v = c •
      toEuclideanLin R (selectedBellPost β Ω X E k) :=
    bellPin_schmidtBellPrevector_eq_selectedBellPost β Ω X E k hz ell
  rw [hpin, map_smul, norm_smul] at hnorm
  have hc : ‖c‖ ^ 2 = (z / (E.card : ℝ) ^ 2) ^ k := by
    change ‖(((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k)‖ ^ 2 = _
    rw [Complex.norm_pow, Complex.norm_div,
      Complex.norm_of_nonneg (Real.sqrt_nonneg z), Complex.norm_natCast,
      pow_right_comm (Real.sqrt z / (E.card : ℝ)) k 2, div_pow, Real.sq_sqrt hz.le]
  have hsq := pow_le_pow_left₀
    (mul_nonneg (norm_nonneg c) (norm_nonneg _)) hnorm 2
  rw [mul_pow, hc] at hsq
  exact hsq

end TensorPower
