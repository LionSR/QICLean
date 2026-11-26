/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.Bell.SelectedBellPostMass
import QICLean.ManyBody.Replica.Bell.SchmidtBellPrevectorOverlap
import QICLean.ManyBody.Replica.Bell.SchmidtBellWitnessRange
import QICLean.ManyBody.Replica.Bell.PinnedMetricCoordinates
import QICLean.ManyBody.Replica.Bell.PinnedCompressedPowers
import QICLean.ManyBody.Replica.Bell.InsertionSymmetry
import QICLean.Analysis.Isometry.IsometricDomainExtension

/-!
# The exact pin identity for the literal selected Bell postvector

The actual physical prevector, its supplied right auxiliary label, the fixed
selected-set enumeration and the exact pin coefficient are retained. The
symmetric pin is obtained from the Bell range pin by proving symmetry of the
same labelled postvector, rather than assuming any vector equality.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 283--299
and 383--418, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

It also contains the following results.

* `TensorPower.selectedBellPost_inverse_norm_le_physical`: physical inverse-metric norm transport
  with the exact selected pin cost.
-/

open Matrix PermutationRepresentation

section SelectedBellPostPin

open scoped BigOperators Matrix Kronecker ComplexOrder

noncomputable section

namespace TensorPower

attribute [local instance] sharpTreeRegionDecidableEq sharpTreeSiteDecidableEq
  sharpTreeConfigDecidableEq

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
variable (E : Finset (ManyBody.RegionConfig β X)) (k : ℕ)

local notation "ι₀" => addedSiteSpace (addedSiteSpace β E) (Fin E.card)
local notation "ιe" => ManyBody.compressedSiteSpace β X (Fin E.card)
local notation "A" => ManyBody.RegionConfig β X
local notation "B" => ManyBody.ComplConfig β X
local notation "L" => Fin k → A × E

/-- The literal inserted postvector is the pullback of the actual selected
Bell tensor and compressed selected tensor in witness coordinates. -/
theorem selectedBellPost_eq_pullback :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv β X) Ω
    let post : EuclideanSpace ℂ (L × Config k ιe) := WithLp.toLp 2
      (fun x ↦ (∏ j, selectedBellVector ΩX E (x.1 j)) *
        ∏ j, compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x.2 j none), fun v ↦ x.2 j (some v)))
    selectedBellPost β Ω X E k =
      WithLp.toLp 2 (post ∘ ManyBody.schmidtBellWitnessEquiv β X E k) := by
  intro ΩX post
  ext x
  change (addedSiteInsertion ιe (A × E) k (selectedBellVector ΩX E) *ᵥ
      (fun y : Config k ιe ↦ ∏ j, compressedTypicalPureState ΩX E
        ((Finset.equivFin E).symm (y j none), fun v ↦ y j (some v))))
      (bellInsertionCopyEquiv β X E (Fin E.card) k x) = _
  rw [addedSiteInsertion_mulVec]
  rfl

/-- The supplied auxiliary sector of the literal postvector is symmetric.
The proof uses only the tensor-product construction and the derived
auxiliary-label commutation; no selected-mass or norm hypothesis is needed. -/
theorem symProj_labelProj_selectedBellPost
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let Q := labelProj (subsystemPerm k ι₀ {none}) ell
    toEuclideanLin (symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k))
      (toEuclideanLin Q (selectedBellPost β Ω X E k)) =
        toEuclideanLin Q (selectedBellPost β Ω X E k) := by
  intro Q
  let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv β X) Ω
  let χ : ((o : Option {v // v ∉ X}) → ιe o) → ℂ := fun x ↦
    compressedTypicalPureState ΩX E
      ((Finset.equivFin E).symm (x none), fun v ↦ x (some v))
  let Ψ : Config k ιe → ℂ := fun x ↦ ∏ j, χ (x j)
  let J := (addedSiteInsertion ιe (A × E) k (selectedBellVector ΩX E)).submatrix
    (bellInsertionCopyEquiv β X E (Fin E.card) k) id
  let Pe := symProj (copyPerm ((o : Option {v // v ∉ X}) → ιe o) k)
  let Qe := labelProj (subsystemPerm k ιe {none}) ell
  have hΨ : Pe *ᵥ Ψ = Ψ := by
    apply symProj_mulVec_of_mem
    intro σ
    rw [permOp_mulVec]
    funext x
    change (∏ j, χ (x (σ j))) = ∏ j, χ (x j)
    exact Fintype.prod_equiv σ _ _ (fun _ ↦ rfl)
  have hQe : Commute Qe Pe := by
    classical
    simpa [labelObservable] using commute_labelObservable_symProj ιe k {none}
      (fun l ↦ if l = ell then 1 else 0)
  have hQJ : Q * J = J * Qe :=
    labelProj_mul_bellInsertion_auxiliary β X E (Fin E.card) k ell
      (selectedBellVector ΩX E)
  have hSJ : symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k) * J =
      J * Pe := symProj_mul_bellInsertion β X E (Fin E.card) k
        (selectedBellVector ΩX E)
  apply WithLp.ofLp_injective 2
  change symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k) *ᵥ
      (Q *ᵥ (J *ᵥ Ψ)) = Q *ᵥ (J *ᵥ Ψ)
  have hQP : Q *ᵥ (J *ᵥ Ψ) = J *ᵥ (Qe *ᵥ Ψ) := by
    rw [Matrix.mulVec_mulVec, hQJ, ← Matrix.mulVec_mulVec]
  have hPeQP : Pe *ᵥ (Qe *ᵥ Ψ) = Qe *ᵥ Ψ := by
    rw [Matrix.mulVec_mulVec, ← hQe.eq, ← Matrix.mulVec_mulVec, hΨ]
  calc
    _ = symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k) *ᵥ
        (J *ᵥ (Qe *ᵥ Ψ)) := congrArg (fun w ↦
          symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k) *ᵥ w) hQP
    _ = (J * Pe) *ᵥ (Qe *ᵥ Ψ) := by rw [Matrix.mulVec_mulVec, hSJ]
    _ = J *ᵥ (Qe *ᵥ Ψ) := by rw [← Matrix.mulVec_mulVec, hPeQP]
    _ = _ := hQP.symm

/-- The actual symmetric Bell pin of the original supplied-label physical
prevector equals the same supplied auxiliary sector of the literal postvector,
with the exact coefficient `(sqrt z / E.card)^k`. -/
theorem bellPin_schmidtBellPrevector_eq_selectedBellPost
    (hz : 0 < (ManyBody.regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let z := (ManyBody.regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv β X) Ω
    let J := (addedSiteInsertion ιe (A × E) k (selectedBellVector ΩX E)).submatrix
      (bellInsertionCopyEquiv β X E (Fin E.card) k) id
    let Pe := symProj (copyPerm ((o : Option {v // v ∉ X}) → ιe o) k)
    let P := J * Pe * Jᴴ
    let v : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2
      (ManyBody.schmidtBellSitePrevector β X E k ΩX ell ∘ ManyBody.schmidtBellWitnessEquiv β X E k)
    let Q := labelProj (subsystemPerm k ι₀ {none}) ell
    toEuclideanLin P v = (((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k) •
      toEuclideanLin Q (selectedBellPost β Ω X E k) := by
  intro z ΩX J Pe P v Q
  let τ := ManyBody.schmidtBellWitnessEquiv β X E k
  let R := (piKronecker fun _ : Fin k ↦ selectedBellProjection ΩX E) ⊗ₖ
    (1 : Matrix (Config k ιe) (Config k ιe) ℂ)
  let Qw := (1 : Matrix L L ℂ) ⊗ₖ labelProj (subsystemPerm k ιe {none}) ell
  let post : EuclideanSpace ℂ (L × Config k ιe) := WithLp.toLp 2
    (fun x ↦ (∏ j, selectedBellVector ΩX E (x.1 j)) *
      ∏ j, compressedTypicalPureState ΩX E
        ((Finset.equivFin E).symm (x.2 j none), fun w ↦ x.2 j (some w)))
  let c : ℂ := ((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k
  have hraw := ManyBody.selectedBellProjection_replicaPrevector_site β X E k ΩX hz ell
  change WithLp.toLp 2 (R *ᵥ (ManyBody.schmidtBellSitePrevector β X E k ΩX ell).ofLp) =
    c • WithLp.toLp 2 (Qw *ᵥ post.ofLp) at hraw
  have hJJ : J * Jᴴ = R.submatrix τ τ :=
    ManyBody.bellInsertion_mul_conjTranspose_selectedBell β X E k ΩX
  have hQ : Qw.submatrix τ τ = Q :=
    ManyBody.labelProj_schmidtBellWitnessEquiv_auxiliary β X E k ell
  have hpost : selectedBellPost β Ω X E k = WithLp.toLp 2 (post ∘ τ) :=
    selectedBellPost_eq_pullback β Ω X E k
  have hpin : toEuclideanLin (J * Jᴴ) v =
      c • toEuclideanLin Q (selectedBellPost β Ω X E k) := by
    rw [hJJ, ← hQ, hpost]
    ext x
    have hx := congrArg (fun w : EuclideanSpace ℂ (L × Config k ιe) ↦ w (τ x)) hraw
    change ((R.submatrix τ τ) *ᵥ
        ((ManyBody.schmidtBellSitePrevector β X E k ΩX ell).ofLp ∘ τ)) x =
      c * ((Qw.submatrix τ τ) *ᵥ (post.ofLp ∘ τ)) x
    rw [Matrix.submatrix_mulVec_equiv, Matrix.submatrix_mulVec_equiv]
    simpa only [Function.comp_def, Equiv.apply_symm_apply, WithLp.ofLp_smul,
      WithLp.ofLp_toLp, Pi.smul_apply, smul_eq_mul] using hx
  let S := symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k)
  have hSJ : S * J = J * Pe :=
    symProj_mul_bellInsertion β X E (Fin E.card) k (selectedBellVector ΩX E)
  have hP : P = S * (J * Jᴴ) := by
    change J * Pe * Jᴴ = S * (J * Jᴴ)
    rw [← Matrix.mul_assoc, hSJ]
  rw [hP, toLpLin_mul_same, LinearMap.comp_apply, hpin, map_smul]
  rw [symProj_labelProj_selectedBellPost β Ω X E k ell]

end TensorPower

end

end SelectedBellPostPin

section SelectedBellPostInverseTransport

/-!
## Physical inverse-metric norm transport with the exact selected pin cost

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
    (X : Finset V) (E : Finset (ManyBody.RegionConfig β X))
    (hz : 0 < (ManyBody.regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E)
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
    let z := (ManyBody.regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv β X) Ω
    let v : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2
      (ManyBody.schmidtBellSitePrevector β X E k ΩX ell ∘ ManyBody.schmidtBellWitnessEquiv β X E k)
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
  let b : ManyBody.RegionConfig β X × E → ℂ := selectedBellVector ΩX E
  let J := (addedSiteInsertion (ManyBody.compressedSiteSpace β X (Fin E.card))
    (ManyBody.RegionConfig β X × E) k b).submatrix
      (bellInsertionCopyEquiv β X E (Fin E.card) k) id
  let Pe := symProj (copyPerm
    ((o : Option {v // v ∉ X}) → ManyBody.compressedSiteSpace β X (Fin E.card) o) k)
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

end

end SelectedBellPostInverseTransport
