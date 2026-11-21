/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.CompressedTypicalCommonBellVector
import QICLean.ManyBody.Replica.CompressedPhysicalMatchedCutoffs
import QICLean.Representation.Coherent.Symbol
import QICLean.ManyBody.Replica.Bell.SchmidtBellWitnessRange
import QICLean.ManyBody.Replica.Bell.SchmidtBellPrevectorOverlap

/-!
# A physical test vector for the supplied Schmidt--Bell label

Fix the original physical state, its positive-mass spectral selection, the
already supplied auxiliary-label sequence, and a finite nested family of
regions. The actual auxiliary-mass lower bound gives an eventual unit
common-cutoff vector. Its fixed coordinate pullback is a physical test vector
in the inserted symmetric range, with the same auxiliary label and the exact
selected-mass overlap factor.

The test vector is chosen before the matched region families and their
threshold bounds. Thus these choices share one vector and one eventual
threshold at the fixed physical system. No uniform threshold over different
physical states or ambient systems is asserted. No label sequence is selected.

Source: OpenAI, A two-dimensional area law from a global spectral gap,
September 24, 2026, `07-comparators.tex`, lines 283--308 and 332--381,
`comparator:bell-pin`, `comparator:rough-overlap`, and
`comparator:actual-cutoffs`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Topology Matrix PermutationRepresentation TensorPower
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder symmDiff

noncomputable section

namespace ManyBody

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
variable (E : Finset (RegionConfig β X))

local notation "A" => RegionConfig β X
local notation "B" => ComplConfig β X
local notation "ι₀" => addedSiteSpace (addedSiteSpace β E) (Fin E.card)
local notation "ιe" => compressedSiteSpace β X (Fin E.card)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian (regionState_posSemidef X Ω)) E

local instance schmidtBellPhysicalWitnessConfigDecidableEq (k : ℕ) :
    DecidableEq (TensorPower.Config k ι₀) := Fintype.decidablePiFintype

open Classical in
/-- The supplied auxiliary-label mass bound produces one eventual unit
physical test vector for all matched cutoff families. Its overlap is with
the original supplied-label prevector; both auxiliary coordinate sets and
the selected mass are retained. Nonempty coordinate sets and normalization
of the inserted Bell vector are conclusions.

Source: area-law manuscript, `07-comparators.tex`, lines 283--308 and
332--381. The auxiliary-mass premise is the conclusion supplied by the
previously chosen Schmidt--Bell label sequence, not a regional tail premise. -/
theorem eventually_exists_suppliedSchmidtBell_physicalWitness {S : Type*}
    (hΩ : ‖Ω‖ = 1) (hz : 0 < z)
    (regions : List (Finset V))
    (hnested : regions.Pairwise fun D D' ↦ D ⊆ D' ∨ D' ⊆ D)
    (hdisjoint : ∀ D ∈ regions, Disjoint X D)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv β X) Ω
    let ψ : B × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (TensorPower.Config k ιe) := fun _ ↦
      WithLp.toLp 2 (fun x ↦ ∏ j, ψ ((fun v ↦ x j (some v)), x j none))
    let q : ℕ → ℝ := fun k ↦
      ‖toEuclideanLin (labelProj (subsystemPerm k ιe {none}) (ell k)) (Ψ k)‖ ^ 2
    (∀ᶠ k : ℕ in atTop,
      1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ q k) →
    (∀ o : Option (Option V), Nonempty (ι₀ o)) ∧
    ‖selectedBellVector ΩX E‖ = 1 ∧
    ∀ᶠ k : ℕ in atTop,
      let τ := schmidtBellWitnessEquiv β X E k
      let J := (addedSiteInsertion ιe (A × E) k (selectedBellVector ΩX E)).submatrix
        (bellInsertionCopyEquiv β X ↥E (Fin E.card) k) id
      let Pe := symProj (copyPerm ((o : Option {v // v ∉ X}) → ιe o) k)
      let P := J * Pe * Jᴴ
      let v : EuclideanSpace ℂ (TensorPower.Config k ι₀) := WithLp.toLp 2
        (schmidtBellSitePrevector β X E k ΩX (ell k) ∘ τ)
      ∃ Φ : EuclideanSpace ℂ (TensorPower.Config k ι₀),
        ‖Φ‖ = 1 ∧
        (fun x ↦ Φ x) ∈ symmetricSubspace k ι₀ ∧
        toEuclideanLin P Φ = Φ ∧
        toEuclideanLin (labelProj (subsystemPerm k ι₀ {none}) (ell k)) Φ = Φ ∧
        (z / (E.card : ℝ) ^ 2) ^ k /
          (4 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤
            ‖inner ℂ Φ (toEuclideanLin P v)‖ ^ 2 ∧
        ∀ (K : ℕ) (U Y : S → Fin K → Finset V) (Bsh Bexc : ℝ),
          (∀ D ∈ regions, regionEntropy Ω D ≤ Bsh) →
          (∀ j g, Disjoint X (U j g ∪ Y j g)) →
          (∀ j g (Q : Finset V), Q = U j g ∨ Q = U j g ∪ Y j g →
            ∃ D ∈ regions, (D ⊆ Q ∨ Q ⊆ D) ∧
              1 + Real.log (Fintype.card (RegionConfig β (D ∆ Q))) ≤ Bexc) →
          let a := (k : ℝ) * (Bsh / z + Bexc)
          let extRegion := fun Q : Finset V ↦ (Q \ X).image fun x ↦ some (some x)
          ∀ j g,
            toEuclideanLin
              (labelCutoff (subsystemPerm k ι₀ (extRegion (U j g))) a) Φ = Φ ∧
            toEuclideanLin
              (labelCutoff (subsystemPerm k ι₀ (extRegion (U j g ∪ Y j g))) a) Φ = Φ := by
  classical
  intro ΩX ψ Ψ q hmass
  have hw := eventually_exists_commonLabelCutoff_compressedTypical_bell_vector
    β Ω X E hΩ hz regions hnested hdisjoint ell hmass
  have hb := Matrix.norm_selectedBellVector ΩX E hz
  obtain ⟨x, _⟩ := Function.ne_iff.mp
    (fun h : Ω.ofLp = 0 ↦ (norm_ne_zero_iff.mp (hΩ.trans_ne one_ne_zero))
      ((WithLp.ofLp_eq_zero 2).mp h))
  have hE : 0 < E.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr fun he ↦ by
      simp [he, IsHermitian.spectralRestrictionMass] at hz)
  refine ⟨(fun
    | none => ⟨⟨0, hE⟩⟩
    | some none => (Finset.card_pos.mp hE).coe_sort
    | some (some v) => ⟨x v⟩), hb, ?_⟩
  filter_upwards [hw] with k ⟨φ, hφnorm, hφsym, hφBell, hφlabel, hφcuts,
    hφoverlap, hhalf, hbound⟩
  intro τ J Pe P v
  have hΦ := schmidtBellWitness_pullback_range β X E k ΩX φ
    (by simpa only [mem_invariantSubspace, permOp_mulVec] using hφsym) hφBell
  have hpull (A' : Matrix ((Fin k → A × E) × TensorPower.Config k ιe)
      ((Fin k → A × E) × TensorPower.Config k ιe) ℂ) (hA' : toEuclideanLin A' φ = φ) :
      toEuclideanLin (A'.submatrix τ τ) (WithLp.toLp 2 (φ ∘ τ)) =
        WithLp.toLp 2 (φ ∘ τ) := by
    simpa only [toEuclideanLin, toLpLin_apply, WithLp.ofLp_toLp,
      submatrix_mulVec_equiv, Function.comp_def, Equiv.apply_symm_apply] using!
      congrArg (fun w : EuclideanSpace ℂ ((Fin k → A × E) × TensorPower.Config k ιe) ↦
        WithLp.toLp 2 (w ∘ τ)) hA'
  refine ⟨WithLp.toLp 2 (φ ∘ τ),
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ τ.symm).norm_map φ).trans hφnorm,
    hΦ.1, hΦ.2, ?_, ?_, ?_⟩
  case refine_2 =>
    have hinner := inner_schmidtBellSitePrevector β X E k ΩX hz (ell k) φ hφBell
    have hpair :
        inner ℂ (WithLp.toLp 2 (φ ∘ τ)) (toEuclideanLin P v) =
          inner ℂ φ (schmidtBellSitePrevector β X E k ΩX (ell k)) :=
      ((isSymmetric_toEuclideanLin_iff.mpr
        (isHermitian_mul_mul_conjTranspose J
          (isHermitian_symProj (Ω := ((o : Option {v // v ∉ X}) → ιe o)) (k := k))))
        (WithLp.toLp 2 (φ ∘ τ)) v).symm.trans
        ((congrArg (fun w : EuclideanSpace ℂ (TensorPower.Config k ι₀) ↦ inner ℂ w v)
          hΦ.2).trans
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ τ.symm).inner_map_map φ
            (schmidtBellSitePrevector β X E k ΩX (ell k))))
    have hc :
        ‖(((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k)‖ ^ 2 =
          (z / (E.card : ℝ) ^ 2) ^ k := by
      rw [Complex.norm_pow, Complex.norm_div,
        Complex.norm_of_nonneg (Real.sqrt_nonneg z), Complex.norm_natCast,
        pow_right_comm (Real.sqrt z / (E.card : ℝ)) k 2, div_pow, Real.sq_sqrt hz.le]
    simp only [toEuclideanLin, toLpLin_apply] at hpair ⊢
    rw [hpair, hinner, norm_mul, mul_pow]
    erw [hc]
    erw [hφoverlap]
    simpa only [div_eq_mul_inv, one_mul] using!
      (mul_le_mul_of_nonneg_left hbound
        (pow_nonneg (div_nonneg hz.le (sq_nonneg (E.card : ℝ))) k))
  case refine_3 =>
    intro K U Y Bsh Bexc hsh hXY hmatch a extRegion j g
    have hmatched (Q D : Finset V) (hD : D ∈ regions) (hXQ : Disjoint X Q)
        (hDQ : D ⊆ Q ∨ Q ⊆ D)
        (hexc : 1 + Real.log (Fintype.card (RegionConfig β (D ∆ Q))) ≤ Bexc) :=
      toEuclideanLin_compressedPhysicalCutoff_of_matched β Ω X E k regions hD
        (hdisjoint D hD) hXQ hDQ hz (hsh D hD) hexc φ hφcuts
    have hcut (Q D : Finset V) (hD : D ∈ regions) (hXQ : Disjoint X Q)
        (hDQ : D ⊆ Q ∨ Q ⊆ D)
        (hexc : 1 + Real.log (Fintype.card (RegionConfig β (D ∆ Q))) ≤ Bexc) :
        toEuclideanLin (labelCutoff (subsystemPerm k ι₀ (extRegion Q)) a)
          (WithLp.toLp 2 (φ ∘ τ)) = WithLp.toLp 2 (φ ∘ τ) := by
      have htransport := hpull _ (hmatched Q D hD hXQ hDQ hexc)
      rw [labelCutoff_schmidtBellWitnessEquiv_exterior β X E k Q a] at htransport
      simp only [extRegion, toEuclideanLin, toLpLin_apply] at htransport ⊢
      exact htransport
    exact ⟨
      (hmatch j g (U j g) (Or.inl rfl)).elim (fun D hD ↦
        hcut (U j g) D hD.1
          ((hXY j g).mono_right Finset.subset_union_left) hD.2.1 hD.2.2),
      (hmatch j g (U j g ∪ Y j g) (Or.inr rfl)).elim (fun D hD ↦
        hcut (U j g ∪ Y j g) D hD.1 (hXY j g) hD.2.1 hD.2.2)⟩
  case refine_1 =>
    simpa only [τ, labelProj_schmidtBellWitnessEquiv_auxiliary] using! hpull _ hφlabel

end ManyBody

section SchmidtBellCommonCutoffs

/-!
# One Schmidt label sequence for the prevector and the common-cutoff overlap

The label sequence selected from the actual compressed Schmidt vector is
used throughout. Its original physical prevector retains its nonvanishing,
energy, symmetry and auxiliary-label properties, as well as the entropy
asymptotic. The same sequence works for every finite nested regional
collection: it admits a unit vector in the selected Bell range and all prescribed regional
cutoff ranges, with an inverse-polynomial overlap.

The auxiliary polynomial-mass premise of the common-cutoff implication is
discharged here by the original Schmidt selection theorem. No tail estimate,
symmetry, marginal identity, positive overlap or independently chosen label is
assumed. The normalized post vector uses the selected Bell coordinate set `E`
and the enumerated right auxiliary set `Fin E.card`. These are the literal
coordinate conventions of the existing selected-state constructions.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 130–147, 240–281 and 332–354,
  `comparator:prevector`, `comparator:high-label` and `comparator:rough-overlap`,
  manuscript revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Filter Topology
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
variable (E : Finset (RegionConfig β X))

local notation "A" => RegionConfig β X
local notation "B" => ComplConfig β X
local notation "ΩX" => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv β X) Ω
local notation "hρA" => Matrix.PosSemidef.partialTraceRight
  (posSemidef_vecMulVec_self_star ΩX)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian (regionState_posSemidef X Ω)) E

open Classical in
/-- One actual Schmidt-label sequence simultaneously has every original
prevector property and the common-cutoff overlap. The label selection theorem
is invoked once, before the regional collection is chosen; the eventual mass
bound needed by the cutoff argument is
derived from its same witness by an exact coordinate isometry.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130–147,
240–281 and 332–354. -/
theorem exists_label_sequence_schmidtBellPrevector_commonCutoffs
    (hΩ : ‖Ω‖ = 1) (hz : 0 < z)
    (H : Matrix (A × B) (A × B) ℂ) (E₀ : ℝ)
    (hE : H *ᵥ ΩX = (E₀ : ℂ) • (fun x ↦ ΩX x)) :
    let ψ : B × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let ι := compressedSiteSpace β X (Fin E.card)
    let χsite := WithLp.toLp 2
      (fun x : (f : Option {v // v ∉ X}) → ι f ↦
        compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (TensorPower.Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x : TensorPower.Config k ι ↦ ∏ j, χsite (x j))
    let a := compressedRegionalThreshold β Ω X E
    let post : (k : ℕ) → EuclideanSpace ℂ ((Fin k → A × E) × TensorPower.Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x ↦ (∏ j, selectedBellVector ΩX E (x.1 j)) * Ψ k x.2)
    ‖WithLp.toLp 2 ψ‖ = 1 ∧
      Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)) =
        Matrix.diagonal (fun r : Fin E.card ↦
          ((((Matrix.PosSemidef.isHermitian hρA).eigenvalues
            ((Finset.equivFin E).symm r)) / z : ℝ) : ℂ)) ∧
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let v := replicaPrevector ΩX E.card k (ell k)
        let P := labelProj (copyPerm (Fin E.card) k) (ell k)
        WithLp.toLp 2 v ≠ 0 ∧ ‖WithLp.toLp 2 v‖ ≤ 1 ∧
        (((k : ℝ)⁻¹ • replicaHamiltonian H k) ⊗ₖ
          (1 : Matrix ((Fin k → Fin E.card) × (Fin k → Fin E.card))
            ((Fin k → Fin E.card) × (Fin k → Fin E.card)) ℂ)) *ᵥ v = (E₀ : ℂ) • v ∧
        ((1 : Matrix (Fin k → (A × B)) (Fin k → (A × B)) ℂ) ⊗ₖ
          (P ⊗ₖ (1 : Matrix (Fin k → Fin E.card) (Fin k → Fin E.card) ℂ))) *ᵥ v = v ∧
        ((1 : Matrix (Fin k → (A × B)) (Fin k → (A × B)) ℂ) ⊗ₖ
          ((1 : Matrix (Fin k → Fin E.card) (Fin k → Fin E.card) ℂ) ⊗ₖ P)) *ᵥ v = v ∧
        (∀ σ : Equiv.Perm (Fin k),
          (permOp (copyPerm (A × B) k) σ ⊗ₖ
            (permOp (copyPerm (Fin E.card) k) σ ⊗ₖ permOp (copyPerm (Fin E.card) k) σ)) *ᵥ v = v)) ∧
      (∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → B) (Fin k → B) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
              (fun x : (Fin k → B) × (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
      Asymptotics.IsLittleO atTop
        (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) *
          vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
            (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ ↦ (k : ℝ)) ∧
      ∀ (regions : List (Finset V)),
        regions.Pairwise (fun C D ↦ C ⊆ D ∨ D ⊆ C) →
        (∀ C ∈ regions, Disjoint X C) →
      let q : ℕ → ℝ := fun k ↦
        ‖toEuclideanLin (labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2
      let r : ℕ → ℝ := fun k ↦
        ‖toEuclideanLin
          (commonLabelCutoff ι k (regions.map (exteriorRegion X)) (a k) *
            labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2
      ∀ᶠ k : ℕ in atTop,
        let e := Equiv.arrowProdEquivProdArrow (Fin k)
          (fun _ ↦ RegionConfig β X × E) (fun _ ↦ (f : Option {v // v ∉ X}) → ι f)
        ∃ φ : EuclideanSpace ℂ ((Fin k → RegionConfig β X × E) × TensorPower.Config k ι),
          ‖φ‖ = 1 ∧
          (fun x ↦ φ (e x)) ∈ invariantSubspace
            (copyPerm ((RegionConfig β X × E) × ((f : Option {v // v ∉ X}) → ι f)) k) ∧
          toEuclideanLin
            ((finKronecker fun _ : Fin k ↦ selectedBellProjection ΩX E) ⊗ₖ
              (1 : Matrix (TensorPower.Config k ι) (TensorPower.Config k ι) ℂ)) φ = φ ∧
          toEuclideanLin
            ((1 : Matrix (Fin k → RegionConfig β X × E)
              (Fin k → RegionConfig β X × E) ℂ) ⊗ₖ
                labelProj (subsystemPerm k ι {none}) (ell k)) φ = φ ∧
          (∀ C ∈ regions,
            toEuclideanLin
              ((1 : Matrix (Fin k → RegionConfig β X × E)
                (Fin k → RegionConfig β X × E) ℂ) ⊗ₖ
                  labelCutoff (subsystemPerm k ι (exteriorRegion X C))
                    (a k (exteriorRegion X C))) φ = φ) ∧
          ‖⟪φ, toEuclideanLin
            ((1 : Matrix (Fin k → RegionConfig β X × E)
              (Fin k → RegionConfig β X × E) ℂ) ⊗ₖ
                labelProj (subsystemPerm k ι {none}) (ell k)) (post k)⟫_ℂ‖ ^ 2 = r k ∧
          q k / 2 ≤ r k ∧
          1 / (4 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ r k := by
  classical
  intro ψ ι χsite Ψ a post
  have hzX : 0 < Matrix.IsHermitian.spectralRestrictionMass
      (Matrix.PosSemidef.isHermitian hρA) E := hz
  have hΩX : ‖ΩX‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv β X)).norm_map Ω).trans hΩ
  obtain ⟨hψ, hdiag, ell, hpre, hmass, hentropy⟩ :=
    TensorPower.exists_label_sequence_schmidtBellPrevector ΩX E hzX hΩX H E₀ hE
  refine ⟨hψ, hdiag, ell, hpre, hmass, hentropy, ?_⟩
  intro regions hnested hdisjoint q r
  have hmassSite : ∀ᶠ k : ℕ in atTop,
      1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ q k := by
    filter_upwards [hmass] with k hk
    have he : q k = ‖WithLp.toLp 2
        (((1 : Matrix (Fin k → ComplConfig β X)
          (Fin k → ComplConfig β X) ℂ) ⊗ₖ
            labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
          (fun x ↦ ∏ j, ψ (x.1 j, x.2 j)))‖ ^ 2 :=
      norm_sq_labelProj_compressedTypicalSite_prod β X k Ω E (ell k)
    rw [he]
    simpa only [one_div, Nat.cast_pow] using hk
  exact eventually_exists_commonLabelCutoff_compressedTypical_bell_vector
    β Ω X E hΩ hz regions hnested hdisjoint ell hmassSite

end ManyBody
end

end SchmidtBellCommonCutoffs
