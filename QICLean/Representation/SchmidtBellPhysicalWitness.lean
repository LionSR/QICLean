/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedTypicalCommonBellVector
import QICLean.Entropy.CompressedPhysicalMatchedCutoffs
import QICLean.Representation.CoherentSymbol
import QICLean.Representation.SchmidtBellWitnessRange
import QICLean.Representation.SchmidtBellPrevectorOverlap

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

namespace FiniteProduct

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
variable (E : Finset (Configuration β X))

local notation "A" => Configuration β X
local notation "B" => Configuration β Xᶜ
local notation "ι₀" => addedSiteSpace (addedSiteSpace β E) (Fin E.card)
local notation "ιe" => compressedSiteSpace β X (Fin E.card)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian (reducedPure_posSemidef β Ω X)) E

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
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let ψ : B × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (Config k ιe) := fun k ↦
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
      let Pe := symProj (copyPerm ((o : Option ↥(Xᶜ)) → ιe o) k)
      let P := J * Pe * Jᴴ
      let v : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2
        (schmidtBellSitePrevector β X E k ΩX (ell k) ∘ τ)
      ∃ Φ : EuclideanSpace ℂ (Config k ι₀),
        ‖Φ‖ = 1 ∧
        (fun x ↦ Φ x) ∈ symmetricSubspace k ι₀ ∧
        toEuclideanLin P Φ = Φ ∧
        toEuclideanLin (labelProj (subsystemPerm k ι₀ {none}) (ell k)) Φ = Φ ∧
        (z / (E.card : ℝ) ^ 2) ^ k /
          (4 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤
            ‖inner ℂ Φ (toEuclideanLin P v)‖ ^ 2 ∧
        ∀ (K : ℕ) (U Y : S → Fin K → Finset V) (Bsh Bexc : ℝ),
          (∀ D ∈ regions, entropy β Ω D ≤ Bsh) →
          (∀ j g, Disjoint X (U j g ∪ Y j g)) →
          (∀ j g (Q : Finset V), Q = U j g ∨ Q = U j g ∪ Y j g →
            ∃ D ∈ regions, (D ⊆ Q ∨ Q ⊆ D) ∧
              1 + Real.log (Fintype.card (Configuration β (D ∆ Q))) ≤ Bexc) →
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
  refine ⟨WithLp.toLp 2 (φ ∘ τ),
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ τ.symm).norm_map φ).trans hφnorm,
    hΦ.1, hΦ.2, ?_, ?_, ?_⟩
  case refine_2 =>
    have hinner := inner_schmidtBellSitePrevector β X E k ΩX hz (ell k) φ hφBell
    letI : DecidableEq (Config k ι₀) := Fintype.decidablePiFintype
    have hpair :
        inner ℂ (WithLp.toLp 2 (φ ∘ τ)) (toEuclideanLin P v) =
          inner ℂ φ (schmidtBellSitePrevector β X E k ΩX (ell k)) :=
      ((isSymmetric_toEuclideanLin_iff.mpr
        (isHermitian_mul_mul_conjTranspose J
          (isHermitian_symProj (Ω := ((o : Option ↥(Xᶜ)) → ιe o)) (k := k))))
        (WithLp.toLp 2 (φ ∘ τ)) v).symm.trans
        ((congrArg (fun w : EuclideanSpace ℂ (Config k ι₀) ↦ inner ℂ w v)
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
    done
  all_goals done

end FiniteProduct
