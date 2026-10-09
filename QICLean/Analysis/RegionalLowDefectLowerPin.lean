/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaLowDefectRoughLowerPin
import QICLean.Analysis.RegionalLowDefectProjection
import QICLean.Representation.RegionalReplicaMetric
import QICLean.Representation.RegionalPhysicalVector

/-!
# A uniform rough regional lower bound in one symmetric coordinate space

The original physical vector and auxiliary labels determine one global
low-defect projection. Each regional estimate is transported to this
projection by the actual grouping equivalence. The polynomial constant is
then replaced by a maximum over the finite set of physical cuts, before
the copy number, vector, labels, cutoffs or symmetric coordinates are chosen.

The rough estimate requires no marginal moment hypothesis. The projection
transport and the inverse-compression bound are derived from their original
definitions and the regional comparison.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 421--456 and 585--615,
`comparator:lower-pin`, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local instance regionalLowerPin_decidableEqPhysical :
    DecidableEq ((v : V) → β v) := Fintype.decidablePiFintype

local instance regionalLowerPin_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k (addedSiteSpace (addedSiteSpace β C) R)) :=
  Fintype.decidablePiFintype

local instance regionalLowerPin_decidableEqGroupedConfig
    (Q Y : Finset V) (k : ℕ) :
    DecidableEq (Config k (regionalFiveFactorSpace β C R Q Y)) :=
  Fintype.decidablePiFintype

private theorem regional_lower_pin_pullback
    (Ω : ((v : V) → β v) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (Q Y : Finset V) (hQY : Disjoint Q Y) (t : ℝ) (k : ℕ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ)
    {b₀ b : ℝ} (hb₀ : 0 < b₀) (hbb : b₀ ≤ b)
    (hpin :
      let ι := regionalFiveFactorSpace β C R Q Y
      let ψ := Ω ∘ (FiniteProduct.regionalPhysicalEquiv β Q Y hQY).symm
      let η := fiveFactorCopiesEquiv ι k
      let P := (replicaLowDefectProjection (C := C) (R := R)
        ψ k ellC ellR τ).submatrix η η
      let W := replicaMetric ι t k
      b₀⁻¹ • P ≤ ((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)
    (n : ℕ) (Z : Matrix (Config k (addedSiteSpace (addedSiteSpace β C) R)) (Fin n) ℂ) :
    let P := globalReplicaLowDefectProjection β C R Ω k ellC ellR τ
    let W := replicaMetric (addedSiteSpace (addedSiteSpace β C) R) t k
    let A := ((W (regionalOriginalRegion Q Y {0, 3}))⁻¹ *
      (W (regionalOriginalRegion Q Y {2, 4}))⁻¹ *
        W (regionalOriginalRegion Q Y {1})) ^ 2
    b⁻¹ • (Zᴴ * P * Z) ≤ Zᴴ * A * Z := by
  intro P W A
  let ι := regionalFiveFactorSpace β C R Q Y
  let ψ := Ω ∘ (FiniteProduct.regionalPhysicalEquiv β Q Y hQY).symm
  let η := fiveFactorCopiesEquiv ι k
  let e := regionalFiveFactorCopyEquiv β C R Q Y hQY k
  let Pc := (replicaLowDefectProjection (C := C) (R := R)
    ψ k ellC ellR τ).submatrix η η
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 :=
    (FiniteProduct.norm_regionalPhysicalVector β Ω Q Y hQY).trans hΩ
  have hPc : 0 ≤ Pc := by
    exact ((Matrix.nonneg_iff_posSemidef.mp
      (isStarProjection_replicaLowDefectProjection ψ hψ k ellC ellR τ).nonneg).submatrix η).nonneg
  have hb : 0 < b := hb₀.trans_le hbb
  have hweak : b⁻¹ • Pc ≤
      ((replicaMetric ι t k {0, 3})⁻¹ *
        (replicaMetric ι t k {2, 4})⁻¹ * replicaMetric ι t k {1}) ^ 2 :=
    (smul_le_smul_of_nonneg_right ((inv_le_inv₀ hb hb₀).mpr hbb) hPc).trans hpin
  have hP : Pc.submatrix e e = P :=
    regionalFiveFactor_lowDefectProjection_eq_global β C R Ω hΩ Q Y hQY k ellC ellR τ
  have hA := replicaMetric_inv_mul_inv_mul_sq_submatrix_regionalFiveFactorCopyEquiv
    β C R Q Y hQY t k {0, 3} {2, 4} {1}
  have hpull : b⁻¹ • P ≤ A := by
    apply Matrix.le_iff.mpr
    simpa only [hA, Matrix.submatrix_sub, Matrix.submatrix_smul, hP,
      Matrix.submatrix_submatrix, Function.comp_def, Equiv.symm_apply_apply,
      Matrix.submatrix_id_id] using (Matrix.le_iff.mp hweak).submatrix e
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using
    (Matrix.le_iff.mp hpull).conjTranspose_mul_mul_same Z

variable [∀ v, Nonempty (β v)] [Nonempty C] [Nonempty R]

/-- One rough polynomial constant works for all regional cuts, with the
same global low-defect projection and any fixed symmetric coordinates.
Only the original unit vector and original auxiliary-label bound enter;
no marginal moment assumption is imposed. Source: `07-comparators.tex`,
`comparator:lower-pin`, lines 585--615. -/
theorem exists_globalReplicaLowDefectProjection_rough_lower_pin
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (k : ℕ) (Ω : ((v : V) → β v) → ℂ),
      ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ S ε : ℝ),
      0 ≤ τ → τ ≤ 1 / 2 →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let P := globalReplicaLowDefectProjection β C R Ω k ellC ellR τ
      let d := Real.log (Fintype.card C) + Real.log (Fintype.card R)
      let b := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) *
        (((k : ℝ) + 2) ^ c * Real.exp
          (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) + (2 * t) * ε))
      ∀ (n : ℕ) (Z : Matrix (Config k (addedSiteSpace (addedSiteSpace β C) R)) (Fin n) ℂ),
        Z * Zᴴ = symProj (copyPerm ((v : Option (Option V)) →
          addedSiteSpace (addedSiteSpace β C) R v) k) →
        IsStarProjection (Zᴴ * P * Z) ∧
          ∀ (Q Y : Finset V), Disjoint Q Y →
            let W := replicaMetric (addedSiteSpace (addedSiteSpace β C) R) t k
            let A := ((W (regionalOriginalRegion Q Y {0, 3}))⁻¹ *
              (W (regionalOriginalRegion Q Y {2, 4}))⁻¹ *
                W (regionalOriginalRegion Q Y {1})) ^ 2
            b⁻¹ • (Zᴴ * P * Z) ≤ Zᴴ * A * Z := by
  classical
  let ι := fun p : Finset V × Finset V => regionalFiveFactorSpace β C R p.1 p.2
  choose c₀ _hc₀ hlocal using fun p : Finset V × Finset V =>
    exists_replicaLowDefectProjection_rough_lower_pin (ι p) ht htsmall
  let D := fun p : Finset V × Finset V =>
    max ((Fintype.card (ι p 0) * Fintype.card C) ^ 2)
      ((Fintype.card (ι p 2) * Fintype.card R) ^ 2)
  let f := fun p : Finset V × Finset V => c₀ p + (D p : ℝ)
  let c := max 0 ((Finset.univ : Finset (Finset V × Finset V)).sup'
    Finset.univ_nonempty f)
  have hfc (p : Finset V × Finset V) : f p ≤ c :=
    (Finset.le_sup' f (Finset.mem_univ p)).trans (le_max_right _ _)
  refine ⟨c, le_max_left _ _, ?_⟩
  intro k Ω hΩ ellC ellR τ S ε hτ hτhalf hlabel P d b n Z hZZ
  refine ⟨(globalReplicaLowDefectProjection_properties β C R Ω hΩ k ellC ellR τ).2.2
    n Z hZZ, ?_⟩
  intro Q Y hQY W A
  let ψ := Ω ∘ (FiniteProduct.regionalPhysicalEquiv β Q Y hQY).symm
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 :=
    (FiniteProduct.norm_regionalPhysicalVector β Ω Q Y hQY).trans hΩ
  let b₀ := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) *
    (((k : ℝ) + 2) ^ f (Q, Y) * Real.exp
      (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) + (2 * t) * ε))
  have hb₀ : 0 < b₀ := by dsimp only [b₀]; positivity
  have hbb : b₀ ≤ b := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le
        (by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (hfc (Q, Y)))
      (Real.exp_pos _).le
  exact regional_lower_pin_pullback β C R Ω hΩ Q Y hQY t k ellC ellR τ
    hb₀ hbb (hlocal (Q, Y) k ψ hψ ellC ellR τ S ε hτ hτhalf hlabel).1 n Z

end Matrix
