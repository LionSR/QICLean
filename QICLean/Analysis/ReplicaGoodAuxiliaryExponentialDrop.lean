/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodAuxiliarySpectralSupport
import QICLean.Analysis.SpectralExponentialDrop
import QICLean.Representation.CompatiblePhysicalLabel

/-!
# Auxiliary label factors in an excitation-component exponential

Let Γ be the actual density retaining all five good-copy factors Q, Y, V, C
and R and tracing only the bad copies of the same excitation component.
The original whole-copy auxiliary labels give closed spectral support of Γ
above the thresholds L_C and L_R. Consequently, for a nonnegative a, the
exponential of the negative merged-label observable is bounded in its Γ
trace by exp(-a(L_C+L_R)) times the exponential of the two merge deficits
minus the physical label observable.

The bound is derived by removing the two shifted auxiliary label observables
successively. The needed central observables commute because their actual
regions are nested or disjoint. No commutation of Γ with those observables
is assumed. All good middle physical coordinates Y remain present.

Only the original vector's two auxiliary label conditions and a ≥ 0 are
assumed. The one-copy vector and the original vector are arbitrary. Zero
components, zero copies and empty coordinate factors are included, without
normalization or division by the component mass. The whole-copy restriction,
the bad-copy estimate and the inverse metric comparison are separate results.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `07-comparators.tex`, lines 481–522 and 553–569,
  `comparator:good-auxiliary`, `comparator:merge-decomposition` and
  `comparator:component-inverse`, at manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix TensorPower PermutationRepresentation
open scoped Matrix Kronecker Matrix.Norms.Operator ComplexOrder MatrixOrder

namespace Matrix

/-- The actual good-copy auxiliary labels contribute their two lower
thresholds to the exponential estimate. No normalization or original
permutation symmetry is assumed.

References: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 481–522 and 553–569,
`comparator:good-auxiliary`, `comparator:merge-decomposition`, and
`comparator:component-inverse`, at manuscript revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is an auxiliary exponential reduction, before any whole-copy or
inverse-metric comparison. -/
theorem replicaGoodConfigurationMarginal_exp_mergedLabel_le
    (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (lC lR : IrrepLabel (Equiv.Perm (Fin k)))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (hC : ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
        (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
      (labelProj (copyPerm (ι 3) k) lC ⊗ₖ
        (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ))) *ᵥ u = u)
    (hR : ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
        (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
      ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ
        labelProj (copyPerm (ι 4) k) lR)) *ᵥ u = u)
    (a : ℝ) (ha : 0 ≤ a) :
    let Γ := replicaGoodConfigurationMarginal ι Ω k B u
    let LC := Real.log lC.dim - (B.card : ℝ) * Real.log (Fintype.card (ι 3)) -
      Real.log (k.choose B.card)
    let LR := Real.log lR.dim - (B.card : ℝ) * Real.log (Fintype.card (ι 4)) -
      Real.log (k.choose B.card)
    let m := Bᶜ.card
    let F := fun A => labelEntropy (subsystemPerm m ι A)
    let DC := F {0} + F {3} - F {0, 3}
    let DR := F {2} + F {4} - F {2, 4}
    (Γ * NormedSpace.exp ((-a : ℂ) • (F {0, 3} + F {2, 4} - F {1}))).trace.re ≤
      Real.exp (-a * (LC + LR)) *
        (Γ * NormedSpace.exp ((a : ℂ) •
          (DC + DR - physicalMergeDeficit ι m))).trace.re := by
  intro Γ LC LR m F DC DR
  have hΓ : Γ.PosSemidef := (posSemidef_vecMulVec_self_star _).partialTraceRight
  have hs := spectralProjectionGE_auxiliaryLabelEntropy_mul_replicaGoodConfigurationMarginal
    ι Ω k B lC lR u hC hR
  have hF (A : Finset (Fin 5)) : (F A).IsHermitian :=
    isHermitian_labelObservable _ _
  let T := DC + DR - physicalMergeDeficit ι m
  have hT : T.IsHermitian :=
    ((((hF {0}).add (hF {3})).sub (hF {0, 3})).add
      (((hF {2}).add (hF {4})).sub (hF {2, 4}))).sub
        (((hF {0}).add (hF {2})).sub (hF {1}))
  have hc (A D : Finset (Fin 5)) (h : A ⊆ D ∨ D ⊆ A ∨ Disjoint A D) :
      Commute (F A) (F D) :=
    commute_labelObservables_subsystemPerm_of_laminar ι m A D h _ _
  have hmerge : F {0, 3} + F {2, 4} - F {1} = F {3} + F {4} - T := by
    dsimp only [T, DC, DR, physicalMergeDeficit, F]
    abel
  have hTform : T = F {3} + F {4} - (F {0, 3} + F {2, 4} - F {1}) := by
    rw [hmerge]
    abel
  have h3T : Commute (F {3}) T := by
    simpa only [hTform] using
      ((hc {3} {3} (by decide)).add_right (hc {3} {4} (by decide))).sub_right
        (((hc {3} {0, 3} (by decide)).add_right
          (hc {3} {2, 4} (by decide))).sub_right (hc {3} {1} (by decide)))
  have h4T : Commute (F {4}) T := by
    simpa only [hTform] using
      ((hc {4} {3} (by decide)).add_right (hc {4} {4} (by decide))).sub_right
        (((hc {4} {0, 3} (by decide)).add_right
          (hc {4} {2, 4} (by decide))).sub_right (hc {4} {1} (by decide)))
  let X := F {3} - (LC : ℂ) • 1
  let Y := F {4} - (LR : ℂ) • 1
  have hX : X.IsHermitian :=
    (hF {3}).sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have hY : Y.IsHermitian :=
    (hF {4}).sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have hXT : Commute X T :=
    h3T.sub_left ((Commute.one_left T).smul_left (LC : ℂ))
  have hYT : Commute Y T :=
    h4T.sub_left ((Commute.one_left T).smul_left (LR : ℂ))
  have hXY : Commute X Y :=
    ((hc {3} {4} (by decide)).sub_right
      ((Commute.one_right (F {3})).smul_right (LR : ℂ))).sub_left
        ((Commute.one_left Y).smul_left (LC : ℂ))
  have hdropC := hΓ.re_trace_mul_exp_smul_sub_le_of_spectralProjectionGE_mul
    hX (hT.sub hY) (hXT.sub_right hXY) ha hs.1
  have hdropR := hΓ.re_trace_mul_exp_smul_sub_le_of_spectralProjectionGE_mul
    hY hT hYT ha hs.2
  set_option backward.isDefEq.respectTransparency false in
  have hscalar (s : ℝ) : NormedSpace.exp ((s : ℂ) •
      (1 : Matrix (Config m ι) (Config m ι) ℂ)) = (Real.exp s : ℂ) • 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one, ← Complex.exp_eq_exp_ℂ,
      Complex.ofReal_exp] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℂ)
        (𝔸 := Matrix (Config m ι) (Config m ι) ℂ) (s : ℂ)).symm
  have hshift : (-a : ℂ) • (F {0, 3} + F {2, 4} - F {1}) =
      (a : ℂ) • (T - Y - X) + ((-a * (LC + LR) : ℝ) : ℂ) • 1 := by
    simp only [hmerge, X, Y, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_add, smul_add, smul_sub, neg_smul, smul_smul]
    module
  have hfactor : NormedSpace.exp ((-a : ℂ) •
      (F {0, 3} + F {2, 4} - F {1})) =
      (Real.exp (-a * (LC + LR)) : ℂ) • NormedSpace.exp ((a : ℂ) • (T - Y - X)) := by
    rw [hshift, NormedSpace.exp_add_of_commute
      ((Commute.one_right ((a : ℂ) • (T - Y - X))).smul_right
        ((-a * (LC + LR) : ℝ) : ℂ)), hscalar]
    simp only [Matrix.mul_smul, mul_one]
  simpa only [hfactor, Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left (hdropC.trans hdropR) (Real.exp_pos (-a * (LC + LR))).le

end Matrix
