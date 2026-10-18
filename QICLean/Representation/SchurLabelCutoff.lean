import QICLean.Representation.SchurLabelTails
import QICLean.Analysis.ShiftedDensityTruncation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-! # The closed spectral cutoff of the Schur-label observable

The finite sum of selected label projections is exactly the closed spectral
cutoff used in the rough upper comparison. OpenAI area-law manuscript,
`07-comparators.tex`, lines 332–354.
-/

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace Matrix.IsOrthogonalResolution

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
  {P : ι → Matrix n n ℂ} (hP : Matrix.IsOrthogonalResolution P)

/-- Functional calculus acts on the real coordinates of a finite Hermitian
resolution. This identifies the closed cutoff in source07, lines 332–354. -/
private theorem cfc_hom (hH : ∀ i, (P i).IsHermitian) (a : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (hP.hom (fun i ↦ (a i : ℂ))) = hP.hom (fun i ↦ (f (a i) : ℂ)) := by
  let : ContinuousFunctionalCalculus ℂ (ι → ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (ι → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let φ : (ι → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ :=
    { hP.hom with
      map_star' := by
        intro g
        change hP.hom (star g) = star (hP.hom g)
        simp only [hP.hom_apply, star_sum, star_smul, Pi.star_apply]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Matrix.star_eq_conjTranspose, (hH i).eq] }
  have hfinite : (⋃ i, spectrum ℝ (a i : ℂ)).Finite := by
    have hscalar (i : ι) : spectrum ℝ (a i : ℂ) = {a i} :=
      spectrum.scalar_eq (𝕜 := ℝ) (A := ℂ) (a i)
    simp_rw [hscalar]
    exact Set.finite_iUnion fun i ↦ Set.finite_singleton (a i)
  have ha : IsSelfAdjoint (fun i ↦ (a i : ℂ)) := by
    change star (fun i ↦ (a i : ℂ)) = (fun i ↦ (a i : ℂ))
    funext i
    simp
  have hh := φ.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) f
    (fun i ↦ (a i : ℂ)) (by rw [Pi.spectrum_eq]; exact hfinite.continuousOn f)
    hP.continuous_hom ha (hP.isHermitian_hom hH a).isSelfAdjoint
  have hp : cfc f (fun i ↦ (a i : ℂ)) = fun i ↦ (f (a i) : ℂ) := by
    rw [cfc_map_pi (S := ℂ) f (fun i ↦ (a i : ℂ)) (hfinite.continuousOn f) ha
      (fun i ↦ by change star (a i : ℂ) = (a i : ℂ); simp)]
    funext i
    exact cfc_algebraMap (a i) f
  rw [hp] at hh
  exact hh.symm

end Matrix.IsOrthogonalResolution

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]

/-- The finite label sum is the closed lower spectral cutoff, including labels
exactly at the threshold. OpenAI area-law manuscript, `07-comparators.tex`,
lines 332–354. -/
theorem labelCutoff_eq_spectralProjectionGE (φ : G →* Equiv.Perm X) (a : ℝ) :
    labelCutoff φ a = Matrix.spectralProjectionGE (-labelEntropy φ) (-a) := by
  classical
  let R := isOrthogonalResolution_labelProj φ
  have hneg : -labelEntropy φ = R.hom (fun l ↦ ((-Real.log l.dim : ℝ) : ℂ)) := by
    simp only [Matrix.IsOrthogonalResolution.hom_apply, labelEntropy,
      labelObservable, Finset.sum_neg_distrib, neg_smul, Complex.ofReal_neg]
  rw [Matrix.spectralProjectionGE, hneg,
    Matrix.IsOrthogonalResolution.cfc_hom R (isHermitian_labelProj φ)]
  simp only [neg_le_neg_iff, labelCutoff, labelObservable,
    Matrix.IsOrthogonalResolution.hom_apply]

end PermutationRepresentation
