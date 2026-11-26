/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Twirl
import QICLean.ManyBody.Sites.Product.ProductOperatorTrace
import QICLean.Spectral.Eigenvalue.HermitianExtremalEigenvalues
import QICLean.Spectral.Filter.PositiveReplacement
import QICLean.Analysis.FunctionalCalculus.TraceCFC
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Ground spectral cutoffs and common ground vectors on disjoint regions

The spectral projection of a Hermitian operator `A` onto the eigenspace of its least eigenvalue
is a function of `A`, so it is supported on the region of `A`; its trace is the multiplicity of
the least eigenvalue, which is nonzero. Traces of products of operators supported on disjoint
regions factorize, so the product of the ground projections of three Hermitian operators on
pairwise disjoint regions is nonzero, and any nonzero column of it is a common vector attaining
the three least eigenvalues. It can be normalized. No common ground vector is assumed.

The finite-family version with a unit vector is
`ManyBody.exists_common_unit_ground_of_disjoint_family`; the statements here keep the least
eigenvalues `minEigenvalue` of the three operators as the energies.

Moved from TNLean, `TNLean/Circuit/SupportedGroundSpace.lean` and
`TNLean/Circuit/SupportedNormalizedGroundSpace.lean`, restated on a system of sites with
nonempty basis types (in place of `Fin d` at every site with `d ≠ 0`).

## Main results

* `ManyBody.exists_supported_ground_cutoff` — a supported ground cutoff of nonzero trace.
* `ManyBody.trace_mul_ne_zero_of_disjoint` — nonzero traces on disjoint regions multiply.
* `ManyBody.exists_common_ground_of_disjoint`,
  `ManyBody.exists_normalized_common_ground_of_disjoint` — a common nonzero, and a common unit,
  ground vector of three operators on disjoint regions.

## References

* Arad, Kitaev, Landau and Vazirani, arXiv:1301.1162v1, Section 6.1, the normalization argument
  preceding Theorem 6.1.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder BigOperators

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- A supported Hermitian operator has a supported ground spectral cutoff of nonzero trace,
annihilated by the subtraction of its least eigenvalue. AKLV, arXiv:1301.1162v1, Section 6.1,
the normalization. -/
theorem exists_supported_ground_cutoff [∀ v, Nonempty (X v)] {S : Finset V}
    {A : Matrix (Config X) (Config X) ℂ} (hA : A.IsHermitian)
    (hs : A ∈ supportedOperators X S) :
    ∃ P : Matrix (Config X) (Config X) ℂ,
      P ∈ supportedOperators X S ∧ Matrix.trace P ≠ 0 ∧
      (A - (minEigenvalue hA : ℂ) • 1) * P = 0 := by
  classical
  let groundEnergy := minEigenvalue hA
  let f : ℝ → ℝ := fun x => if x = groundEnergy then 1 else 0
  let P := cfc f A
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn g
  have hshift : cfc (fun x : ℝ => x - groundEnergy) A = A - (groundEnergy : ℂ) • 1 := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => groundEnergy) A (hc _) (hc _),
      cfc_id' ℝ A hA.isSelfAdjoint, cfc_const groundEnergy A hA.isSelfAdjoint,
      Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  have hkill : (A - (groundEnergy : ℂ) • 1) * P = 0 := by
    rw [← hshift, show P = cfc f A from rfl, ← cfc_mul _ _ A (hc _) (hc _)]
    have hfun : (fun x : ℝ => (x - groundEnergy) * f x) = fun _ => 0 := by
      funext x
      by_cases hx : x = groundEnergy <;> simp [f, hx]
    rw [hfun, cfc_const_zero]
  let T := Finset.univ.filter fun i => hA.eigenvalues i = groundEnergy
  have hT : T.Nonempty := by
    obtain ⟨i, hi⟩ := minEigenvalue_achieved hA
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have htrace : Matrix.trace P = (T.card : ℂ) := by
    simp [P, hA.cfc_eq, hA.trace_cfc_eq_sum, f, T]
  refine ⟨P, cfc_mem_supportedOperators f hs, ?_, hkill⟩
  rw [htrace]
  exact_mod_cast Finset.card_ne_zero.mpr hT

/-- On disjoint regions, nonzero traces force a nonzero trace of the product. AKLV,
arXiv:1301.1162v1, Section 6.1, the tensor product of regional ground states. -/
theorem trace_mul_ne_zero_of_disjoint {S T : Finset V} (hST : Disjoint S T)
    {A B : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X S) (hB : B ∈ supportedOperators X T)
    (htrA : Matrix.trace A ≠ 0) (htrB : Matrix.trace B ≠ 0) :
    Matrix.trace (A * B) ≠ 0 := by
  have hfactor := trace_piKronecker_mul_mul_mul_trace hST
    (fun v : V => (1 : Matrix (X v) (X v) ℂ)) hA hB
  rw [piKronecker_one, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul] at hfactor
  intro hzero
  rw [hzero, zero_mul] at hfactor
  exact mul_ne_zero htrA htrB hfactor.symm

variable [∀ v, Nonempty (X v)]

/-- Three Hermitian operators on pairwise disjoint regions have a common nonzero vector
attaining their least eigenvalues. AKLV, arXiv:1301.1162v1, Section 6.1. -/
theorem exists_common_ground_of_disjoint
    {S T R : Finset V} (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    {A B C : Matrix (Config X) (Config X) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hsA : A ∈ supportedOperators X S) (hsB : B ∈ supportedOperators X T)
    (hsC : C ∈ supportedOperators X R) :
    ∃ v : Config X → ℂ, v ≠ 0 ∧
      (A - (minEigenvalue hA : ℂ) • 1) *ᵥ v = 0 ∧
      (B - (minEigenvalue hB : ℂ) • 1) *ᵥ v = 0 ∧
      (C - (minEigenvalue hC : ℂ) • 1) *ᵥ v = 0 := by
  classical
  obtain ⟨P, hsP, hP, hAP⟩ := exists_supported_ground_cutoff hA hsA
  obtain ⟨Q, hsQ, hQ, hBQ⟩ := exists_supported_ground_cutoff hB hsB
  obtain ⟨W, hsW, hW, hCW⟩ := exists_supported_ground_cutoff hC hsC
  have hsPQ : P * Q ∈ supportedOperators X (S ∪ T) :=
    mul_mem (supportedOperators_mono Finset.subset_union_left hsP)
      (supportedOperators_mono Finset.subset_union_right hsQ)
  have hPQ := trace_mul_ne_zero_of_disjoint hST hsP hsQ hP hQ
  have hPQW := trace_mul_ne_zero_of_disjoint (Finset.disjoint_union_left.mpr ⟨hSR, hTR⟩)
    hsPQ hsW hPQ hW
  have hnonzero : P * Q * W ≠ 0 := by
    intro hzero
    exact hPQW (by rw [hzero, Matrix.trace_zero])
  have hBP : Commute (B - (minEigenvalue hB : ℂ) • 1) P :=
    (commute_of_mem_supportedOperators_of_disjoint hsB hsP hST.symm).sub_left
      ((Commute.one_left P).smul_left _)
  have hCP : Commute (C - (minEigenvalue hC : ℂ) • 1) P :=
    (commute_of_mem_supportedOperators_of_disjoint hsC hsP hSR.symm).sub_left
      ((Commute.one_left P).smul_left _)
  have hCQ : Commute (C - (minEigenvalue hC : ℂ) • 1) Q :=
    (commute_of_mem_supportedOperators_of_disjoint hsC hsQ hTR.symm).sub_left
      ((Commute.one_left Q).smul_left _)
  have hkillA : (A - (minEigenvalue hA : ℂ) • 1) * (P * Q * W) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAP, Matrix.zero_mul, Matrix.zero_mul]
  have hkillB : (B - (minEigenvalue hB : ℂ) • 1) * (P * Q * W) = 0 := by
    rw [Matrix.mul_assoc P Q W, hBP.left_comm (Q * W),
      ← Matrix.mul_assoc (B - (minEigenvalue hB : ℂ) • 1) Q W,
      hBQ, Matrix.zero_mul, Matrix.mul_zero]
  have hkillC : (C - (minEigenvalue hC : ℂ) • 1) * (P * Q * W) = 0 := by
    rw [Matrix.mul_assoc P Q W, hCP.left_comm (Q * W), hCQ.left_comm W,
      hCW, Matrix.mul_zero, Matrix.mul_zero]
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hnonzero
  obtain ⟨y, hxy⟩ := Function.ne_iff.mp hx
  refine ⟨(P * Q * W).col y, ?_, ?_, ?_, ?_⟩
  · intro hz
    exact hxy (congrFun hz x)
  · rw [← Matrix.col_mul_eq_mulVec_col, hkillA]
    rfl
  · rw [← Matrix.col_mul_eq_mulVec_col, hkillB]
    rfl
  · rw [← Matrix.col_mul_eq_mulVec_col, hkillC]
    rfl

/-- Three Hermitian operators on pairwise disjoint regions have a common unit vector attaining
their least eigenvalues, with its squared norm written as a star dot product. No common ground
vector and no normalization is assumed. AKLV, arXiv:1301.1162v1, Section 6.1, the
normalization preceding Theorem 6.1. -/
theorem exists_normalized_common_ground_of_disjoint
    {S T R : Finset V} (hST : Disjoint S T) (hSR : Disjoint S R) (hTR : Disjoint T R)
    {A B C : Matrix (Config X) (Config X) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
    (hsA : A ∈ supportedOperators X S) (hsB : B ∈ supportedOperators X T)
    (hsC : C ∈ supportedOperators X R) :
    ∃ v : Config X → ℂ, star v ⬝ᵥ v = 1 ∧
      (A - (minEigenvalue hA : ℂ) • 1) *ᵥ v = 0 ∧
      (B - (minEigenvalue hB : ℂ) • 1) *ᵥ v = 0 ∧
      (C - (minEigenvalue hC : ℂ) • 1) *ᵥ v = 0 := by
  obtain ⟨v, hv, hAv, hBv, hCv⟩ :=
    exists_common_ground_of_disjoint hST hSR hTR hA hB hC hsA hsB hsC
  let vE : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 v
  have hvE : vE ≠ 0 := by
    intro hzero
    apply hv
    simpa [vE] using congrArg WithLp.ofLp hzero
  let w := NormedSpace.normalize vE
  have hw : ‖w‖ = 1 := NormedSpace.norm_normalize hvE
  have hkill (M : Matrix (Config X) (Config X) ℂ) (hMv : M *ᵥ v = 0) :
      M *ᵥ WithLp.ofLp w = 0 := by
    change M *ᵥ WithLp.ofLp (‖vE‖⁻¹ • vE) = 0
    rw [WithLp.ofLp_smul, Matrix.mulVec_smul]
    change ‖vE‖⁻¹ • (M *ᵥ v) = 0
    rw [hMv, smul_zero]
  exact ⟨WithLp.ofLp w, EuclideanSpace.star_dotProduct_self_eq_one_of_norm_eq_one hw,
    hkill _ hAv, hkill _ hBv, hkill _ hCv⟩

end ManyBody
