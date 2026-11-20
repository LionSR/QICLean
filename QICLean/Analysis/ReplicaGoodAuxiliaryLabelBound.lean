/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.GoodAuxiliaryLabelCompression
import QICLean.Analysis.ReplicaExcitationSymmetry

/-!
# The good auxiliary label on an actual excitation component

For a vector with a specified whole-copy auxiliary label, applying the
literal physical excitation operator preserves that label. The derived
whole-label compression bound therefore gives a lower bound for the actual
good-copy auxiliary observable on the resulting component, while retaining
all additional auxiliary registers. The coordinate split is constructed
from the complement and the excited subset; it is not a supplied hypothesis.

This is the component support step in *A two-dimensional area law from a
global spectral gap*, `07-comparators.tex`, lines 441–456 and 481–493,
equation `comparator:good-auxiliary`. The scalar correction uses the actual
number of excited copies. The numerical whole-label threshold and the
subsequent metric comparison are separate assertions. No physical excitation
operator is commuted through a band metric.

The identity is algebraic for any one-copy vector. For a unit ground vector,
the existing sector theorem identifies the literal excitation operator
with the orthogonal excitation projection. No normalization, independence
or iid assumption is needed for the present bound. Empty registers, zero
copies and zero components are included, with the total real logarithm.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix PermutationRepresentation TensorPower
open scoped MatrixOrder ComplexOrder Kronecker

namespace Matrix

/-- Enumerate the actual good coordinates first and bad coordinates second.
Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 441–456 and 481–493, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
noncomputable def replicaGoodBadSplit {k : ℕ} (B : Finset (Fin k)) :
    Fin (Bᶜ).card ⊕ Fin B.card ≃ Fin k :=
  ((Equiv.sumCongr (Bᶜ).equivFin.symm B.equivFin.symm).trans
    (Equiv.sumComm ↥(Bᶜ) ↥B)).trans
      ((Equiv.sumCongr (Equiv.refl ↥B)
        (Equiv.subtypeEquivRight (fun _ : Fin k => Finset.mem_compl))).trans
          (Equiv.sumCompl (fun i : Fin k => i ∈ B)))

variable {A C D : Type*} [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:good-auxiliary, lines 481–493.
-/

/-- The literal physical excitation component preserves a given whole-copy
auxiliary label and therefore satisfies the derived lower bound for the
actual good-copy auxiliary observable. The additional auxiliary register
`D` is retained throughout. The good/bad split is constructed from `Bᶜ`
and `B`, rather than supplied by a compatibility assumption.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 441–456 and 481–493, equation `comparator:good-auxiliary`. The sole
support hypothesis concerns the original vector, not its component. -/
theorem replicaExcitationComponent_goodAuxiliary_labelEntropy_lower
    (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k))
    (l : IrrepLabel (Equiv.Perm (Fin k)))
    (v : (Fin k → A) × ((Fin k → C) × D) → ℂ)
    (hv : ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (labelProj (copyPerm C k) l ⊗ₖ (1 : Matrix D D ℂ))) *ᵥ v = v) :
    let e := replicaGoodBadSplit B
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → C) × D) ((Fin k → C) × D) ℂ)) *ᵥ v
    (Real.log l.dim - (B.card : ℝ) * Real.log (Fintype.card C) - Real.log (k.choose B.card)) *
      (star w ⬝ᵥ w).re ≤
      (star w ⬝ᵥ (((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
        (labelEntropy ((copyPerm C k).comp (groupHom₁ e)) ⊗ₖ
          (1 : Matrix D D ℂ))) *ᵥ w)).re := by
  classical
  dsimp only
  let w := (replicaExcitationProjection Ω k B ⊗ₖ
    (1 : Matrix ((Fin k → C) × D) ((Fin k → C) × D) ℂ)) *ᵥ v
  have hw : ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (labelProj (copyPerm C k) l ⊗ₖ (1 : Matrix D D ℂ))) *ᵥ w = w := by
    simpa only [map_one] using
      replicaExcitationProjection_kronecker_mulVec_preserves_fixed Ω k B 1 (by simp)
        (labelProj (copyPerm C k) l ⊗ₖ (1 : Matrix D D ℂ)) v
        (by simpa only [map_one] using hv)
  have hc := (copyPerm_groupedGood_labelEntropy_compression (C := C)
    (replicaGoodBadSplit B) l).2
  let L : Matrix (Fin k → C) (Fin k → C) ℂ →ₗ[ℂ]
      Matrix ((Fin k → A) × ((Fin k → C) × D)) ((Fin k → A) × ((Fin k → C) × D)) ℂ :=
    ((Matrix.kroneckerBilinear (R := ℂ)) (1 : Matrix (Fin k → A) (Fin k → A) ℂ)).comp
      ((Matrix.kroneckerBilinear (R := ℂ)).flip (1 : Matrix D D ℂ))
  have h : (L (labelProj (copyPerm C k) l *
      labelEntropy ((copyPerm C k).comp (groupHom₁ (replicaGoodBadSplit B))) *
      labelProj (copyPerm C k) l -
      ((Real.log l.dim - (B.card : ℝ) * Real.log (Fintype.card C) -
        Real.log (k.choose B.card) : ℝ) : ℂ) • labelProj (copyPerm C k) l)).PosSemidef :=
    (PosSemidef.one (n := Fin k → A)).kronecker
      ((Matrix.le_iff.mp hc).kronecker (PosSemidef.one (n := D)))
  rw [map_sub, map_smul] at h
  have hLmul (M N : Matrix (Fin k → C) (Fin k → C) ℂ) :
      L (M * N) = L M * L N := by
    change (1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
        ((M * N) ⊗ₖ (1 : Matrix D D ℂ)) =
      ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ (M ⊗ₖ (1 : Matrix D D ℂ))) *
      ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ (N ⊗ₖ (1 : Matrix D D ℂ)))
    simp only [← mul_kronecker_mul, mul_one]
  have hLP : (L (labelProj (copyPerm C k) l))ᴴ = L (labelProj (copyPerm C k) l) := by
    change ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
        (labelProj (copyPerm C k) l ⊗ₖ (1 : Matrix D D ℂ)))ᴴ =
      (1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
        (labelProj (copyPerm C k) l ⊗ₖ (1 : Matrix D D ℂ))
    simp only [conjTranspose_kronecker, conjTranspose_one, (isHermitian_labelProj _ l).eq]
  change L (labelProj (copyPerm C k) l) *ᵥ w = w at hw
  have hwleft : star w ᵥ* L (labelProj (copyPerm C k) l) = star w := by
    rw [← hLP, ← star_mulVec, hw]
  have hq := (RCLike.nonneg_iff.mp (h.dotProduct_mulVec_nonneg w)).1
  simp only [hLmul, sub_mulVec, smul_mulVec, ← mulVec_mulVec, hw,
    dotProduct_sub, dotProduct_smul] at hq
  rw [dotProduct_mulVec, hwleft] at hq
  simp only [RCLike.re_to_complex, smul_eq_mul, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hq
  exact sub_nonneg.mp hq

end Matrix
