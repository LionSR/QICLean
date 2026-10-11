/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.TypicalPureCompression

/-!
# Entropy of the selected Schmidt auxiliary marginal

The selected Schmidt vector is the same vector used to choose the common
auxiliary label sequence. Relabeling its selected coordinate space by
`Fin E.card` does not change the entropy of its normalized selected spectrum.
No label sequence or new state is chosen in this identity.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 240–270, `comparator:high-label`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open scoped Matrix ComplexOrder

namespace Matrix

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
variable (Ω : EuclideanSpace ℂ (A × B)) (E : Finset A)

local notation "hρA" => Matrix.PosSemidef.partialTraceRight
  (Matrix.posSemidef_vecMulVec_self_star Ω)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρA) E

/-- The actual auxiliary marginal of the selected Schmidt vector has the
entropy of the normalized spectral restriction of the original left marginal.
Positive selected mass is the only normalization hypothesis.
Source: `07-comparators.tex`, lines 240–270, `comparator:high-label`. -/
theorem entropy_compressedTypicalPureState_equivFin_swap (hz : 0 < z) :
    let ψ : B × Fin E.card → ℂ := fun x =>
      Matrix.compressedTypicalPureState Ω E ((Finset.equivFin E).symm x.2, x.1)
    vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
      (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian =
        vonNeumannEntropy ((hρA).isHermitian.normalizedSpectralRestriction E)
          ((hρA).normalizedSpectralRestriction_posSemidef E hz).isHermitian := by
  intro ψ
  have hdiag : partialTraceLeft (vecMulVec ψ (star ψ)) =
      diagonal (fun r : Fin E.card =>
        ((((hρA).isHermitian.eigenvalues ((Finset.equivFin E).symm r)) / z : ℝ) : ℂ)) :=
    Matrix.ext fun r s => by
      simpa only [ψ, partialTraceLeft_apply, partialTraceRight_apply,
        vecMulVec_apply, Pi.star_apply, diagonal_apply,
        (Finset.equivFin E).symm.injective.eq_iff] using
          congrArg (fun M : Matrix E E ℂ =>
            M ((Finset.equivFin E).symm r) ((Finset.equivFin E).symm s))
            (partialTraceRight_compressedTypicalPureState Ω E hz)
  done

end Matrix
