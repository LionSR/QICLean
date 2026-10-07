import QICLean.Entropy.TypicalBellPinPowers

open scoped BigOperators Matrix Kronecker ComplexOrder

noncomputable section
namespace SchmidtBellPrototype

example {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (M : Matrix I I ℂ) (k : ℕ) :
    (Matrix.finKronecker (fun _ : Fin k => M)).submatrix
        (Equiv.piCongrRight (fun _ : Fin k => e)).symm
        (Equiv.piCongrRight (fun _ : Fin k => e)).symm =
      Matrix.finKronecker (fun _ : Fin k => M.submatrix e.symm e.symm) := by
  rfl

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (Ω : EuclideanSpace ℂ (A × B)) (E : Finset A)

local notation "hρA" => Matrix.PosSemidef.partialTraceRight
  (Matrix.posSemidef_vecMulVec_self_star Ω)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass (Matrix.PosSemidef.isHermitian hρA) E

example (hz : 0 < z) :
    ‖WithLp.toLp 2 (fun x : B × Fin E.card =>
      Matrix.compressedTypicalPureState Ω E ((Finset.equivFin E).symm x.2, x.1))‖ = 1 := by
  exact ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodComm E B).trans ((Equiv.refl B).prodCongr (Finset.equivFin E)))).norm_map
      (Matrix.compressedTypicalPureState Ω E)).trans
    (Matrix.norm_compressedTypicalPureState Ω E hz)

example (hz : 0 < z) :
    Matrix.partialTraceLeft (Matrix.vecMulVec
      (fun x : B × Fin E.card => Matrix.compressedTypicalPureState Ω E
        ((Finset.equivFin E).symm x.2, x.1))
      (star (fun x : B × Fin E.card => Matrix.compressedTypicalPureState Ω E
        ((Finset.equivFin E).symm x.2, x.1)))) =
      Matrix.diagonal (fun r : Fin E.card =>
        ((((Matrix.PosSemidef.isHermitian hρA).eigenvalues
          ((Finset.equivFin E).symm r)) / z : ℝ) : ℂ)) := by
  simpa only [Matrix.partialTraceLeft_apply, Matrix.partialTraceRight_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Matrix.submatrix_apply,
    Matrix.submatrix_diagonal _ _ (Finset.equivFin E).symm.injective] using
      congrArg (fun M : Matrix E E ℂ =>
        M.submatrix (Finset.equivFin E).symm (Finset.equivFin E).symm)
        (Matrix.partialTraceRight_compressedTypicalPureState Ω E hz)

end SchmidtBellPrototype
