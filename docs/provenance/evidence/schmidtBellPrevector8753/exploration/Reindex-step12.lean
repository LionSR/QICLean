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
  ext r s
  simpa only [Matrix.partialTraceLeft_apply, Matrix.partialTraceRight_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Matrix.diagonal_apply,
    (Finset.equivFin E).symm.injective.eq_iff] using
      congrArg (fun M : Matrix E E ℂ =>
        M ((Finset.equivFin E).symm r) ((Finset.equivFin E).symm s))
        (Matrix.partialTraceRight_compressedTypicalPureState Ω E hz)

example (c r : Fin E.card) :
    Matrix.omegaVec (Fintype.card E)
      ((Fintype.equivFin E) ((Finset.equivFin E).symm c),
       (Fintype.equivFin E) ((Finset.equivFin E).symm r)) =
      Matrix.omegaVec E.card (c, r) := by
  simp [Matrix.omegaVec]

example (a : A) (b : B) (c r : Fin E.card) :
    Matrix.bellPinPrevector Ω E
      ((a, (Finset.equivFin E).symm c), ((Finset.equivFin E).symm r, b)) =
      Ω (a, b) * Matrix.omegaVec E.card (c, r) := by
  change Ω (a, b) * Matrix.omegaVec (Fintype.card E)
    ((Fintype.equivFin E) ((Finset.equivFin E).symm c),
      (Fintype.equivFin E) ((Finset.equivFin E).symm r)) = _
  simp [Matrix.omegaVec]

example {X Y R S : Type*} [Fintype X] [Fintype Y] [Fintype R] [Fintype S]
    [DecidableEq R] [DecidableEq S]
    (eX : X ≃ Y) (eR : R ≃ S) (P : Matrix X X ℂ) (k : ℕ) :
    ((Matrix.finKronecker (fun _ : Fin k => P)) ⊗ₖ
      (1 : Matrix ((Fin k → R) × (Fin k → B)) ((Fin k → R) × (Fin k → B)) ℂ)).submatrix
        ((Equiv.piCongrRight (fun _ : Fin k => eX)).prodCongr
          ((Equiv.piCongrRight (fun _ : Fin k => eR)).prodCongr
            (Equiv.refl (Fin k → B)))).symm
        ((Equiv.piCongrRight (fun _ : Fin k => eX)).prodCongr
          ((Equiv.piCongrRight (fun _ : Fin k => eR)).prodCongr
            (Equiv.refl (Fin k → B)))).symm =
      Matrix.finKronecker (fun _ : Fin k => P.submatrix eX.symm eX.symm) ⊗ₖ
        (1 : Matrix ((Fin k → S) × (Fin k → B)) ((Fin k → S) × (Fin k → B)) ℂ) := by
  change ((Matrix.finKronecker (fun _ : Fin k => P)) ⊗ₖ
    (1 : Matrix ((Fin k → R) × (Fin k → B)) ((Fin k → R) × (Fin k → B)) ℂ)).submatrix
      (Prod.map (Equiv.piCongrRight (fun _ : Fin k => eX)).symm
        ((Equiv.piCongrRight (fun _ : Fin k => eR)).prodCongr
          (Equiv.refl (Fin k → B))).symm)
      (Prod.map (Equiv.piCongrRight (fun _ : Fin k => eX)).symm
        ((Equiv.piCongrRight (fun _ : Fin k => eR)).prodCongr
          (Equiv.refl (Fin k → B))).symm) = _
  done

end SchmidtBellPrototype
