/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.UnitaryGroup
import QICLean.Algebra.Cohomology.ProjectiveRepresentation
import QICLean.Algebra.Unitary.MatrixCoordinateInclusion
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import QICLean.Analysis.Cohomology.CircleCohomology
import QICLean.Analysis.FunctionalCalculus.ContinuousProjectionFrames
import QICLean.Analysis.FunctionalCalculus.MatrixPolar

/-!
# Direct sums with a common projective factor system

The virtual direct sum in Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.F.2, equation `eq:1d-sym:jointsym`, is projective when its two
summands have the same factor system. This is the algebraic step following
rephasing and preceding the interpolation of the bond state.

## Inclusions of the virtual symmetry summands

The coordinate inclusions of the two bond summands intertwine their
projective representations with the common-factor direct sum.
Source: arXiv:1010.3732, Section II.F.2, `eq:1d-sym:jointsym`.

Moved from TNLean, `TNLean/MPS/Symmetry/Projective/ProjectiveDirectSum.lean`,
`TNLean/MPS/Symmetry/Projective/ProjectiveRephasing.lean`,
`TNLean/MPS/Symmetry/Projective/UnitModulusProjectiveFactor.lean`,
`TNLean/MPS/Symmetry/Projective/ProjectiveHomConjugation.lean`,
`TNLean/MPS/Symmetry/ContinuousFamily/VaryingSupportPhaseInvariance.lean`,
`TNLean/MPS/Symmetry/OnSite/ProjectiveGaugeTransport.lean`,
`TNLean/MPS/Symmetry/SPTClassification/CohomologousFixedPointPath.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

section

open scoped Matrix

private def sumGL {D₀ D₁ : ℕ} (X : GL (Fin D₀) ℂ) (Y : GL (Fin D₁) ℂ) :
    GL (Fin D₀ ⊕ Fin D₁) ℂ where
  val := Matrix.fromBlocks X.val 0 0 Y.val
  inv := Matrix.fromBlocks X.inv 0 0 Y.inv
  val_inv := by
    simp [Matrix.fromBlocks_multiply]
  inv_val := by
    simp [Matrix.fromBlocks_multiply]

/-- The direct sum of two virtual representations with the same factor
system has that factor system. Schuch–Pérez-García–Cirac,
arXiv:1010.3732, Section II.F.2, equation `eq:1d-sym:jointsym`. -/
def ProjectiveRepresentation.directSum {G : Type} [Group G]
    {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) :
    ProjectiveRepresentation (D := D₀ + D₁) ω where
  X g := Units.map (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv).toMonoidHom
    (sumGL (ρ₀.X g) (ρ₁.X g))
  map_mul' g h := by
    change (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv) _ *
      (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv) _ =
      (ω (g, h) : ℂ) • (Matrix.reindexAlgEquiv ℂ ℂ finSumFinEquiv) _
    rw [← _root_.map_mul, ← map_smul]
    congr 1
    simp [sumGL, Matrix.fromBlocks_multiply, ρ₀.map_mul, ρ₁.map_mul,
      Matrix.fromBlocks_smul]

/-- The common-factor-system direct sum preserves unitarity. This supplies
the unitary virtual action in Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.F.2, equation `eq:1d-sym:jointsym`. -/
theorem ProjectiveRepresentation.directSum_mem_unitaryGroup
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G)
    (h₀ : (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) ∈
      Matrix.unitaryGroup _ ℂ := by
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (ρ₀.X g).val 0 0 (ρ₁.X g).val) ∈ _
  apply Matrix.reindex_mem_unitaryGroup
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp h₀,
    Matrix.mem_unitaryGroup_iff.mp h₁]

end

section

open scoped Matrix

/-- The first coordinate inclusion intertwines the projective direct sum
with its first summand. Source: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`. -/
theorem ProjectiveRepresentation.directSum_coordinateInclusion_left
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G) :
    ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) *
      Matrix.coordinateInclusion (Fin.castAddEmb D₁) =
    Matrix.coordinateInclusion (Fin.castAddEmb D₁) *
      (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) := by
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (ρ₀.X g).val 0 0 (ρ₁.X g).val) *
      Matrix.coordinateInclusion (Fin.castAddEmb D₁) =
    Matrix.coordinateInclusion (Fin.castAddEmb D₁) * (ρ₀.X g).val
  rw [Matrix.mul_coordinateInclusion]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [Matrix.coordinateInclusion, Matrix.mul_apply,
    Matrix.reindex_apply, Matrix.fromBlocks,
    ← finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right,
    finSumFinEquiv.injective.eq_iff]

/-- The second coordinate inclusion intertwines the projective direct sum
with its second summand. Source: arXiv:1010.3732, Section II.F.2,
`eq:1d-sym:jointsym`. -/
theorem ProjectiveRepresentation.directSum_coordinateInclusion_right
    {G : Type} [Group G] {D₀ D₁ : ℕ} {ω : ScalarCocycle G}
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω) (g : G) :
    ((ρ₀.directSum ρ₁).X g : Matrix (Fin (D₀ + D₁)) (Fin (D₀ + D₁)) ℂ) *
      Matrix.coordinateInclusion (Fin.natAddEmb D₀) =
    Matrix.coordinateInclusion (Fin.natAddEmb D₀) *
      (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) := by
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (ρ₀.X g).val 0 0 (ρ₁.X g).val) *
      Matrix.coordinateInclusion (Fin.natAddEmb D₀) =
    Matrix.coordinateInclusion (Fin.natAddEmb D₀) * (ρ₁.X g).val
  rw [Matrix.mul_coordinateInclusion]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [Matrix.coordinateInclusion, Matrix.mul_apply,
    Matrix.reindex_apply, Matrix.fromBlocks,
    ← finSumFinEquiv_apply_right, -finSumFinEquiv_apply_left,
    finSumFinEquiv.injective.eq_iff]

end

section

open scoped Matrix ScalarCohomology

variable {G : Type} [Group G] {D : ℕ}

/-- Multiplying each virtual matrix by a scalar unit changes its factor system
by the corresponding coboundary. Schuch–Pérez-García–Cirac, arXiv:1010.3732,
Section II.F.2, lines 886–929. -/
def ProjectiveRepresentation.rephase {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω) (φ : G → Units ℂ) :
    ProjectiveRepresentation (D := D)
      (fun p => φ p.1 * φ p.2 * (φ (p.1 * p.2))⁻¹ * ω p) where
  X g := Matrix.GeneralLinearGroup.scalar (Fin D) (φ g) * ρ.X g
  map_mul' := by
    intro g h
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul, Units.val_mul,
      Units.val_inv_eq_inv_val]
    calc
      ((φ g : ℂ) • (ρ.X g : Matrix (Fin D) (Fin D) ℂ)) *
          ((φ h : ℂ) • (ρ.X h : Matrix (Fin D) (Fin D) ℂ))
          = ((φ g : ℂ) * (φ h : ℂ)) •
              ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
                (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) := by
              simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
      _ = ((φ g : ℂ) * (φ h : ℂ) * (φ (g * h) : ℂ)⁻¹ * (ω (g, h) : ℂ)) •
          ((φ (g * h) : ℂ) •
            (ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ)) := by
          rw [ρ.map_mul]
          simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]

end

section

open scoped Matrix Matrix.Norms.L2Operator ScalarCohomology

namespace ProjectiveRepresentation

variable {G : Type} [Group G] {D : ℕ} [NeZero D]

variable {ω : ScalarCocycle G}

/-- The factor of a unitary projective representation has unit modulus.
Source: arXiv:1010.3732, Section II.F.2, lines 886--921. -/
theorem norm_factor_eq_one_of_unitary
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g h : G) : ‖(ω (g, h) : ℂ)‖ = 1 := by
  have hnorm := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => ‖M‖) (ρ.map_mul g h)
  rw [CStarRing.norm_mem_unitary_mul _ (hρ g), CStarRing.norm_of_mem_unitary (hρ h),
    norm_smul, CStarRing.norm_of_mem_unitary (hρ (g * h)), mul_one] at hnorm
  exact hnorm.symm

/-- The circle-phase inclusion preserves the actual factor system of a
unitary projective representation.
Source: arXiv:1010.3732, Section II.F.2, lines 886--921. -/
theorem circlePhaseInclusion_eq_of_unitary
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    ω.circlePhaseInclusion = ω := by
  funext ⟨g, h⟩
  apply Units.ext
  change (ω (g, h) : ℂ) / ‖(ω (g, h) : ℂ)‖ = (ω (g, h) : ℂ)
  simp only [ρ.norm_factor_eq_one_of_unitary hρ g h, Complex.ofReal_one, div_one]

end ProjectiveRepresentation

end

section

open scoped Matrix Kronecker

namespace ProjectiveRepresentation

variable {G : Type} [Group G] {D₀ D₁ : ℕ}

variable {ω₀ ω₁ : ScalarCocycle G}

/-- The factor of a unitary projective representation cancels with its
complex conjugate. The bond dimension must be nonzero. -/
theorem factor_mul_star_eq_one_of_unitary [NeZero D₀]
    (ρ : ProjectiveRepresentation (D := D₀) ω₀)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g h : G) : (ω₀ (g, h) : ℂ) * star (ω₀ (g, h) : ℂ) = 1 := by
  change (ω₀ (g, h) : ℂ) * (starRingEnd ℂ) (ω₀ (g, h) : ℂ) = 1
  rw [Complex.mul_conj', ρ.norm_factor_eq_one_of_unitary hρ g h,
    Complex.ofReal_one, one_pow]

/-- The projective matrix acting on vectorized intertwiners. -/
def homMatrix
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁) (g : G) :
    Matrix (Fin D₀ × Fin D₁) (Fin D₀ × Fin D₁) ℂ :=
  (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ).map star ⊗ₖ
    (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ)

/-- The projective matrix on the intertwiner space is unitary. -/
theorem homMatrix_mem_unitaryGroup
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g : G) : homMatrix ρ₀ ρ₁ g ∈ Matrix.unitaryGroup _ ℂ :=
  Matrix.kronecker_mem_unitary (Matrix.map_star_mem_unitaryGroup_iff.mpr (h₀ g)) (h₁ g)

/-- The factor on the intertwiner space is the complex conjugate of the
first factor multiplied by the second. -/
theorem homMatrix_mul
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁) (g h : G) :
    homMatrix ρ₀ ρ₁ g * homMatrix ρ₀ ρ₁ h =
      (star (ω₀ (g, h) : ℂ) * (ω₁ (g, h) : ℂ)) • homMatrix ρ₀ ρ₁ (g * h) := by
  simp only [homMatrix]
  rw [← Matrix.mul_kronecker_mul]
  have hMap :
      (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ).map star *
        (ρ₀.X h : Matrix (Fin D₀) (Fin D₀) ℂ).map star =
      (((ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) *
        (ρ₀.X h : Matrix (Fin D₀) (Fin D₀) ℂ)).map star) := by
    exact (Matrix.map_mul (f := starRingEnd ℂ)).symm
  rw [hMap, ρ₀.map_mul, ρ₁.map_mul,
    Matrix.map_smulₛₗ star star _ (fun _ => star_smul _ _),
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]

private theorem homFactor_mul_star_eq_one [NeZero D₀] [NeZero D₁]
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g h : G) :
    (star (ω₀ (g, h) : ℂ) * (ω₁ (g, h) : ℂ)) *
      star (star (ω₀ (g, h) : ℂ) * (ω₁ (g, h) : ℂ)) = 1 := by
  simp only [star_mul, star_star]
  calc
    (star (ω₀ (g, h) : ℂ) * (ω₁ (g, h) : ℂ)) *
        (star (ω₁ (g, h) : ℂ) * (ω₀ (g, h) : ℂ)) =
        ((ω₀ (g, h) : ℂ) * star (ω₀ (g, h) : ℂ)) *
          ((ω₁ (g, h) : ℂ) * star (ω₁ (g, h) : ℂ)) := by ac_rfl
    _ = 1 := by
      rw [ρ₀.factor_mul_star_eq_one_of_unitary h₀,
        ρ₁.factor_mul_star_eq_one_of_unitary h₁, mul_one]

/-- Although the matrices on the intertwiner space are projective, their
conjugations compose exactly. -/
theorem homMatrix_conjugation_mul [NeZero D₀] [NeZero D₁]
    (ρ₀ : ProjectiveRepresentation (D := D₀) ω₀)
    (ρ₁ : ProjectiveRepresentation (D := D₁) ω₁)
    (h₀ : ∀ g, (ρ₀.X g : Matrix (Fin D₀) (Fin D₀) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (h₁ : ∀ g, (ρ₁.X g : Matrix (Fin D₁) (Fin D₁) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g h : G) (X : Matrix (Fin D₀ × Fin D₁) (Fin D₀ × Fin D₁) ℂ) :
    homMatrix ρ₀ ρ₁ g * (homMatrix ρ₀ ρ₁ h * X * (homMatrix ρ₀ ρ₁ h)ᴴ) *
        (homMatrix ρ₀ ρ₁ g)ᴴ =
      homMatrix ρ₀ ρ₁ (g * h) * X * (homMatrix ρ₀ ρ₁ (g * h))ᴴ := by
  calc
    homMatrix ρ₀ ρ₁ g * (homMatrix ρ₀ ρ₁ h * X * (homMatrix ρ₀ ρ₁ h)ᴴ) *
        (homMatrix ρ₀ ρ₁ g)ᴴ =
        (homMatrix ρ₀ ρ₁ g * homMatrix ρ₀ ρ₁ h) * X *
          (homMatrix ρ₀ ρ₁ g * homMatrix ρ₀ ρ₁ h)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = homMatrix ρ₀ ρ₁ (g * h) * X * (homMatrix ρ₀ ρ₁ (g * h))ᴴ := by
      rw [homMatrix_mul, Matrix.conjTranspose_smul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm, homFactor_mul_star_eq_one ρ₀ ρ₁ h₀ h₁ g h, one_smul]

end ProjectiveRepresentation

end

section

open scoped Matrix

section VaryingSupportPhaseInvariance

namespace Matrix

/-- Isometric compression is multiplicative when the first matrix
preserves the compressed subspace. Source context: arXiv:1010.3732,
Appendix C, lines 2712–2717. -/
theorem isometry_compression_mul_of_commute {D r : ℕ}
    (J : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry)
    (X Y : Matrix (Fin D) (Fin D) ℂ) (hX : Commute X (J * Jᴴ)) :
    (Jᴴ * X * J) * (Jᴴ * Y * J) = Jᴴ * (X * Y) * J := by
  calc
    (Jᴴ * X * J) * (Jᴴ * Y * J) = Jᴴ * (X * (J * Jᴴ)) * Y * J := by
      simp only [Matrix.mul_assoc]
    _ = Jᴴ * ((J * Jᴴ) * X) * Y * J := by rw [hX.eq]
    _ = (Jᴴ * J) * Jᴴ * (X * Y) * J := by simp only [Matrix.mul_assoc]
    _ = Jᴴ * (X * Y) * J := by rw [show Jᴴ * J = 1 from hJ, Matrix.one_mul]

/-- A unitary matrix remains unitary on an invariant isometrically
included subspace. Source context: arXiv:1010.3732, Appendix C,
lines 2712–2717. -/
theorem isometry_compression_mem_unitaryGroup {D r : ℕ}
    (J : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X ∈ Matrix.unitaryGroup _ ℂ)
    (hComm : Commute X (J * Jᴴ)) :
    Jᴴ * X * J ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  have hXX : X * Xᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hX
  have heq : Jᴴ * (X * Xᴴ) * J = 1 := by
    simpa only [hXX, Matrix.mul_one] using (show Jᴴ * J = 1 from hJ)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc] using (isometry_compression_mul_of_commute J hJ X Xᴴ hComm).trans heq

end Matrix

/-- Restriction of a unitary projective representation to a nonzero
invariant single-bond subspace retains its factor system and unitarity.
The isometric inclusion is supplied here, not derived from a physical
path. Source: arXiv:1010.3732, Appendix C, lines 2712–2717. -/
theorem ProjectiveRepresentation.exists_unitary_compression
    {G : Type} [Group G] {D r : ℕ} [NeZero r] {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (J : Matrix (Fin D) (Fin r) ℂ) (hJ : J.IsIsometry)
    (hUnitary : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hComm : ∀ g, Commute (ρ.X g : Matrix (Fin D) (Fin D) ℂ) (J * Jᴴ)) :
    ∃ σ : ProjectiveRepresentation (D := r) ω,
      (∀ g, (σ.X g : Matrix (Fin r) (Fin r) ℂ) =
        Jᴴ * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * J) ∧
      ∀ g, (σ.X g : Matrix (Fin r) (Fin r) ℂ) ∈ Matrix.unitaryGroup _ ℂ := by
  have hW (g : G) : Jᴴ * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * J ∈
      Matrix.unitaryGroup _ ℂ :=
    Matrix.isometry_compression_mem_unitaryGroup J hJ _ (hUnitary g) (hComm g)
  let X (g : G) : GL (Fin r) ℂ := {
    val := Jᴴ * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * J
    inv := star (Jᴴ * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * J)
    val_inv := (hW g).2
    inv_val := (hW g).1
  }
  let σ : ProjectiveRepresentation (D := r) ω := {
    X := X
    map_mul' := by
      intro g h
      change (Jᴴ * (ρ.X g : Matrix (Fin D) (Fin D) ℂ) * J) *
        (Jᴴ * (ρ.X h : Matrix (Fin D) (Fin D) ℂ) * J) =
        (ω (g, h) : ℂ) • (Jᴴ * (ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ) * J)
      rw [Matrix.isometry_compression_mul_of_commute J hJ _ _ (hComm g), ρ.map_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul]
  }
  exact ⟨σ, fun _ => rfl, hW⟩

end VaryingSupportPhaseInvariance

section ContinuousInvariantCompression

/-- Continuous local compression to a nonzero invariant projection range
preserves the factor system exactly. Source context: arXiv:1010.3732,
Appendix C, lines 2653–2717. -/
theorem ProjectiveRepresentation.exists_local_continuous_unitary_compression
    {T : Type*} {G : Type} [TopologicalSpace T] [Group G] {D r : ℕ} [NeZero r]
    (ω : T → ScalarCocycle G) (ρ : ∀ t, ProjectiveRepresentation (D := D) (ω t))
    (hρ : ∀ g, Continuous fun t => ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ))
    (hUnitary : ∀ t g, ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (P : T → Matrix (Fin D) (Fin D) ℂ) (hP : Continuous P)
    (hHerm : ∀ t, (P t).IsHermitian) (hid : ∀ t, P t * P t = P t)
    (hrank : ∀ t, (P t).rank = r)
    (hComm : ∀ t g, Commute ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) (P t))
    (t₀ : T) (J₀ : Matrix (Fin D) (Fin r) ℂ) (hJ₀ : J₀.IsIsometry)
    (hbase : P t₀ = J₀ * J₀ᴴ) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ∃ σ : ∀ t : S, ProjectiveRepresentation (D := r) (ω t),
        (∀ g, Continuous fun t : S => ((σ t).X g : Matrix (Fin r) (Fin r) ℂ)) ∧
        (∀ t g, ((σ t).X g : Matrix (Fin r) (Fin r) ℂ) ∈ Matrix.unitaryGroup _ ℂ) ∧
        ∀ t g, ((σ t).X g : Matrix (Fin r) (Fin r) ℂ) =
          (Matrix.polarIso (P t * J₀))ᴴ *
            ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) * Matrix.polarIso (P t * J₀) := by
  classical
  obtain ⟨S, hS, ht₀, hcont, hFrame⟩ :=
    Matrix.exists_local_continuous_projection_frame P hP hHerm hid
      (fun t => by simpa using hrank t) t₀ J₀ hJ₀ hbase
  have hcomp (t : S) : ∃ σ : ProjectiveRepresentation (D := r) (ω t),
      (∀ g, (σ.X g : Matrix (Fin r) (Fin r) ℂ) =
        (Matrix.polarIso (P t * J₀))ᴴ *
          ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) * Matrix.polarIso (P t * J₀)) ∧
      ∀ g, (σ.X g : Matrix (Fin r) (Fin r) ℂ) ∈ Matrix.unitaryGroup _ ℂ := by
    apply (ρ t).exists_unitary_compression _ (hFrame t t.property).1 (hUnitary t)
    intro g
    rw [(hFrame t t.property).2]
    exact hComm t g
  choose σ hσ hσUnitary using hcomp
  refine ⟨S, hS, ht₀, σ, ?_, hσUnitary, hσ⟩
  intro g
  have hJ : Continuous fun t : S => Matrix.polarIso (P t * J₀) :=
    continuousOn_iff_continuous_domRestrict.mp hcont
  have h := (hJ.matrix_conjTranspose.matrix_mul
    ((hρ g).comp continuous_subtype_val)).matrix_mul hJ
  exact h.congr (fun t => (hσ t g).symm)

/-- A continuous projective matrix family of positive fixed dimension has
continuous factors. Hence the unchanged factors of an invariant local
compression are continuous as well. Source context: arXiv:1010.3732,
Section II.F.2, lines 1000–1029, and Appendix C, lines 2653–2717. -/
theorem ProjectiveRepresentation.continuous_factor_family
    {T : Type*} {G : Type} [TopologicalSpace T] [Group G] {D : ℕ} (hD : 0 < D)
    (ω : T → ScalarCocycle G) (ρ : ∀ t, ProjectiveRepresentation (D := D) (ω t))
    (hρ : ∀ g, Continuous fun t => ((ρ t).X g : Matrix (Fin D) (Fin D) ℂ))
    (g h : G) : Continuous fun t => (ω t (g, h) : ℂ) := by
  let i : Fin D := ⟨0, hD⟩
  have hformula (t : T) : (ω t (g, h) : ℂ) =
      ((((ρ t).X g : Matrix (Fin D) (Fin D) ℂ) * (ρ t).X h *
        ((ρ t).X (g * h) : Matrix (Fin D) (Fin D) ℂ).adjugate) i i) /
          ((ρ t).X (g * h) : Matrix (Fin D) (Fin D) ℂ).det := by
    rw [(ρ t).map_mul, Matrix.smul_mul, Matrix.mul_adjugate]
    simp [Matrix.smul_apply, ((ρ t).X (g * h)).det_ne_zero]
  have hc := ((((hρ g).matrix_mul (hρ h)).matrix_mul
    (hρ (g * h)).matrix_adjugate).matrix_elem i i).div
      (hρ (g * h)).matrix_det (fun t => ((ρ t).X (g * h)).det_ne_zero)
  exact hc.congr (fun t => (hformula t).symm)

end ContinuousInvariantCompression

end

section

open scoped Matrix ScalarCohomology

namespace ProjectiveRepresentation

variable {G : Type} [Group G] {D : ℕ} {ω : ScalarCocycle G}

/-- Conjugating the virtual matrices retains the factor system. Source:
arXiv:1010.3732, Section II.C, virtual gauge preparation. -/
def conjugate (ρ : ProjectiveRepresentation (D := D) ω) (Y : GL (Fin D) ℂ) :
    ProjectiveRepresentation (D := D) ω where
  X g := Y * ρ.X g * Y⁻¹
  map_mul' := by
    intro g h
    have hY : ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
        (Y : Matrix (Fin D) (Fin D) ℂ) = 1 := by simp
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    calc
      _ = (Y : Matrix (Fin D) (Fin D) ℂ) *
          ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
          ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
            simp only [Matrix.mul_assoc, ← Matrix.mul_assoc
              ((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ), hY, Matrix.one_mul]
      _ = _ := by rw [ρ.map_mul, Matrix.mul_smul, Matrix.smul_mul]

end ProjectiveRepresentation

end

section

open scoped Matrix Matrix.Norms.L2Operator ScalarCohomology

/-- A factor system of a unitary projective representation has unit modulus.
Source: arXiv:1010.3732, Section II.F.2, lines 886--896, the unitary virtual
representations in the fixed-point symmetry. -/
theorem ProjectiveRepresentation.norm_factorSystem
    {G : Type} [Group G] {D : ℕ} [NeZero D] {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (g h : G) : ‖(ω (g, h) : ℂ)‖ = 1 := by
  have hp := CStarRing.norm_of_mem_unitary
    ((Matrix.unitaryGroup (Fin D) ℂ).mul_mem (hρ g) (hρ h))
  rwa [ρ.map_mul, norm_smul, CStarRing.norm_of_mem_unitary (hρ (g * h)),
    mul_one] at hp

/-- The factor system of a unitary virtual action equals its pointwise unit
phase. Source: arXiv:1010.3732, Section II.F.2, lines 886--896. -/
theorem ProjectiveRepresentation.circlePhaseInclusion_eq
    {G : Type} [Group G] {D : ℕ} [NeZero D] {ω : ScalarCocycle G}
    (ρ : ProjectiveRepresentation (D := D) ω)
    (hρ : ∀ g, (ρ.X g : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ) :
    ω.circlePhaseInclusion = ω := by
  funext ⟨g, h⟩
  apply Units.ext
  change (ω (g, h) : ℂ) / ‖(ω (g, h) : ℂ)‖ = (ω (g, h) : ℂ)
  simp only [ρ.norm_factorSystem hρ, Complex.ofReal_one, div_one]

end
