import QICLean.Representation.ReplicaPrevector
import QICLean.Entropy.TypicalPureCompression
open Matrix PermutationRepresentation Module Filter TensorPower
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder
noncomputable section
namespace SchmidtBellPrototype
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (Ω : EuclideanSpace ℂ (A × B)) (E : Finset A)

local notation "hρA" => Matrix.PosSemidef.partialTraceRight
  (Matrix.posSemidef_vecMulVec_self_star Ω)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass (Matrix.PosSemidef.isHermitian hρA) E

theorem selected_norm (hz : 0 < z) :
    ‖WithLp.toLp 2 (fun x : B × Fin E.card =>
      Matrix.compressedTypicalPureState Ω E ((Finset.equivFin E).symm x.2, x.1))‖ = 1 := by
  exact ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodComm E B).trans ((Equiv.refl B).prodCongr (Finset.equivFin E)))).norm_map
      (Matrix.compressedTypicalPureState Ω E)).trans
    (Matrix.norm_compressedTypicalPureState Ω E hz)

theorem selected_marginal (hz : 0 < z) :
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


theorem commonSelected (hz : 0 < z) (hΩ : ‖Ω‖ = 1)
    (H : Matrix (A × B) (A × B) ℂ) (E₀ : ℝ)
    (hE : H *ᵥ Ω = (E₀ : ℂ) • (fun x => Ω x)) :
    let ψ : B × Fin E.card → ℂ := fun x =>
      Matrix.compressedTypicalPureState Ω E ((Finset.equivFin E).symm x.2, x.1)
    ‖WithLp.toLp 2 ψ‖ = 1 ∧
      Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)) =
        Matrix.diagonal (fun r : Fin E.card =>
          ((((Matrix.PosSemidef.isHermitian hρA).eigenvalues
            ((Finset.equivFin E).symm r)) / z : ℝ) : ℂ)) ∧
    ∃ l : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let v := replicaPrevector Ω E.card k (l k)
        let P := labelProj (copyPerm (Fin E.card) k) (l k)
        WithLp.toLp 2 v ≠ 0 ∧ ‖WithLp.toLp 2 v‖ ≤ 1 ∧
        (((k : ℝ)⁻¹ • replicaHamiltonian H k) ⊗ₖ
          (1 : Matrix ((Fin k → Fin E.card) × (Fin k → Fin E.card))
            ((Fin k → Fin E.card) × (Fin k → Fin E.card)) ℂ)) *ᵥ v = (E₀ : ℂ) • v ∧
        ((1 : Matrix (Fin k → (A × B)) (Fin k → (A × B)) ℂ) ⊗ₖ
          (P ⊗ₖ (1 : Matrix (Fin k → Fin E.card) (Fin k → Fin E.card) ℂ))) *ᵥ v = v ∧
        ((1 : Matrix (Fin k → (A × B)) (Fin k → (A × B)) ℂ) ⊗ₖ
          ((1 : Matrix (Fin k → Fin E.card) (Fin k → Fin E.card) ℂ) ⊗ₖ P)) *ᵥ v = v ∧
        (∀ σ : Equiv.Perm (Fin k),
          (permOp (copyPerm (A × B) k) σ ⊗ₖ
            (permOp (copyPerm (Fin E.card) k) σ ⊗ₖ permOp (copyPerm (Fin E.card) k) σ)) *ᵥ v = v)) ∧
      (∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → B) (Fin k → B) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (l k)) *ᵥ
              (fun x : (Fin k → B) × (Fin k → Fin E.card) => ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
      Asymptotics.IsLittleO atTop
        (fun k : ℕ => Real.log (l k).dim - (k : ℝ) *
          vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
            (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ => (k : ℝ)) := by
  intro ψ
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 := selected_norm Ω E hz
  refine ⟨hψ, selected_marginal Ω E hz, ?_⟩
  exact TensorPower.exists_label_sequence_replicaPrevector Ω hΩ ψ hψ H E₀ hE

end SchmidtBellPrototype
