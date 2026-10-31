/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceCoordinates
import QICLean.Analysis.ViableSubspaceSchmidtRank
import QICLean.Analysis.VonNeumannEntropySpectralTail
import QICLean.Channel.FiniteProduct
import QICLean.Channel.MaximalOverlap
import QICLean.Entropy.RegionRank

/-!
# Regional entropy from viable subspaces

For one fixed unit vector, viable-subspace bounds control tails of a single
ordered eigenvalue distribution. The entropy of that distribution is the
von Neumann entropy of the vector's reduced state. The actual finite-product
splitting is identified with the canonical tensor-product coordinates, so
no compatibility between independently chosen coordinate maps is assumed.
The marginal identity itself requires no normalization or nonempty region.

These statements support ALVV, arXiv:1602.08828v2, the proof of Theorem
`thm:al-dg`, lines 1080–1099. The spectral interpretation of reduced states
is Wolf, Chapter 3, Lemma 3.1, and Chapter 8, Section 8.2.
-/

open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder Matrix

namespace Submodule

/-- The same unit target vector and the same cut isometry determine one
spectral probability distribution before all choices of accuracy, viable
subspace and rank. Its eigenvalue tails inherit every viable-subspace
bound. Auxiliary to ALVV, arXiv:1602.08828v2, proof of `thm:al-dg`,
lines 1080–1094, and Wolf, Chapter 3, Lemma 3.1; the entropy identity is
Wolf, Chapter 8, Section 8.2, Eq. (8.15). -/
theorem unit_cut_spectral_probability
    {E σ β : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Fintype σ] [Fintype β] [DecidableEq σ] [DecidableEq β]
    (Tm : E ≃ₗᵢ[ℂ] (EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β))
    (G : Submodule ℂ E) (ψ : E) (hψG : ψ ∈ G) (hψ : ‖ψ‖ = 1) :
    let w := (euclideanTensorEquiv σ β).symm (Tm ψ)
    let C := Matrix.schmidtCoeffMatrix (WithLp.ofLp w)
    let hρ := Matrix.posSemidef_self_mul_conjTranspose C
    let p := hρ.isHermitian.eigenvalues₀
    (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1) ∧
      vonNeumannEntropy (C * Cᴴ) hρ.isHermitian = Entropy.probabilityEntropy p ∧
      ∀ (δ : ℝ) (S : Submodule ℂ (EuclideanSpace ℂ σ)) (R : ℕ),
        δ < 1 → Module.finrank ℂ S ≤ R →
        IsViable δ S (G.map (Tm.toLinearEquiv :
          E →ₗ[ℂ] EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β)) →
        (∑ a ∈ Finset.univ.filter
          (fun a : Fin (Fintype.card σ) ↦ R ≤ a.val), p a) ≤ δ := by
  intro w C hρ p
  have hw : ‖w‖ = 1 := by
    simpa only [w, LinearIsometryEquiv.norm_map] using hψ
  have htrace : (C * Cᴴ).trace = 1 :=
    Matrix.trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one w hw
  have hdesc (a : Fin (Fintype.card σ)) :
      hρ.isHermitian.descEigenvalue a.val = p a := by
    simp only [Matrix.IsHermitian.descEigenvalue, dite_eq_left a.isLt, p]
  have hp (a) : 0 ≤ p a := by
    rw [← hdesc a]
    exact hρ.descEigenvalue_nonneg a.val
  have hsum : ∑ a, p a = 1 := by
    simp_rw [← hdesc]
    rw [Fin.sum_univ_eq_sum_range, hρ.isHermitian.sum_descEigenvalue_card]
    exact posSemidef_trace_one_eigenvalues_sum_one hρ htrace
  have hmem : euclideanTensorEquiv σ β w ∈
      G.map (Tm.toLinearEquiv :
        E →ₗ[ℂ] EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β) := by
    dsimp only [w]
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact ⟨ψ, hψG, rfl⟩
  refine ⟨hp, hsum, vonNeumannEntropy_eq_probabilityEntropy_eigenvalues₀ hρ.isHermitian, ?_⟩
  intro δ S R hδ hSR hV
  have hmass0 := hV.one_sub_le_kyFanNorm hδ hmem hw
  have hmass : 1 - δ ≤ hρ.isHermitian.kyFanNorm R :=
    le_trans hmass0 (hρ.kyFanNorm_mono hSR)
  change (∑ a ∈ Finset.univ.filter
    (fun a : Fin (Fintype.card σ) ↦ R ≤ a.val), hρ.isHermitian.eigenvalues₀ a) ≤ δ
  rw [hρ.isHermitian.sum_eigenvalues₀_filter_le, htrace]
  simpa only [Complex.one_re] using (sub_le_comm.mp hmass)

/-- The exterior-first tensor identification followed by the tensor commutor
has exactly the region-first product coordinates of the original vector.
No compatibility between independently chosen identifications is assumed. -/
private theorem euclideanTensorEquiv_symm_actualRegionSplit
    {V : Type*} [Fintype V] [DecidableEq V]
    (siteType : V → Type*) [∀ v, Fintype (siteType v)] [∀ v, DecidableEq (siteType v)]
    (J : Finset V) (ψ : EuclideanSpace ℂ ((v : V) → siteType v)) :
    let σ := FiniteProduct.Configuration siteType J
    let β := FiniteProduct.Configuration siteType Jᶜ
    let tau := (FiniteProduct.splitEquiv siteType J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun β ℂ).tensorProduct
      (EuclideanSpace.basisFun σ ℂ)).repr
    let Tm := (U.trans Phi.symm).trans
      (TensorProduct.commIsometry ℂ (EuclideanSpace ℂ β) (EuclideanSpace ℂ σ))
    (euclideanTensorEquiv σ β).symm (Tm ψ) =
      WithLp.toLp 2 (fun x : σ × β ↦ ψ ((FiniteProduct.splitEquiv siteType J).symm x)) := by
  intro σ β tau U Phi Tm
  change (euclideanTensorEquiv σ β).symm
      (TensorProduct.commIsometry ℂ (EuclideanSpace ℂ β) (EuclideanSpace ℂ σ)
        (euclideanTensorEquiv β σ (U ψ))) = _
  rw [euclideanTensorEquiv_symm_comm]
  ext ⟨a, b⟩
  rfl

/-- In the canonical regional tensor coordinates, the coefficient Gram matrix
is the original regional state, and its von Neumann entropy is the original
regional entropy. No normalization of the vector is required. Supporting
coordinate identity for ALVV, arXiv:1602.08828v2, proof of Theorem `thm:al-dg`,
lines 1080–1094. -/
theorem actualRegionSplit_marginal_and_entropy
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (J : Finset V) (ψ : EuclideanSpace ℂ ((v : V) → Fin (n v))) :
    let siteType := fun v : V ↦ Fin (n v)
    let σ := FiniteProduct.Configuration siteType J
    let β := FiniteProduct.Configuration siteType Jᶜ
    let tau := (FiniteProduct.splitEquiv siteType J).trans (Equiv.prodComm _ _)
    let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ tau
    let Phi := ((EuclideanSpace.basisFun β ℂ).tensorProduct
      (EuclideanSpace.basisFun σ ℂ)).repr
    let Tm := (U.trans Phi.symm).trans
      (TensorProduct.commIsometry ℂ (EuclideanSpace ℂ β) (EuclideanSpace ℂ σ))
    let psiCoord := (euclideanTensorEquiv σ β).symm (Tm ψ)
    let C := Matrix.schmidtCoeffMatrix (WithLp.ofLp psiCoord)
    C * Cᴴ = Entropy.regionState J ψ ∧
      vonNeumannEntropy (C * Cᴴ) (Matrix.posSemidef_self_mul_conjTranspose C).isHermitian =
        Entropy.regionEntropy J ψ := by
  intro siteType σ β tau U Phi Tm psiCoord C
  have hsplit : psiCoord =
      WithLp.toLp 2 (fun x : σ × β ↦ ψ ((FiniteProduct.splitEquiv siteType J).symm x)) :=
    euclideanTensorEquiv_symm_actualRegionSplit siteType J ψ
  have hmarginal : C * Cᴴ = Entropy.regionState J ψ := by
    rw [Entropy.regionState_eq_reducedPure, FiniteProduct.reducedPure_eq_partialTrace,
      Matrix.partialTraceRight_vecMulVec_eq]
    exact congrArg (fun x : EuclideanSpace ℂ (σ × β) ↦
      Matrix.schmidtCoeffMatrix (WithLp.ofLp x) *
        (Matrix.schmidtCoeffMatrix (WithLp.ofLp x))ᴴ) hsplit
  exact ⟨hmarginal, vonNeumannEntropy_congr hmarginal _ _⟩

end Submodule
