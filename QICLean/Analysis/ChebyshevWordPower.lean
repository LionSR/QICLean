/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChebyshevViability
import QICLean.Analysis.TensorOperatorPower

/-!
# Ordered powers of an actual Chebyshev improving family

The Chebyshev polynomial and its actual complementary tensor factors are
chosen before every power and viable input space. Ordered words in the
common retained family then give the powered cardinality and suppression
bounds for one fixed original cluster. This supports ALVV,
arXiv:1602.08828v2, `thm:Cheby-AGSP`, lines 789–853, and `l:er`, lines 597–622.

**Local fix (closed cutoffs and the sign of the filter):** The closed
spectral convention and unsquared Chebyshev filter are those documented in
`docs/paper-gaps/alvv16_spectral_projector_boundary.tex` and
`docs/paper-gaps/alvv16_chebyshev_filter_positivity.tex`.
-/

open scoped BigOperators TensorProduct Matrix.Norms.L2Operator

namespace Matrix

/-- A common actual polynomial decomposition supplies one filter and its
complementary tensor factors before all input spaces. The filter preserves
the actual low cluster, has minimum gain one there, and contracts its
orthogonal complement. It need not be the identity or scalar on the low
band. The same factors also give every ordered word-family bound.
Supporting ALVV, arXiv:1602.08828v2, `thm:Cheby-AGSP`, lines 789–853,
and `l:er`, lines 597–622. Physical construction of the polynomial
family and spectral data remains separate. -/
theorem exists_chebyshev_tensor_family_of_actual_cluster
    {sigma iota m e : Type*}
    [Fintype sigma] [DecidableEq sigma] [Fintype iota]
    [Fintype m] [DecidableEq m] [Fintype e] [DecidableEq e] {N degree : ℕ}
    (B : Matrix sigma sigma ℂ) (hB : B.IsHermitian)
    (v : OrthonormalBasis iota ℂ (EuclideanSpace ℂ sigma)) (lam : iota → ℝ)
    (hv : ∀ i, B.toEuclideanLin (v i) = (lam i : ℂ) • v i)
    (W : Fin N → Matrix m m ℂ)
    (Tm : EuclideanSpace ℂ sigma ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
    (hdecomp : ∀ Q : Polynomial ℂ, Q.natDegree ≤ degree →
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := sigma) (Polynomial.aeval B Q) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ i, TensorProduct.mapL
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W i))
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M i)))
    (C : ℕ) (hN : N ≤ C)
    (eta0 eta1 upper : ℝ) (hsep : eta0 < eta1) (hupperEndpoint : eta1 ≤ upper)
    (hcluster : Submodule.spectralSpanLE v lam eta0 =
      Submodule.spectralSpanLE v lam eta1) (hnorm : ‖B‖ ≤ upper) :
    let A : Fin N → EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m :=
      fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W i)
    let T := (Submodule.spectralSpanLE v lam eta0).map Tm.toLinearEquiv.toLinearMap
    let Delta := (2 * Real.exp
      (-2 * (degree : ℝ) * Real.sqrt ((eta1 - eta0) / (upper - eta0)))) ^ 2
    ∃ (K : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →L[ℂ]
        (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
      (Rop : Fin N → EuclideanSpace ℂ e →L[ℂ] EuclideanSpace ℂ e),
      K = ∑ i, TensorProduct.mapL (A i) (Rop i) ∧
      (∀ t ∈ T, K t ∈ T) ∧ (∀ z ∈ Tᗮ, K z ∈ Tᗮ) ∧
      (∀ t ∈ T, ‖t‖ ≤ ‖K t‖) ∧
      (∀ z ∈ Tᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) ∧
    ∀ (r : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ m)) (delta : ℝ),
      Submodule.IsViable delta S T → delta < 1 →
      let grow := ⨆ w : Fin r → Fin N,
        S.map ((List.ofFn (fun j ↦ A (w j))).prod : _ →ₗ[ℂ] _)
      Module.finrank ℂ grow ≤ C ^ r * Module.finrank ℂ S ∧
        Submodule.IsViable (Delta ^ r / (1 - delta) ^ 2) grow T := by
  intro A T Delta
  obtain ⟨hH, hgap, hupper, hmap⟩ :=
    exists_canonical_isometric_spectral_data B hB v lam hv eta0 eta1 upper hcluster hnorm Tm
  let H : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →L[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) :=
    Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := sigma) B ∘L
      Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hH' : (H : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →ₗ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e)).IsSymmetric := hH
  obtain ⟨p, hdegree, _hpoint, hprojector⟩ :=
    Submodule.exists_isSpectralProjector_chebyshev H hH' rfl degree
      hsep hupperEndpoint hupper
  let Q := p.map (algebraMap ℝ ℂ)
  have hQ : Q.natDegree ≤ degree := Polynomial.natDegree_map_le.trans hdegree.le
  obtain ⟨M, hdecomposition⟩ := hdecomp Q hQ
  let Rop := fun i : Fin N ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M i)
  have hfilter : Polynomial.aeval H Q =
      Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := sigma) (Polynomial.aeval B Q) ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    let C := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := sigma)
    change Polynomial.aeval (Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv (C B)) Q =
      Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv (C (Polynomial.aeval B Q))
    exact (Polynomial.aeval_algHom_apply
      Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom (C B) Q).trans
        (congrArg Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom
          (Polynomial.aeval_algHom_apply C.toAlgEquiv.toAlgHom B Q))
  have hdec : Polynomial.aeval H Q = ∑ i, TensorProduct.mapL (A i) (Rop i) :=
    hfilter.trans hdecomposition
  have hT : T = Submodule.span ℂ
      (hH'.eigenvectorBasis rfl '' {j | hH'.eigenvalues rfl j ≤ eta0}) := hmap eta0
  obtain ⟨hKT, hKTo, hlow, hhigh⟩ := hprojector.contract hgap
  rw [← hT] at hKT hKTo hlow hhigh
  refine ⟨Polynomial.aeval H Q, Rop, hdec, hKT, hKTo, hlow, hhigh, ?_⟩
  intro r S delta hS hdelta grow
  rw [hT] at hS ⊢
  obtain ⟨hdimension, hviable⟩ :=
    hprojector.viability_word_power hgap (sq_nonneg _) A Rop hdec r S delta hS hdelta
  refine ⟨?_, hviable⟩
  exact hdimension.trans (Nat.mul_le_mul_right (Module.finrank ℂ S)
    (by simpa only [Fintype.card_fin] using Nat.pow_le_pow_left hN r))

/-- A common polynomial decomposition gives the actual ordered-word family
for every power, with one fixed transported low target. The actual matrix
cluster determines the symmetry, eigenbasis and filter. Supporting ALVV,
arXiv:1602.08828v2, `thm:Cheby-AGSP`, lines 789–853, and `l:er`, lines 597–622.
The polynomial decomposition is an input here; physical applications derive it. -/
lemma chebyshev_word_power_viability_of_actual_cluster_polynomial_family
    {sigma iota m e : Type*}
    [Fintype sigma] [DecidableEq sigma] [Fintype iota]
    [Fintype m] [DecidableEq m] [Fintype e] [DecidableEq e] {N degree : ℕ}
    (B : Matrix sigma sigma ℂ) (hB : B.IsHermitian)
    (v : OrthonormalBasis iota ℂ (EuclideanSpace ℂ sigma)) (lam : iota → ℝ)
    (hv : ∀ i, B.toEuclideanLin (v i) = (lam i : ℂ) • v i)
    (W : Fin N → Matrix m m ℂ)
    (Tm : EuclideanSpace ℂ sigma ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
    (hdecomp : ∀ Q : Polynomial ℂ, Q.natDegree ≤ degree →
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := sigma) (Polynomial.aeval B Q) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ i, TensorProduct.mapL
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W i))
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M i)))
    (C : ℕ) (hN : N ≤ C)
    (eta0 eta1 upper : ℝ) (hsep : eta0 < eta1) (hupperEndpoint : eta1 ≤ upper)
    (hcluster : Submodule.spectralSpanLE v lam eta0 =
      Submodule.spectralSpanLE v lam eta1) (hnorm : ‖B‖ ≤ upper) :
    let A : Fin N → EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m :=
      fun i ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W i)
    let T := (Submodule.spectralSpanLE v lam eta0).map Tm.toLinearEquiv.toLinearMap
    let Delta := (2 * Real.exp
      (-2 * (degree : ℝ) * Real.sqrt ((eta1 - eta0) / (upper - eta0)))) ^ 2
    ∀ (r : ℕ) (S : Submodule ℂ (EuclideanSpace ℂ m)) (delta : ℝ),
      Submodule.IsViable delta S T → delta < 1 →
      let grow := ⨆ w : Fin r → Fin N,
        S.map ((List.ofFn (fun j ↦ A (w j))).prod : _ →ₗ[ℂ] _)
      Module.finrank ℂ grow ≤ C ^ r * Module.finrank ℂ S ∧
        Submodule.IsViable (Delta ^ r / (1 - delta) ^ 2) grow T := by
  obtain ⟨_K, _Rop, _hdec, _hKT, _hKTo, _hlow, _hhigh, hwords⟩ :=
    exists_chebyshev_tensor_family_of_actual_cluster B hB v lam hv W Tm
      hdecomp C hN eta0 eta1 upper hsep hupperEndpoint hcluster hnorm
  exact hwords

end Matrix
