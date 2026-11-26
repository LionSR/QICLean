/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Filter.ChebyshevSpectralProjector
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv
import QICLean.Spectral.LowEnergy.Coordinates
import QICLean.Analysis.TensorProduct.OperatorPower

/-!
# Chebyshev improvement of viable subspaces from a common polynomial family

A uniform polynomial reduction gives an enlargement of a viable subspace by
applying the actual Chebyshev filter. A common finite matrix family supplies
such a reduction through its conjugated tensor decomposition. Its cardinality,
or any prescribed numerical upper bound on it, controls the dimension increase.

These are supporting compositions for ALVV, arXiv:1602.08828v2,
Theorem `thm:Cheby-AGSP`, lines 789–853, Lemma `l:er`, lines 597–622, and
Proposition 5.7, lines 1311–1333. The polynomial decomposition is supplied
explicitly; no physical representation or algorithmic bound is asserted.

**Local fix (closed spectral conditions and the sign of the filter).** The three
consequences in this module use the closed low/high spectral conditions and
`δ < 1` from the error-reduction estimate. They do not assert positivity of the
unsquared Chebyshev filter. These points are documented in
`docs/paper-gaps/alvv16_spectral_projector_boundary.tex` and
`docs/paper-gaps/alvv16_chebyshev_filter_positivity.tex`, published at
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf and
https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf.

It also contains the following results.

* `Matrix.exists_chebyshev_tensor_family_of_actual_cluster`,
  `Matrix.chebyshev_word_power_viability_of_actual_cluster_polynomial_family`: ordered powers of an
  actual Chebyshev improving family.
-/

section ChebyshevViability

open scoped TensorProduct InnerProductSpace

namespace Submodule

/-- Compose a uniform polynomial viability reduction with the actual Chebyshev
filter. The enlargement operation and polynomial-filter reduction are supplied
before the spectral endpoints and before the subspace to be improved.
Supporting composition for ALVV, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`
and Lemma `l:er`; this is not a separate physical representation assertion. -/
theorem chebyshev_viability_of_polynomial_reduction
    {HM HE : Type*}
    [NormedAddCommGroup HM] [InnerProductSpace ℂ HM] [FiniteDimensional ℂ HM]
    [NormedAddCommGroup HE] [InnerProductSpace ℂ HE] [FiniteDimensional ℂ HE]
    {n k R : ℕ}
    (Hm : (HM ⊗[ℂ] HE) →L[ℂ] (HM ⊗[ℂ] HE))
    (hHm : (Hm : (HM ⊗[ℂ] HE) →ₗ[ℂ] (HM ⊗[ℂ] HE)).IsSymmetric)
    (hn : Module.finrank ℂ (HM ⊗[ℂ] HE) = n)
    (grow : Submodule ℂ HM → Submodule ℂ HM)
    (filter : Polynomial ℂ → (HM ⊗[ℂ] HE) →L[ℂ] (HM ⊗[ℂ] HE))
    (hfilter : ∀ Q, filter Q = Polynomial.aeval Hm Q)
    (hreduce : ∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
      ∀ (S : Submodule ℂ HM) (G : Submodule ℂ (HM ⊗[ℂ] HE)) (δ Δ : ℝ),
        IsViable (𝕜 := ℂ) (E := HM) (F := HE) δ S G → δ < 1 → 0 ≤ Δ →
        (∀ v ∈ G, filter Q v ∈ G) → (∀ v ∈ Gᗮ, filter Q v ∈ Gᗮ) →
        (∀ v ∈ G, ‖v‖ ≤ ‖filter Q v‖) →
        (∀ v ∈ Gᗮ, ‖filter Q v‖ ^ (2 : ℕ) ≤ Δ * ‖v‖ ^ (2 : ℕ)) →
        Module.finrank ℂ (grow S) ≤ R * Module.finrank ℂ S ∧
          IsViable (𝕜 := ℂ) (E := HM) (F := HE)
            (Δ / (1 - δ) ^ (2 : ℕ)) (grow S) G)
    {η₀ η₁ u : ℝ} (hsep : η₀ < η₁) (hupperEndpoint : η₁ ≤ u)
    (hupper : ∀ j, hHm.eigenvalues hn j ≤ u)
    (hgap : ∀ j, hHm.eigenvalues hn j ≤ η₀ ∨ η₁ ≤ hHm.eigenvalues hn j) :
    let G : Submodule ℂ (HM ⊗[ℂ] HE) := Submodule.span ℂ
      (hHm.eigenvectorBasis hn '' {j | hHm.eigenvalues hn j ≤ η₀})
    let Δ : ℝ := (2 * Real.exp
      (-2 * (k : ℝ) * Real.sqrt ((η₁ - η₀) / (u - η₀)))) ^ (2 : ℕ)
    ∀ (S : Submodule ℂ HM) (δ : ℝ),
      IsViable (𝕜 := ℂ) (E := HM) (F := HE) δ S G → δ < 1 →
      Module.finrank ℂ (grow S) ≤ R * Module.finrank ℂ S ∧
        IsViable (𝕜 := ℂ) (E := HM) (F := HE)
          (Δ / (1 - δ) ^ (2 : ℕ)) (grow S) G := by
  intro G Δ
  obtain ⟨p, hdegree, _hpoint, hprojector⟩ :=
    exists_isSpectralProjector_chebyshev Hm hHm hn k hsep hupperEndpoint hupper
  let Q : Polynomial ℂ := p.map (algebraMap ℝ ℂ)
  have hQdegree : Q.natDegree ≤ k := Polynomial.natDegree_map_le.trans hdegree.le
  have hprojector' : IsSpectralProjector (filter Q) Hm (hHm.eigenvectorBasis hn)
      (hHm.eigenvalues hn) (fun j ↦ p.eval (hHm.eigenvalues hn j)) η₀ η₁ Δ := by
    rw [hfilter Q]
    exact hprojector
  obtain ⟨hKT, hKTo, hlow, hhigh⟩ := hprojector'.contract hgap
  intro S δ hS hδ
  exact hreduce Q hQdegree S G δ Δ hS hδ (sq_nonneg _) hKT hKTo hlow hhigh

end Submodule

namespace Matrix

open scoped BigOperators TensorProduct InnerProductSpace

/-- A common matrix family with a supplied uniform conjugated polynomial
expansion improves viability for the actual Chebyshev filter. This is an
abstract finite-matrix composition for ALVV, arXiv:1602.08828v2,
Theorem `thm:Cheby-AGSP`, lines 789–853, and Lemma `l:er`, lines 606–622.
The polynomial expansion is an explicit input, not a physical assumption
derived from arbitrary trace data. -/
theorem chebyshev_viability_of_conjugated_polynomial_family
    {σ m e : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] {N k : ℕ}
    (H : Matrix σ σ ℂ) (W : Fin N → Matrix m m ℂ)
    (Tm : EuclideanSpace ℂ σ ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
    (hdecomp : ∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (Polynomial.aeval H Q) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ r, TensorProduct.mapL
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r))
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r))) :
    let Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →L[ℂ]
        (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) :=
      Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) H ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap
    let A : Fin N → EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m := fun r ↦
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r)
    let grow : Submodule ℂ (EuclideanSpace ℂ m) → Submodule ℂ (EuclideanSpace ℂ m) :=
      fun S ↦ ⨆ r : Fin N, S.map (A r : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ m)
    ∀ hHm : (Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →ₗ[ℂ]
        (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e)).IsSymmetric,
      ∀ (d : ℕ) (hn : Module.finrank ℂ
          (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) = d),
        ∀ η₀ η₁ u : ℝ, η₀ < η₁ → η₁ ≤ u →
          (∀ j, hHm.eigenvalues hn j ≤ u) →
          (∀ j, hHm.eigenvalues hn j ≤ η₀ ∨ η₁ ≤ hHm.eigenvalues hn j) →
          let G : Submodule ℂ (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) :=
            Submodule.span ℂ (hHm.eigenvectorBasis hn ''
              {j | hHm.eigenvalues hn j ≤ η₀})
          let Δ : ℝ := (2 * Real.exp
            (-2 * (k : ℝ) * Real.sqrt ((η₁ - η₀) / (u - η₀)))) ^ (2 : ℕ)
          ∀ (S : Submodule ℂ (EuclideanSpace ℂ m)) (δ : ℝ),
            Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ m)
              (F := EuclideanSpace ℂ e) δ S G → δ < 1 →
            Module.finrank ℂ (grow S) ≤ N * Module.finrank ℂ S ∧
              Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ m)
                (F := EuclideanSpace ℂ e) (Δ / (1 - δ) ^ (2 : ℕ)) (grow S) G := by
  intro Hm A grow hHm d hn η₀ η₁ u hsep hupperEndpoint hupper hgap G Δ
  let C := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ)
  let filter : Polynomial ℂ →
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →L[ℂ]
        (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) := fun Q ↦
    Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      C (Polynomial.aeval H Q) ∘L
      Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfilter (Q : Polynomial ℂ) : filter Q = Polynomial.aeval Hm Q := by
    symm
    change Polynomial.aeval (Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv (C H)) Q =
      Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv (C (Polynomial.aeval H Q))
    exact (Polynomial.aeval_algHom_apply
      Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom (C H) Q).trans
        (congrArg Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom
          (Polynomial.aeval_algHom_apply C.toAlgEquiv.toAlgHom H Q))
  exact Submodule.chebyshev_viability_of_polynomial_reduction
    (HM := EuclideanSpace ℂ m) (HE := EuclideanSpace ℂ e)
    (n := d) (k := k) (R := N) Hm hHm hn grow filter hfilter (by
      intro Q hQ
      obtain ⟨M, hdec⟩ := hdecomp Q hQ
      let Rop : Fin N → EuclideanSpace ℂ e →L[ℂ] EuclideanSpace ℂ e := fun r ↦
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r)
      have hdec' : filter Q = ∑ r, TensorProduct.mapL (A r) (Rop r) := hdec
      intro S T δ Δ hS hδ hΔ hKT hKTo hlow hhigh
      obtain ⟨hdim, hviable⟩ :=
        Submodule.IsViable.map_of_tensor_decomposition
          (𝕜 := ℂ) (M := EuclideanSpace ℂ m) (R := EuclideanSpace ℂ e) (ι := Fin N)
          (δ := δ) (Δ := Δ) (S := S) (T := T) (K := filter Q)
          hS A Rop hdec' hδ hΔ hKT hKTo hlow hhigh
      exact ⟨by simpa only [Fintype.card_fin] using hdim, hviable⟩)
      hsep hupperEndpoint hupper hgap

open scoped BigOperators TensorProduct InnerProductSpace

/-- A numerical upper bound on the size of a common matrix family gives
an upper bound on the dimension of the enlarged viable space. Supporting
ALVV, arXiv:1602.08828v2, Proposition 5.7, lines 1311–1333, and
Lemma `l:er`, lines 606–622. The polynomial decomposition, spectral hypotheses
and Chebyshev estimate are those of the preceding abstract theorem. -/
theorem chebyshev_viability_of_conjugated_polynomial_family_of_card_le
    {σ m e : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype m] [DecidableEq m]
    [Fintype e] [DecidableEq e] {N k : ℕ}
    (H : Matrix σ σ ℂ) (W : Fin N → Matrix m m ℂ)
    (Tm : EuclideanSpace ℂ σ ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
    (hdecomp : ∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (Polynomial.aeval H Q) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ r, TensorProduct.mapL
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r))
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r)))
    (C : ℕ) (hN : N ≤ C) :
    let Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →L[ℂ]
        (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) :=
      Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) H ∘L
        Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap
    let A : Fin N → EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m := fun r ↦
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r)
    let grow : Submodule ℂ (EuclideanSpace ℂ m) → Submodule ℂ (EuclideanSpace ℂ m) :=
      fun S ↦ ⨆ r : Fin N, S.map (A r : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ m)
    ∀ hHm : (Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →ₗ[ℂ]
        (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e)).IsSymmetric,
      ∀ (d : ℕ) (hn : Module.finrank ℂ
          (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) = d),
        ∀ η₀ η₁ u : ℝ, η₀ < η₁ → η₁ ≤ u →
          (∀ j, hHm.eigenvalues hn j ≤ u) →
          (∀ j, hHm.eigenvalues hn j ≤ η₀ ∨ η₁ ≤ hHm.eigenvalues hn j) →
          let G : Submodule ℂ (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) :=
            Submodule.span ℂ (hHm.eigenvectorBasis hn ''
              {j | hHm.eigenvalues hn j ≤ η₀})
          let Δ : ℝ := (2 * Real.exp
            (-2 * (k : ℝ) * Real.sqrt ((η₁ - η₀) / (u - η₀)))) ^ (2 : ℕ)
          ∀ (S : Submodule ℂ (EuclideanSpace ℂ m)) (δ : ℝ),
            Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ m)
              (F := EuclideanSpace ℂ e) δ S G → δ < 1 →
            Module.finrank ℂ (grow S) ≤ C * Module.finrank ℂ S ∧
              Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ m)
                (F := EuclideanSpace ℂ e) (Δ / (1 - δ) ^ (2 : ℕ)) (grow S) G := by
  intro Hm A grow hHm d hn η₀ η₁ u hsep hupperEndpoint hupper hgap G Δ S δ hS hδ
  obtain ⟨hdim, hviable⟩ :=
    chebyshev_viability_of_conjugated_polynomial_family H W Tm hdecomp
      hHm d hn η₀ η₁ u hsep hupperEndpoint hupper hgap S δ hS hδ
  exact ⟨hdim.trans (Nat.mul_le_mul_right (Module.finrank ℂ S) hN), hviable⟩

end Matrix


section

open scoped Matrix.Norms.L2Operator

open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator

namespace Matrix

/-- An actual Hermitian matrix with equal source low spans gives Chebyshev
viability for their isometric image. Canonical symmetry, eigenvalue separation
and the canonical spectral upper bound are derived from the actual matrix data.
The polynomial family and its numerical cardinal bound remain explicit inputs.
Auxiliary to ALVV, arXiv:1602.08828v2, Theorem `thm:Cheby-AGSP`, lines 789–853,
Lemma `l:er`, lines 606–622, and Theorem `t:ais`, lines 1010–1024.

The closed spectral convention and `δ < 1` are those of the companion notes
https://sirui-lu.com/QICLean/paper-gaps/alvv16_spectral_projector_boundary.pdf
and https://sirui-lu.com/QICLean/paper-gaps/alvv16_chebyshev_filter_positivity.pdf.
This is an auxiliary composition, not the physical DG existence theorem. -/
theorem chebyshev_viability_of_actual_cluster_polynomial_family
    {σ ι m e : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype ι]
    [Fintype m] [DecidableEq m] [Fintype e] [DecidableEq e]
    {N k : ℕ}
    (B : Matrix σ σ ℂ) (hB : B.IsHermitian)
    (v : OrthonormalBasis ι ℂ (EuclideanSpace ℂ σ)) (lam : ι → ℝ)
    (hv : ∀ i, B.toEuclideanLin (v i) = (lam i : ℂ) • v i)
    (W : Fin N → Matrix m m ℂ)
    (Tm : EuclideanSpace ℂ σ ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
    (hdecomp : ∀ Q : Polynomial ℂ, Q.natDegree ≤ k →
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (Polynomial.aeval B Q) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ r, TensorProduct.mapL
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r))
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r)))
    (C : ℕ) (hN : N ≤ C)
    (η₀ η₁ U : ℝ) (hsep : η₀ < η₁) (hupperEndpoint : η₁ ≤ U)
    (hcluster : Submodule.spectralSpanLE v lam η₀ =
      Submodule.spectralSpanLE v lam η₁)
    (hnorm : ‖B‖ ≤ U) :
    let A : Fin N → EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m := fun r ↦
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r)
    let grow : Submodule ℂ (EuclideanSpace ℂ m) → Submodule ℂ (EuclideanSpace ℂ m) :=
      fun S ↦ ⨆ r : Fin N, S.map (A r : EuclideanSpace ℂ m →ₗ[ℂ] EuclideanSpace ℂ m)
    let G : Submodule ℂ (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) :=
      (Submodule.spectralSpanLE v lam η₀).map
        (Tm.toLinearEquiv : EuclideanSpace ℂ σ →ₗ[ℂ]
          (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
    let Δ : ℝ := (2 * Real.exp
      (-2 * (k : ℝ) * Real.sqrt ((η₁ - η₀) / (U - η₀)))) ^ (2 : ℕ)
    ∀ (S : Submodule ℂ (EuclideanSpace ℂ m)) (δ : ℝ),
      Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ m)
        (F := EuclideanSpace ℂ e) δ S G → δ < 1 →
      Module.finrank ℂ (grow S) ≤ C * Module.finrank ℂ S ∧
        Submodule.IsViable (𝕜 := ℂ) (E := EuclideanSpace ℂ m)
          (F := EuclideanSpace ℂ e) (Δ / (1 - δ) ^ (2 : ℕ)) (grow S) G := by
  intro A grow G Δ
  obtain ⟨hK, hgap, hupper, hmap⟩ :=
    exists_canonical_isometric_spectral_data B hB v lam hv η₀ η₁ U hcluster hnorm Tm
  let Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →L[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) :=
    Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) B ∘L
      Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hHm : (Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →ₗ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e)).IsSymmetric := hK
  let d := Module.finrank ℂ (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e)
  have hG : G = Submodule.span ℂ
      (hHm.eigenvectorBasis (rfl : Module.finrank ℂ
        (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) = d) ''
        {j | hHm.eigenvalues rfl j ≤ η₀}) := hmap η₀
  intro S δ hS hδ
  rw [hG] at hS ⊢
  exact chebyshev_viability_of_conjugated_polynomial_family_of_card_le
    B W Tm hdecomp C hN hHm d rfl η₀ η₁ U hsep hupperEndpoint hupper hgap S δ hS hδ
end Matrix
end

section NestedChebyshevViability

/-!
# A Chebyshev filter between two nested spectral spaces

A uniform finite product decomposition of polynomials in one actual matrix
supplies the middle operators of a Chebyshev filter. Viability for the upper
closed spectral space improves to viability for the lower one. The spectrum
between the two cutoffs may be arbitrary. The polynomial and its actual
conjugated decomposition precede every viable subspace.

This is an abstract matrix composition for ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1037–1041. The polynomial-family decomposition
is an explicit hypothesis here; the physical chain construction derives it
separately from the original supported interactions.

**Local fix (spectral boundaries):** The closed cutoffs and `delta < 1`
are the conventions of `docs/paper-gaps/alvv16_spectral_projector_boundary.tex`.
The squared contraction allows oscillating values of the polynomial.
-/

open scoped BigOperators TensorProduct InnerProductSpace Matrix.Norms.L2Operator

namespace Matrix

/-- A common polynomial family gives one actual Chebyshev filter and its
finite tensor decomposition before any viable subspace is chosen. It
improves viability from the upper closed spectral span to the lower one,
without assuming a gap between them. The polynomial family is an explicit
input to this auxiliary; the physical theorem constructs it separately.
ALVV, arXiv:1602.08828v2, Theorem `t:aisgapless`, lines 1037–1041. -/
theorem exists_chebyshev_nested_viability_of_polynomial_family
    {σ ι m e : Type*}
    [Fintype σ] [DecidableEq σ] [Fintype ι]
    [Fintype m] [DecidableEq m] [Fintype e] [DecidableEq e]
    {N degree : ℕ}
    (B : Matrix σ σ ℂ) (hB : B.IsHermitian)
    (v : OrthonormalBasis ι ℂ (EuclideanSpace ℂ σ)) (lam : ι → ℝ)
    (hv : ∀ i, B.toEuclideanLin (v i) = (lam i : ℂ) • v i)
    (W : Fin N → Matrix m m ℂ)
    (Tm : EuclideanSpace ℂ σ ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e))
    (hdecomp : ∀ Q : Polynomial ℂ, Q.natDegree ≤ degree →
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (Polynomial.aeval B Q) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ r, TensorProduct.mapL
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r))
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r)))
    (eta0 eta1 upper : ℝ) (hsep : eta0 < eta1) (hend : eta1 ≤ upper)
    (hnorm : ‖B‖ ≤ upper) :
    let A : Fin N → EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m := fun r ↦
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := m) (W r)
    let lower := (Submodule.spectralSpanLE v lam eta0).map Tm.toLinearEquiv.toLinearMap
    let higher := (Submodule.spectralSpanLE v lam eta1).map Tm.toLinearEquiv.toLinearMap
    let Delta := (2 * Real.exp
      (-2 * (degree : ℝ) * Real.sqrt ((eta1 - eta0) / (upper - eta0)))) ^ 2
    ∃ p : Polynomial ℝ, p.natDegree = degree ∧ p.eval eta0 = 1 ∧
      ∃ M : Fin N → Matrix e e ℂ,
        Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
            Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ)
              (Polynomial.aeval B (p.map (algebraMap ℝ ℂ))) ∘L
            Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap =
          ∑ r, TensorProduct.mapL (A r)
            (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r)) ∧
        ∀ (S : Submodule ℂ (EuclideanSpace ℂ m)) (delta : ℝ),
          Submodule.IsViable (F := EuclideanSpace ℂ e) delta S higher → delta < 1 →
          let grow := ⨆ r : Fin N, S.map (A r).toLinearMap
          Module.finrank ℂ grow ≤ N * Module.finrank ℂ S ∧
            Submodule.IsViable (F := EuclideanSpace ℂ e)
              (Delta / (1 - delta) ^ 2) grow lower := by
  intro A lower higher Delta
  -- Coincident endpoints obtain only the canonical coordinates, without a gap.
  obtain ⟨hK, _htrivial, hupper, hmap⟩ :=
    Matrix.exists_canonical_isometric_spectral_data B hB v lam hv eta0 eta0 upper rfl hnorm Tm
  let Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →L[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) :=
    Tm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) B ∘L
      Tm.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hHm : (Hm : (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e) →ₗ[ℂ]
      (EuclideanSpace ℂ m ⊗[ℂ] EuclideanSpace ℂ e)).IsSymmetric := hK
  have hhigher : higher = Submodule.span ℂ
      (hHm.eigenvectorBasis rfl '' {j | hHm.eigenvalues rfl j ≤ eta1}) := hmap eta1
  have hlower : lower = Submodule.span ℂ
      (hHm.eigenvectorBasis rfl '' {j | hHm.eigenvalues rfl j ≤ eta0}) := hmap eta0
  obtain ⟨p, hdegree, hp0, hp⟩ :=
    Submodule.exists_isSpectralProjector_chebyshev Hm hHm rfl degree hsep hend hupper
  obtain ⟨M, hM⟩ := hdecomp (p.map (algebraMap ℝ ℂ))
    (Polynomial.natDegree_map_le.trans hdegree.le)
  have hfilter (Q : Polynomial ℂ) : Polynomial.aeval Hm Q =
      Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) (Polynomial.aeval B Q)) :=
    (Polynomial.aeval_algHom_apply
      Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ) B) Q).trans
      (congrArg Tm.toContinuousLinearEquiv.conjContinuousAlgEquiv.toAlgEquiv.toAlgHom
        (Polynomial.aeval_algHom_apply
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := σ)).toAlgEquiv.toAlgHom B Q))
  refine ⟨p, hdegree, hp0, M, hM, fun S delta hS hdelta ↦ ?_⟩
  rw [hhigher] at hS
  simpa only [hlower, Fintype.card_fin] using
    (Submodule.IsViable.spectralProjector_between_cutoffs
      (𝕜 := ℂ) (M := EuclideanSpace ℂ m) (R := EuclideanSpace ℂ e) hp hsep.le A
      (fun r ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) (n := e) (M r))
      ((hfilter _).trans hM) hS hdelta (sq_nonneg _))

end Matrix

end NestedChebyshevViability

end ChebyshevViability

section ChebyshevWordPower

/-!
## Ordered powers of an actual Chebyshev improving family

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

end ChebyshevWordPower
