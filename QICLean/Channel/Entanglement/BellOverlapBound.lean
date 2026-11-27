/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.MaxEntangledOverlap
import QICLean.Channel.Entanglement.RankOneCoherence
import QICLean.Channel.Entanglement.SeparableOperation

/-!
# Dimension-independent all-copy Bell-overlap bound for locally factorized maps

This file establishes the dimension-independent all-copy Bell-overlap obstruction
generalizing Lemma 6 of arXiv:2611.34921v1 to arbitrary finite local dimensions,
arbitrary rectangular local completely positive maps `L, M`, and arbitrary complex
input vectors `u`.

Given `C(X ⊗ Y) = L(X) ⊗ M(Y)` admitting a single-copy reverse-block certificate `S`
(`C + S, C - S` CP, `S` coCP, `C(|u⟩⟨u|) = S(|u⟩⟨u|)`), and any nonnegative multiple
`ρ = c • C(|u⟩⟨u|)` (`c ≥ 0`), for every copy number `N : ℕ` and every finite
shared-index product-Kraus `SeparableOperation` `Λ` from `N` copies to two qubits:

  `Matrix.maxEntangledOverlap 2 (Λ.map (bipartiteCopies N ρ)) ≤ ((1 + √2) / 4) * Re tr(Λ(ρ^{⊗ N}))`.

## Proof mechanism

1. For a single product-Kraus branch `τ = (A ⊗ B) ρ^{⊗ N} (A ⊗ B)ᴴ`, the diagonal
   entries `pᵢⱼ = Re τ_{(i,j),(i,j)}` and coherence `k = ‖τ_{(0,0),(1,1)}‖` are rank-one
   matrix elements of `bipartiteCopies N ρ` on the rows of `A` and `B`.
2. `QuantumInfo.rankOne_coherence_pow_four_le_of_smul` yields `k ^ 4 ≤ p₀₀ p₀₁ p₁₀ p₁₁`,
   whence `k ≤ (1 / 2) √(s r)` for `s = p₀₀ + p₁₁` and `r = p₀₁ + p₁₀`.
3. Weighted AM-GM (`Real.half_add_sqrt_mul_le_bell_cap`) gives the linear bound
   `maxEntangledOverlap 2 τ ≤ ((1 + √2) / 4) * Re tr(τ)`, valid even when `τ = 0`.
4. Summing over any finite product-Kraus family `Λ` by linearity (with no extra
   Cauchy-Schwarz step) gives the unnormalized bound for `Λ`, and local-unitary
   closure extends it to every locally-unitary-equivalent two-qubit Bell state.
5. Normalization divides by `Re tr(Λ(ρ^{⊗ N}))` only under an explicit positivity
   hypothesis, or via `KrausFamily.trace_map` when `Λ.toKrausFamily.IsTP` and `tr ρ = 1`.

## Main results

* `QuantumInfo.bellOverlap_single_product_kraus_le` — single product-Kraus branch bound.
* `QuantumInfo.bellOverlap_separableOperation_le` — unnormalized linear bound for any
  finite product-Kraus `SeparableOperation` (including zero output).
* `QuantumInfo.bellOverlap_localUnitary_separableOperation_le` — extension to any
  locally-unitary-equivalent two-qubit Bell state `(U ⊗ V) |Ω₂⟩⟨Ω₂| (U ⊗ V)ᴴ`.
* `QuantumInfo.bellOverlap_div_trace_le` and
  `QuantumInfo.bellOverlap_normalized_separableOperation_le` — normalized fidelity cap
  `(1 + √2) / 4` for positive-trace outputs.
* `QuantumInfo.bellOverlap_tracePreserving_separableOperation_le` — cap for
  trace-preserving `SeparableOperation` on unit-trace `ρ`.
-/

open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace QuantumInfo

/-! ## Section 1: Explicit two-qubit Bell-overlap and trace formulas -/

/-- For a Hermitian two-qubit matrix `τ`, its overlap with `|Ω₂⟩⟨Ω₂|` is
`(1 / 2) * (Re τ_{(0,0),(0,0)} + Re τ_{(1,1),(1,1)} + 2 * Re τ_{(0,0),(1,1)})`. -/
theorem maxEntangledOverlap_two_eq_of_isHermitian
    {τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hτ : τ.IsHermitian) :
    Matrix.maxEntangledOverlap 2 τ =
      (1 / 2 : ℝ) *
        ((τ (0, 0) (0, 0)).re + (τ (1, 1) (1, 1)).re + 2 * (τ (0, 0) (1, 1)).re) := by
  have h1100 : (τ (1, 1) (0, 0)).re = (τ (0, 0) (1, 1)).re := by
    have h := congrFun (congrFun hτ.eq (1, 1)) (0, 0)
    simp only [Matrix.conjTranspose_apply] at h
    rw [← h, Complex.star_def, Complex.conj_re]
  rw [Matrix.maxEntangledOverlap_def]
  have hsq2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hω : ∀ i j k l : Fin 2,
      Matrix.omegaProj 2 (i, j) (k, l) =
        if i = j ∧ k = l then (2 : ℂ)⁻¹ else 0 := by
    intro i j k l
    simp only [Matrix.omegaProj_apply, Matrix.omegaVec_apply]
    by_cases h1 : i = j <;> by_cases h2 : k = l <;> simp [h1, h2, hsq2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    hω]
  norm_num [Complex.add_re, Complex.mul_re, h1100]
  ring

/-- The real part of the trace of a two-qubit matrix `τ` is the sum of its four diagonal
entries' real parts. -/
theorem trace_re_two_qubit (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    τ.trace.re =
      (τ (0, 0) (0, 0)).re + (τ (0, 1) (0, 1)).re +
        (τ (1, 0) (1, 0)).re + (τ (1, 1) (1, 1)).re := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.add_re]
  ring

/-- Entrywise formula for a single product-Kraus sandwich `(A ⊗ₖ B) * σ * (A ⊗ₖ B)ᴴ`
as a rank-one matrix element of `σ` on the conjugated rows of `A` and `B`. -/
theorem product_kraus_sandwich_apply
    {α β : Type} [Fintype α] [Fintype β]
    (A : Matrix (Fin 2) α ℂ) (B : Matrix (Fin 2) β ℂ)
    (σ : Matrix (α × β) (α × β) ℂ) (i j i' j' : Fin 2) :
    ((A ⊗ₖ B) * σ * (A ⊗ₖ B)ᴴ) (i, j) (i', j') =
      star (Matrix.vecKronecker (fun x => star (A i x)) (fun y => star (B j y))) ⬝ᵥ
        σ *ᵥ Matrix.vecKronecker (fun x => star (A i' x)) (fun y => star (B j' y)) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rcases p with ⟨p₁, p₂⟩
  rcases q with ⟨q₁, q₂⟩
  simp only [Matrix.vecKronecker_apply, star_mul', star_star]
  ring

/-! ## Section 2: Single product-Kraus branch bound -/

/-- **Single product-Kraus branch Bell-overlap cap.**
For any nonnegative multiple `ρ = c • C(|u⟩⟨u|)` (`c ≥ 0`) of a locally factorized
rectangular CP map `C = L ⊗ M` admitting a single-copy reverse-block certificate `S`,
every copy number `N : ℕ`, and any local Kraus operators `A, B` mapping `N` copies
to a qubit each, the unnormalized output `τ = (A ⊗ B) ρ^{⊗ N} (A ⊗ B)ᴴ` satisfies

  `maxEntangledOverlap 2 τ ≤ ((1 + √2) / 4) * Re tr(τ)`,

including when `τ = 0`, `A = 0`, `B = 0`, or `c = 0`. -/
theorem bellOverlap_single_product_kraus_le
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [DecidableEq A_out] [Fintype B_out] [DecidableEq B_out]
    {L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ}
    {M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ}
    {C S : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hL : IsKrausCP L) (hM : IsKrausCP M)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (hadd : IsKrausCP (C + S)) (hsub : IsKrausCP (C - S))
    (hcop : IsCompletelyCopositiveMap S)
    {u : A_in × B_in → ℂ}
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    {c : ℝ} (hc : 0 ≤ c)
    {ρ : Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hρ : ρ = (c : ℂ) • C (Matrix.vecMulVec u (star u)))
    (N : ℕ)
    (A : Matrix (Fin 2) (Fin N → A_out) ℂ)
    (B : Matrix (Fin 2) (Fin N → B_out) ℂ) :
    let τ := (A ⊗ₖ B) * QuantumInfo.bipartiteCopies N ρ * (A ⊗ₖ B)ᴴ
    Matrix.maxEntangledOverlap 2 τ ≤ ((1 + Real.sqrt 2) / 4) * τ.trace.re := by
  intro τ
  set ρ_N := QuantumInfo.bipartiteCopies N ρ
  -- Positivity of `ρ_N` and `τ`.
  have hCN_cp : IsKrausCP (QuantumInfo.localTensorCopies N L M) :=
    QuantumInfo.isKrausCP_localTensorCopies N hL hM
  have hRN_psd : (QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u)))).PosSemidef := by
    rw [← QuantumInfo.localTensorCopies_vecMulVec_eq_bipartiteCopies N L M C hC u]
    exact hCN_cp.map_posSemidef (Matrix.posSemidef_vecMulVec_self_star _)
  have hρN_psd : ρ_N.PosSemidef := by
    have hρN_eq :
        ρ_N = (c ^ N) • QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) := by
      rw [show ρ_N = QuantumInfo.bipartiteCopies N ((c : ℂ) • C (Matrix.vecMulVec u (star u)))
        from by simp [ρ_N, hρ]]
      rw [QuantumInfo.bipartiteCopies_smul, ← Complex.ofReal_pow]
      rfl
    rw [hρN_eq]
    exact hRN_psd.smul (pow_nonneg hc N)
  have hτ_psd : τ.PosSemidef := hρN_psd.mul_mul_conjTranspose_same (A ⊗ₖ B)
  -- Local filter vectors corresponding to the rows of `A` and `B`.
  let a₀ : (Fin N → A_out) → ℂ := fun x => star (A 0 x)
  let a₁ : (Fin N → A_out) → ℂ := fun x => star (A 1 x)
  let b₀ : (Fin N → B_out) → ℂ := fun y => star (B 0 y)
  let b₁ : (Fin N → B_out) → ℂ := fun y => star (B 1 y)
  have hcoh := QuantumInfo.rankOne_coherence_pow_four_le_of_smul
    hL hM hC hadd hsub hcop hu hc hρ N a₀ a₁ b₀ b₁
  dsimp only at hcoh
  -- Rewrite the matrix elements of `ρ_N` as entries of `τ`.
  have h00 : τ (0, 0) (0, 0) =
      star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₀ b₀ :=
    product_kraus_sandwich_apply A B ρ_N 0 0 0 0
  have h01 : τ (0, 1) (0, 1) =
      star (Matrix.vecKronecker a₀ b₁) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₀ b₁ :=
    product_kraus_sandwich_apply A B ρ_N 0 1 0 1
  have h10 : τ (1, 0) (1, 0) =
      star (Matrix.vecKronecker a₁ b₀) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₁ b₀ :=
    product_kraus_sandwich_apply A B ρ_N 1 0 1 0
  have h11 : τ (1, 1) (1, 1) =
      star (Matrix.vecKronecker a₁ b₁) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₁ b₁ :=
    product_kraus_sandwich_apply A B ρ_N 1 1 1 1
  have h0011 : τ (0, 0) (1, 1) =
      star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₁ b₁ :=
    product_kraus_sandwich_apply A B ρ_N 0 0 1 1
  set p00 := (τ (0, 0) (0, 0)).re
  set p01 := (τ (0, 1) (0, 1)).re
  set p10 := (τ (1, 0) (1, 0)).re
  set p11 := (τ (1, 1) (1, 1)).re
  set k := ‖τ (0, 0) (1, 1)‖
  have hp00_nn : 0 ≤ p00 := (Complex.nonneg_iff.mp hτ_psd.diag_nonneg).1
  have hp01_nn : 0 ≤ p01 := (Complex.nonneg_iff.mp hτ_psd.diag_nonneg).1
  have hp10_nn : 0 ≤ p10 := (Complex.nonneg_iff.mp hτ_psd.diag_nonneg).1
  have hp11_nn : 0 ≤ p11 := (Complex.nonneg_iff.mp hτ_psd.diag_nonneg).1
  have hk4 : k ^ 4 ≤ p00 * p01 * p10 * p11 := by
    simpa only [k, p00, p01, p10, p11, h00, h01, h10, h11, h0011] using hcoh
  have hk_le : k ≤ (1 / 2 : ℝ) * Real.sqrt ((p00 + p11) * (p01 + p10)) :=
    Real.le_half_sqrt_sum_mul_sum_of_pow_four_le (norm_nonneg _) hp00_nn hp01_nn hp10_nn hp11_nn hk4
  have hre_le : (τ (0, 0) (1, 1)).re ≤ k := Complex.re_le_norm _
  have hoverlap : Matrix.maxEntangledOverlap 2 τ =
      (1 / 2 : ℝ) * (p00 + p11 + 2 * (τ (0, 0) (1, 1)).re) :=
    maxEntangledOverlap_two_eq_of_isHermitian hτ_psd.isHermitian
  have htr : τ.trace.re = (p00 + p11) + (p01 + p10) := by
    rw [trace_re_two_qubit]
    ring
  have hamgm := Real.half_add_sqrt_mul_le_bell_cap (add_nonneg hp00_nn hp11_nn)
    (add_nonneg hp01_nn hp10_nn)
  rw [hoverlap, htr]
  linarith

/-! ## Section 3: Unnormalized linear bound for arbitrary product-Kraus operations -/

/-- **Unnormalized linear Bell-overlap bound for arbitrary product-Kraus separable operations.**
For any finite shared-index `SeparableOperation` `Λ` from `N` copies of `ρ = c • C(|u⟩⟨u|)`
(`c ≥ 0`) to two qubits, summing the single-branch bound by linearity yields

  `maxEntangledOverlap 2 (Λ.map (bipartiteCopies N ρ)) ≤ ((1 + √2) / 4) * Re tr(Λ(ρ^{⊗ N}))`.

No trace normalization or nonvanishing hypothesis is required; zero output (including empty
`Λ.Index`) is covered automatically. -/
theorem bellOverlap_separableOperation_le
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [DecidableEq A_out] [Fintype B_out] [DecidableEq B_out]
    {L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ}
    {M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ}
    {C S : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hL : IsKrausCP L) (hM : IsKrausCP M)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (hadd : IsKrausCP (C + S)) (hsub : IsKrausCP (C - S))
    (hcop : IsCompletelyCopositiveMap S)
    {u : A_in × B_in → ℂ}
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    {c : ℝ} (hc : 0 ≤ c)
    {ρ : Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hρ : ρ = (c : ℂ) • C (Matrix.vecMulVec u (star u)))
    (N : ℕ)
    (Λ : SeparableOperation (Fin N → A_out) (Fin N → B_out) (Fin 2) (Fin 2)) :
    Matrix.maxEntangledOverlap 2 (Λ.map (QuantumInfo.bipartiteCopies N ρ)) ≤
      ((1 + Real.sqrt 2) / 4) * (Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace.re := by
  rw [SeparableOperation.map_apply, Matrix.maxEntangledOverlap_sum, Matrix.trace_sum,
    Complex.re_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun α _ =>
    bellOverlap_single_product_kraus_le hL hM hC hadd hsub hcop hu hc hρ N (Λ.left α) (Λ.right α)

/-- **Unnormalized linear Bell-overlap bound for any locally-unitary-equivalent Bell state.**
For any local unitaries `U, V ∈ Matrix.unitaryGroup (Fin 2) ℂ`, the overlap of
`Λ(ρ^{⊗ N})` with `(U ⊗ V) |Ω₂⟩⟨Ω₂| (U ⊗ V)ᴴ` is bounded by
`((1 + √2) / 4) * Re tr(Λ(ρ^{⊗ N}))`. -/
theorem bellOverlap_localUnitary_separableOperation_le
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [DecidableEq A_out] [Fintype B_out] [DecidableEq B_out]
    {L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ}
    {M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ}
    {C S : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hL : IsKrausCP L) (hM : IsKrausCP M)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (hadd : IsKrausCP (C + S)) (hsub : IsKrausCP (C - S))
    (hcop : IsCompletelyCopositiveMap S)
    {u : A_in × B_in → ℂ}
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    {c : ℝ} (hc : 0 ≤ c)
    {ρ : Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hρ : ρ = (c : ℂ) • C (Matrix.vecMulVec u (star u)))
    (N : ℕ)
    (Λ : SeparableOperation (Fin N → A_out) (Fin N → B_out) (Fin 2) (Fin 2))
    (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    (((U.1 ⊗ₖ V.1) * Matrix.omegaProj 2 * (U.1 ⊗ₖ V.1)ᴴ) *
        Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace.re ≤
      ((1 + Real.sqrt 2) / 4) * (Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace.re := by
  let Λ' := (SeparableOperation.single U.1ᴴ V.1ᴴ).comp Λ
  have hbase := bellOverlap_separableOperation_le hL hM hC hadd hsub hcop hu hc hρ N Λ'
  have hmap : Λ'.map (QuantumInfo.bipartiteCopies N ρ) =
      (U.1 ⊗ₖ V.1)ᴴ * Λ.map (QuantumInfo.bipartiteCopies N ρ) * (U.1 ⊗ₖ V.1) := by
    simp only [Λ', SeparableOperation.map_comp, SeparableOperation.map_single,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose]
  have hUV_unit : (U.1 ⊗ₖ V.1) * (U.1 ⊗ₖ V.1)ᴴ = 1 := by
    have hU : U.1 * U.1ᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp U.2
    have hV : V.1 * V.1ᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp V.2
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV,
      Matrix.one_kronecker_one]
  have hoverlap :
      Matrix.maxEntangledOverlap 2 (Λ'.map (QuantumInfo.bipartiteCopies N ρ)) =
        (((U.1 ⊗ₖ V.1) * Matrix.omegaProj 2 * (U.1 ⊗ₖ V.1)ᴴ) *
          Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace.re := by
    rw [Matrix.maxEntangledOverlap_def, hmap]
    congr 1
    calc
      (Matrix.omegaProj 2 *
          ((U.1 ⊗ₖ V.1)ᴴ * Λ.map (QuantumInfo.bipartiteCopies N ρ) * (U.1 ⊗ₖ V.1))).trace
        = ((Matrix.omegaProj 2 * (U.1 ⊗ₖ V.1)ᴴ * Λ.map (QuantumInfo.bipartiteCopies N ρ)) *
            (U.1 ⊗ₖ V.1)).trace := by simp [Matrix.mul_assoc]
      _ = ((U.1 ⊗ₖ V.1) *
            (Matrix.omegaProj 2 * (U.1 ⊗ₖ V.1)ᴴ * Λ.map (QuantumInfo.bipartiteCopies N ρ))).trace :=
          Matrix.trace_mul_comm _ _
      _ = (((U.1 ⊗ₖ V.1) * Matrix.omegaProj 2 * (U.1 ⊗ₖ V.1)ᴴ) *
            Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace := by simp [Matrix.mul_assoc]
  have htr :
      (Λ'.map (QuantumInfo.bipartiteCopies N ρ)).trace =
        (Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace := by
    rw [hmap]
    calc
      ((U.1 ⊗ₖ V.1)ᴴ * Λ.map (QuantumInfo.bipartiteCopies N ρ) * (U.1 ⊗ₖ V.1)).trace
        = ((U.1 ⊗ₖ V.1) * ((U.1 ⊗ₖ V.1)ᴴ * Λ.map (QuantumInfo.bipartiteCopies N ρ))).trace :=
          Matrix.trace_mul_comm _ _
      _ = (((U.1 ⊗ₖ V.1) * (U.1 ⊗ₖ V.1)ᴴ) * Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace := by
          simp [Matrix.mul_assoc]
      _ = (Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace := by rw [hUV_unit, Matrix.one_mul]
  rwa [hoverlap, htr] at hbase

/-! ## Section 4: Normalized fidelity caps (only with positive trace or TP) -/

/-- **Normalized Bell-overlap ratio cap for positive-trace outputs.** -/
theorem bellOverlap_div_trace_le
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [DecidableEq A_out] [Fintype B_out] [DecidableEq B_out]
    {L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ}
    {M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ}
    {C S : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hL : IsKrausCP L) (hM : IsKrausCP M)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (hadd : IsKrausCP (C + S)) (hsub : IsKrausCP (C - S))
    (hcop : IsCompletelyCopositiveMap S)
    {u : A_in × B_in → ℂ}
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    {c : ℝ} (hc : 0 ≤ c)
    {ρ : Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hρ : ρ = (c : ℂ) • C (Matrix.vecMulVec u (star u)))
    (N : ℕ)
    (Λ : SeparableOperation (Fin N → A_out) (Fin N → B_out) (Fin 2) (Fin 2))
    (htr : 0 < (Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace.re) :
    Matrix.maxEntangledOverlap 2 (Λ.map (QuantumInfo.bipartiteCopies N ρ)) /
        (Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace.re ≤
      (1 + Real.sqrt 2) / 4 := by
  rw [div_le_iff₀ htr]
  exact bellOverlap_separableOperation_le hL hM hC hadd hsub hcop hu hc hρ N Λ

/-- **Normalized Bell-overlap cap on the renormalized output state.** -/
theorem bellOverlap_normalized_separableOperation_le
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [DecidableEq A_out] [Fintype B_out] [DecidableEq B_out]
    {L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ}
    {M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ}
    {C S : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hL : IsKrausCP L) (hM : IsKrausCP M)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (hadd : IsKrausCP (C + S)) (hsub : IsKrausCP (C - S))
    (hcop : IsCompletelyCopositiveMap S)
    {u : A_in × B_in → ℂ}
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    {c : ℝ} (hc : 0 ≤ c)
    {ρ : Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hρ : ρ = (c : ℂ) • C (Matrix.vecMulVec u (star u)))
    (N : ℕ)
    (Λ : SeparableOperation (Fin N → A_out) (Fin N → B_out) (Fin 2) (Fin 2))
    (htr : 0 < (Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace.re) :
    Matrix.maxEntangledOverlap 2
        (((Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace.re)⁻¹ •
          Λ.map (QuantumInfo.bipartiteCopies N ρ)) ≤
      (1 + Real.sqrt 2) / 4 := by
  rw [Matrix.maxEntangledOverlap_smul_real, inv_mul_eq_div]
  exact bellOverlap_div_trace_le hL hM hC hadd hsub hcop hu hc hρ N Λ htr

/-- **Bell-overlap cap for a trace-preserving separable operation on a unit-trace state `ρ`.**
Uses `KrausFamily.trace_map` directly on `Λ.toKrausFamily`. -/
theorem bellOverlap_tracePreserving_separableOperation_le
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [DecidableEq A_out] [Fintype B_out] [DecidableEq B_out]
    {L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ}
    {M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ}
    {C S : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hL : IsKrausCP L) (hM : IsKrausCP M)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (hadd : IsKrausCP (C + S)) (hsub : IsKrausCP (C - S))
    (hcop : IsCompletelyCopositiveMap S)
    {u : A_in × B_in → ℂ}
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    {c : ℝ} (hc : 0 ≤ c)
    {ρ : Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hρ : ρ = (c : ℂ) • C (Matrix.vecMulVec u (star u)))
    (hρ_tr : ρ.trace = 1)
    (N : ℕ)
    (Λ : SeparableOperation (Fin N → A_out) (Fin N → B_out) (Fin 2) (Fin 2))
    (hTP : Λ.toKrausFamily.IsTP) :
    Matrix.maxEntangledOverlap 2 (Λ.map (QuantumInfo.bipartiteCopies N ρ)) ≤
      (1 + Real.sqrt 2) / 4 := by
  have hbound := bellOverlap_separableOperation_le hL hM hC hadd hsub hcop hu hc hρ N Λ
  have htr : (Λ.map (QuantumInfo.bipartiteCopies N ρ)).trace = 1 := by
    change (Λ.toKrausFamily.map (QuantumInfo.bipartiteCopies N ρ)).trace = 1
    rw [KrausFamily.trace_map hTP, QuantumInfo.trace_bipartiteCopies_eq_one N hρ_tr]
  simpa [htr] using hbound

end QuantumInfo
