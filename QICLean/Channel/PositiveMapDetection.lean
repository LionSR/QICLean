/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Channel.EntanglementWitness
import QICLean.Channel.Schwarz.ChoiCompression

/-!
# Positive maps from entanglement witnesses (Wolf Proposition 3.4)

Wolf's Chapter 3, Section 3.2 (Proposition 3.4) detects a bipartite state of Schmidt
number larger than `n` by an `n`-positive map: through the Choi–Jamiołkowski
correspondence, the entanglement witness of Proposition 3.3 becomes the Choi matrix of an
`n`-positive map under which the state fails to stay positive semidefinite.

This file supplies the two correspondence steps that turn the witness into an
`n`-positive map.

## The Choi correspondence as a linear isomorphism

The rectangular Choi correspondence assigns to every operator on
`ℂ^d ⊗ ℂ^{d'}` the map `P : M_{d'}(ℂ) → M_d(ℂ)` recovered by Wolf's inverse formula,
`ChoiRectangular.mapOfChoiMatrix`. In particular the Hermitian witness `W` is the
Choi matrix of a unique dimension-changing superoperator.

## The witness condition as the `n`-positivity criterion

The rectangular Schmidt-rank Choi criterion phrases `n`-positivity of `T` as
nonnegativity of the Choi quadratic form
`⟨ψ| τ |ψ⟩ = star ψ ⬝ᵥ (τ *ᵥ ψ)` over vectors ψ of Schmidt rank at most `n`.  For `τ = W`
this quadratic form equals the witness expectation `Re tr(W |ψ⟩⟨ψ|)` (a real number, `W`
being Hermitian), which the witness condition makes nonnegative.  So the superoperator
whose Choi matrix is the witness is `n`-positive.

## Detection through the trace-pairing adjoint

The entanglement witness has negative expectation `Re tr(W ρ)` on ρ. Writing `W = τ_P`
and pushing `P` across the trace pairing of the ampliation onto its trace-pairing adjoint
`P*` (`Matrix.trace_traceAdjointMap_mul`) turns this expectation into the Choi-vector
quadratic form of the ampliation of `P*`:

  `tr(W ρ) = ⟨Ω| (P* ⊗ id)(ρ) |Ω⟩`.

The trace-pairing adjoint of an `n`-positive map is again `n`-positive
(`IsNPositiveMap.traceAdjointMap`), so `P*` is the `n`-positive map detecting ρ: the
negative real part of `tr(W ρ)` forces `⟨Ω| (P* ⊗ id)(ρ) |Ω⟩` to have negative real part,
which a positive semidefinite matrix cannot, so `(P* ⊗ id)(ρ)` is not positive
semidefinite.

## Main results

* `ChoiJamiolkowski.exists_choiMatrix_eq`: **the Choi map is surjective** — every bipartite
  matrix is the Choi matrix of a superoperator.
* `ChoiJamiolkowski.exists_isNPositiveMap_choiMatrix_eq_of_witness`: **a Schmidt-`n` witness
  is the Choi matrix of an `n`-positive map**, the Choi–Jamiołkowski translation of the
  entanglement witness into an `n`-positive map.
* `ChoiJamiolkowski.trace_choiMatrix_mul_eq_omegaVec_quadraticForm_traceAdjointMap`: the
  trace pairing of the Choi matrix with ρ equals the Choi-vector quadratic form of the
  trace-pairing-adjoint ampliation.
* `Matrix.exists_isNPositiveMap_tensorMapId_not_posSemidef`: **Wolf Proposition 3.4 (if
  direction)** — a trace-one Hermitian state on `ℂ^d ⊗ ℂ^{d'}` of Schmidt number larger
  than `n` is detected by an `n`-positive map `M_d(ℂ) → M_{d'}(ℂ)`.
* `Matrix.hasSchmidtNumberLE_iff_forall_isNPositiveMap_tensorMapId_posSemidef`:
  **Wolf Proposition 3.4** — the rectangular source equivalence, combining the detector
  with the general forward theorem.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Section 3.2, Proposition 3.4, lines 250--267, especially Equations (3.13)--(3.14)]
  [Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder
open Matrix

namespace ChoiJamiolkowski

variable {D d d' : ℕ}

/-! ## Surjectivity of the Choi map -/

/-- **The Choi map is surjective.**  Every bipartite matrix `W` on `M_{D·D}(ℂ)` is the
Choi matrix `(T ⊗ id)(|Ω⟩⟨Ω|)` of some superoperator `T : M_D(ℂ) → M_D(ℂ)`.

This square compatibility theorem now delegates to the explicit inverse
`ChoiRectangular.mapOfChoiMatrix`, rather than recovering surjectivity indirectly from
finite-dimensional dimension counting. -/
theorem exists_choiMatrix_eq [NeZero D]
    (W : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    ∃ T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ, choiMatrix T = W := by
  refine ⟨ChoiRectangular.mapOfChoiMatrix W, ?_⟩
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    ChoiRectangular.choiMatrix_mapOfChoiMatrix W

/-! ## The witness as the Choi matrix of an `n`-positive map -/

/-- The witness expectation on a pure-state projector equals the Choi quadratic form: for
any matrix `W` and any vector ψ,

  `tr(W |ψ⟩⟨ψ|) = star ψ ⬝ᵥ (W *ᵥ ψ)`.

This is the algebraic identity matching the entanglement-witness condition to the Choi
`n`-positivity criterion. -/
theorem trace_mul_vecMulVec_eq_dotProduct
    {ι : Type*} [Fintype ι]
    (W : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    (W * Matrix.vecMulVec ψ (star ψ)).trace = star ψ ⬝ᵥ (W *ᵥ ψ) := by
  classical
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- **A Schmidt-`n` entanglement witness is the rectangular Choi matrix of an
`n`-positive map.** A Hermitian operator `W` on `ℂ^d ⊗ ℂ^{d'}` whose expectation
on every pure state of Schmidt rank at most `n` is nonnegative is the Choi matrix
of an `n`-positive map `P : M_{d'}(ℂ) → M_d(ℂ)`.

This is the Choi–Jamiołkowski translation of the entanglement-witness criterion (Wolf
Proposition 3.3) into the map `P = T*` of Wolf Proposition 3.4, Equation (3.13).
The inverse Choi assignment `ChoiRectangular.mapOfChoiMatrix` gives `P` with
`ChoiRectangular.choiMatrix P = W`; the witness condition
`0 ≤ Re tr(W |ψ⟩⟨ψ|)`, which on the Hermitian `W` is the full
(real, nonnegative) Choi quadratic form `0 ≤ star ψ ⬝ᵥ (W *ᵥ ψ)`, is exactly the
`n`-positivity criterion for `P`. -/
theorem exists_isNPositiveMap_choiMatrix_eq_of_witness [NeZero d'] {n : ℕ}
    {W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hWherm : W.IsHermitian)
    (hWpos : ∀ ψ : Fin d × Fin d' → ℂ, Matrix.HasSchmidtRankLE n ψ →
      0 ≤ (W * Matrix.vecMulVec ψ (star ψ)).trace.re) :
    ∃ P : Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ,
      IsNPositiveMap n P ∧ ChoiRectangular.choiMatrix P = W := by
  let P := ChoiRectangular.mapOfChoiMatrix W
  refine ⟨P, ?_, ChoiRectangular.choiMatrix_mapOfChoiMatrix W⟩
  rw [isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg_rectangular]
  intro ψ hψ
  -- The Choi quadratic form for ψ is the witness expectation, a nonnegative real.
  rw [show ChoiRectangular.choiMatrix P = W from
    ChoiRectangular.choiMatrix_mapOfChoiMatrix W]
  have hreal : (W * Matrix.vecMulVec ψ (star ψ)).trace = star ψ ⬝ᵥ (W *ᵥ ψ) :=
    trace_mul_vecMulVec_eq_dotProduct W ψ
  -- `star ψ ⬝ᵥ (W *ᵥ ψ)` is real (W Hermitian) with nonnegative real part.
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · rw [← hreal]; exact hWpos ψ hψ
  · -- The imaginary part vanishes since `W` is Hermitian.
    have him := hWherm.im_star_dotProduct_mulVec_self ψ
    simp only [RCLike.im_to_complex] at him
    rw [him]

/-! ## Detection through the trace-pairing adjoint -/

/-- The trace pairing of the rectangular Choi matrix of
`P : M_{d'}(ℂ) → M_d(ℂ)` with `ρ` on `ℂ^d ⊗ ℂ^{d'}` is the quadratic form of
the trace-pairing-adjoint ampliation on the maximally entangled vector of the
`d'`-dimensional factor:

  `tr(τ_P ρ) = ⟨Ω| (P* ⊗ id)(ρ) |Ω⟩`.

Here `P*` is the trace-pairing adjoint (`Matrix.traceAdjointMap`). The identity moves `P`
across the trace pairing of its `id_{d'}`-ampliation (`Matrix.trace_traceAdjointMap_mul`,
together with `nPositiveAmpliation_traceAdjointMap`) and reads the result as the quadratic
form of `(P* ⊗ id_{d'})(ρ)` on `Ω_{d'}`. This is Wolf, Chapter 3,
Equation (3.14), lines 262--265, with the factor order of Equation (3.13). -/
theorem trace_choiMatrix_mul_eq_omegaVec_quadraticForm_traceAdjointMap
    (P : Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    (ChoiRectangular.choiMatrix P * ρ).trace =
      star (omegaVec d') ⬝ᵥ
        (tensorMapId (Matrix.traceAdjointMap P) ρ *ᵥ omegaVec d') := by
  -- `tr(τ_P ρ) = tr(ρ (P ⊗ id)(|Ω⟩⟨Ω|))`.
  have h1 : (ChoiRectangular.choiMatrix P * ρ).trace =
      (ρ * tensorMapId P (omegaProj d')).trace := by
    rw [ChoiRectangular.choiMatrix, Matrix.trace_mul_comm]
  -- Move `P` onto its trace-pairing adjoint across the ampliation trace pairing.
  have h2 : (ρ * tensorMapId P (omegaProj d')).trace =
      (tensorMapId (Matrix.traceAdjointMap P) ρ * omegaProj d').trace := by
    rw [tensorMapId_eq_nPositiveAmpliation P (omegaProj d'),
      show tensorMapId (Matrix.traceAdjointMap P) ρ =
          nPositiveAmpliation d' (Matrix.traceAdjointMap P) ρ from
        tensorMapId_eq_nPositiveAmpliation _ _,
      nPositiveAmpliation_traceAdjointMap,
      Matrix.trace_traceAdjointMap_mul (nPositiveAmpliation d' P) ρ (omegaProj d'),
      Matrix.trace_mul_comm]
  -- `tr(Y |Ω⟩⟨Ω|) = ⟨Ω| Y |Ω⟩`.
  rw [h1, h2, omegaProj, trace_mul_vecMulVec_eq_dotProduct]

end ChoiJamiolkowski

namespace Matrix

open ChoiJamiolkowski

/-- **Positive maps detect high Schmidt number** (Wolf §3.2, Proposition 3.4,
lines 250--267, if direction). A trace-one Hermitian bipartite state `ρ` on
`ℂ^d ⊗ ℂ^{d'}` of Schmidt number larger than `n` is detected by an `n`-positive
map `T : M_d(ℂ) → M_{d'}(ℂ)`: `(T ⊗ id_{d'})(ρ)` is not positive semidefinite.

The entanglement witness `W` of Wolf Proposition 3.3 (`Matrix.exists_isHermitian_witness`)
is the Choi matrix of an `n`-positive map `P` (`exists_isNPositiveMap_choiMatrix_eq_of_witness`).
Its trace-pairing adjoint `T = P*` is again `n`-positive (`IsNPositiveMap.traceAdjointMap`),
and the trace identity
`trace_choiMatrix_mul_eq_omegaVec_quadraticForm_traceAdjointMap` turns the negative witness
expectation `Re tr(W ρ) < 0` into a negative real part of `⟨Ω| (T ⊗ id)(ρ) |Ω⟩`.  A
positive semidefinite matrix has nonnegative quadratic forms, so `(T ⊗ id)(ρ)` is not
positive semidefinite. -/
theorem exists_isNPositiveMap_tensorMapId_not_posSemidef [NeZero d'] (n : ℕ)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρH : ρ.IsHermitian) (hρtr : ρ.trace = 1) (hρ : ¬ HasSchmidtNumberLE n ρ) :
    ∃ T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ,
      IsNPositiveMap n T ∧ ¬ (tensorMapId T ρ).PosSemidef := by
  -- The entanglement witness for ρ.
  obtain ⟨W, hWherm, hWρ, hWpos⟩ := exists_isHermitian_witness n hρH hρtr hρ
  -- `W` is the Choi matrix of an `n`-positive map `P`.
  obtain ⟨P, hPpos, hPchoi⟩ :=
    exists_isNPositiveMap_choiMatrix_eq_of_witness hWherm hWpos
  -- Its trace-pairing adjoint is the detecting `n`-positive map.
  refine ⟨Matrix.traceAdjointMap P, hPpos.traceAdjointMap, ?_⟩
  intro hPSD
  -- A positive semidefinite matrix has a nonnegative Choi-vector quadratic form.
  have hquad : 0 ≤ star (omegaVec d') ⬝ᵥ
      (tensorMapId (Matrix.traceAdjointMap P) ρ *ᵥ omegaVec d') :=
    hPSD.dotProduct_mulVec_nonneg (omegaVec d')
  -- But that quadratic form is `tr(W ρ)`, whose real part is negative.
  have hid := trace_choiMatrix_mul_eq_omegaVec_quadraticForm_traceAdjointMap P ρ
  rw [hPchoi] at hid
  rw [← hid] at hquad
  exact absurd ((Complex.nonneg_iff.mp hquad).1) (not_le.mpr hWρ)

/-- **Wolf's rectangular positive-map characterization of Schmidt number**
(Chapter 3, Proposition 3.4, lines 250--267). A density operator `ρ` on
`ℂ^d ⊗ ℂ^{d'}` has Schmidt number at most `n` if and only if every `n`-positive
map `T : M_d(ℂ) → M_{d'}(ℂ)` keeps `(T ⊗ id_{d'})(ρ)` positive semidefinite.

The forward implication is `HasSchmidtNumberLE.tensorMapId_posSemidef`. For the
converse, Equations (3.13)--(3.14) turn the entanglement witness for `ρ` into the
Choi matrix of `P : M_{d'} → M_d`, and `T = P*` detects `ρ` on `omegaVec d'`. -/
theorem hasSchmidtNumberLE_iff_forall_isNPositiveMap_tensorMapId_posSemidef
    [NeZero d] [NeZero d'] (n : ℕ)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) :
    HasSchmidtNumberLE n ρ ↔
      ∀ T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ,
        IsNPositiveMap n T → (tensorMapId T ρ).PosSemidef := by
  constructor
  · intro hsn T hT
    exact hsn.tensorMapId_posSemidef hT
  · intro hT
    by_contra hsn
    obtain ⟨T, hTpos, hTdetects⟩ :=
      exists_isNPositiveMap_tensorMapId_not_posSemidef n hρ.isHermitian hρtr hsn
    exact hTdetects (hT T hTpos)

end Matrix
