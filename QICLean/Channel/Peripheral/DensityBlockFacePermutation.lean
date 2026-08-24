/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.DensityBlockDynamics
import QICLean.Channel.Peripheral.DirectSumFacePermutation

/-!
# Wolf's permutation of density-block pure-state faces

This file assembles the density-block coordinates of Wolf Theorem 6.14, the
positive trace-preserving recurrent inverse on the asymptotic image, and Wolf's
extreme-state/continuity argument from the proof of Theorem 6.16.  It covers
exactly the source step at
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1641--1659.

The formal coordinates use `sigma k ⊗ X k`, the tensor-factor order fixed by
`IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero`.  The resulting
equivalence sends a source block to its target block.  Its inverse is Wolf's
output-to-input permutation `pi` in the displayed formula at lines 1656--1659.

This is an intentionally partial boundary of Theorem 6.16.  It proves equality
only of the full-matrix dimensions `d`, not of the multiplicity dimensions `m`.
Transport of the ordinary Schwarz inequality to the matched block maps,
comparison of multiplicities, exclusion of the transpose alternative in the
assembled density-block coordinates, and Equation (6.68) are handled by the
subsequent source-facing modules.  No CP/Kraus or ring-ideal classification is
used here.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators Kronecker

noncomputable section

namespace Matrix

variable {iota kappa : Type*}
variable [Finite iota] [DecidableEq iota]
variable [Finite kappa] [DecidableEq kappa]
variable {d : iota → ℕ} {e : kappa → ℕ}
variable [∀ i, NeZero (d i)] [∀ j, NeZero (e j)]

omit [∀ i, NeZero (d i)] [∀ j, NeZero (e j)] in
/-- The full-family form of the forward block action.  At output block `j`,
the input is read from `F.blockEquiv.symm j`, which is Wolf's permutation `pi`. -/
theorem DirectSumFacePermutation.map_apply
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S)
    (X : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) (j : kappa) :
    T X j = directSumBlockMap T (F.blockEquiv.symm j) j
      (X (F.blockEquiv.symm j)) := by
  classical
  let := Fintype.ofFinite iota
  let := Fintype.ofFinite kappa
  calc
    T X j = T (∑ i, Pi.single i (X i)) j := by
      rw [Finset.univ_sum_single]
    _ = (∑ i, T (Pi.single i (X i))) j := by rw [map_sum]
    _ = ∑ i, T (Pi.single i (X i)) j := by rw [Finset.sum_apply]
    _ = ∑ i, (Pi.single (F.blockEquiv i)
        (directSumBlockMap T i (F.blockEquiv i) (X i)) :
          ∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [F.map_single]
    _ = directSumBlockMap T (F.blockEquiv.symm j) j
        (X (F.blockEquiv.symm j)) := by
      rw [Finset.sum_eq_single (F.blockEquiv.symm j)]
      · rw [F.blockEquiv.apply_symm_apply, Pi.single_eq_same]
      · intro i _ hi
        rw [Pi.single_eq_of_ne]
        intro hji
        apply hi
        apply F.blockEquiv.injective
        rw [Equiv.apply_symm_apply]
        exact hji.symm
      · simp

omit [∀ i, NeZero (d i)] [∀ j, NeZero (e j)] in
/-- The source-indexed form of the full-family block action.  Evaluating at
the target `F.blockEquiv i` reads the input block `i` without transporting a
dependent matrix through `F.blockEquiv.symm_apply_apply`.

This is equivalent to `DirectSumFacePermutation.map_apply`, but is the more
stable interface when the matrix sizes depend on the block index. -/
theorem DirectSumFacePermutation.map_apply_blockEquiv
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S)
    (X : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) (i : iota) :
    T X (F.blockEquiv i) =
      directSumBlockMap T i (F.blockEquiv i) (X i) := by
  classical
  let := Fintype.ofFinite iota
  let := Fintype.ofFinite kappa
  calc
    T X (F.blockEquiv i) = T (∑ r, Pi.single r (X r)) (F.blockEquiv i) := by
      rw [Finset.univ_sum_single]
    _ = (∑ r, T (Pi.single r (X r))) (F.blockEquiv i) := by
      rw [map_sum]
    _ = ∑ r, T (Pi.single r (X r)) (F.blockEquiv i) := by
      rw [Finset.sum_apply]
    _ = ∑ r, (Pi.single (F.blockEquiv r)
        (directSumBlockMap T r (F.blockEquiv r) (X r)) :
          ∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) (F.blockEquiv i) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [F.map_single]
    _ = directSumBlockMap T i (F.blockEquiv i) (X i) := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]
      · intro r _ hri
        rw [Pi.single_eq_of_ne]
        exact fun h ↦ hri (F.blockEquiv.injective h.symm)
      · simp

omit [∀ i, NeZero (d i)] [∀ j, NeZero (e j)] in
/-- The full-family form of the inverse block action. -/
theorem DirectSumFacePermutation.inverse_apply
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (F : DirectSumFacePermutation T S)
    (Y : ∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) (i : iota) :
    S Y i = directSumBlockMap S (F.blockEquiv i) i (Y (F.blockEquiv i)) := by
  classical
  let := Fintype.ofFinite iota
  let := Fintype.ofFinite kappa
  calc
    S Y i = S (∑ j, Pi.single j (Y j)) i := by
      rw [Finset.univ_sum_single]
    _ = (∑ j, S (Pi.single j (Y j))) i := by rw [map_sum]
    _ = ∑ j, S (Pi.single j (Y j)) i := by rw [Finset.sum_apply]
    _ = ∑ j, (Pi.single (F.blockEquiv.symm j)
        (directSumBlockMap S j (F.blockEquiv.symm j) (Y j)) :
          ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [F.inverse_map_single]
    _ = directSumBlockMap S (F.blockEquiv i) i (Y (F.blockEquiv i)) := by
      rw [Finset.sum_eq_single (F.blockEquiv i)]
      · rw [F.blockEquiv.symm_apply_apply, Pi.single_eq_same]
      · intro j _ hj
        rw [Pi.single_eq_of_ne]
        intro hij
        apply hj
        apply F.blockEquiv.symm.injective
        rw [Equiv.symm_apply_apply]
        exact hij.symm
      · simp

end Matrix

open Matrix

namespace IsPositiveMap

/-- **Wolf Theorem 6.16, permutation of density-block pure-state faces.**

Under the trace-adjoint Schwarz hypothesis needed to apply Wolf Theorem 6.14
to the recurrent projection, the asymptotic-image coordinates carry mutually
inverse positive trace-preserving maps `Tbar` and `Sbar`.  Their relative pure
states determine a source-to-target block equivalence.  If `tau` denotes that
equivalence, then `tau.symm` is Wolf's output-to-input permutation `pi`:
the output block `j` depends only on the input block `pi j`.

The returned `DirectSumFacePermutation` exposes the matched block maps, their
single-block and full-family actions, positivity, ordinary trace preservation,
two-sided inverse identities, and `d i = d (tau i)`.  No equality involving
the multiplicities `m` is asserted.  The ordinary Schwarz transport and the
later unitary/transpose classification are deliberately outside this theorem. -/
theorem exists_peripheralDensityBlockFacePermutation
    {D : ℕ} [NeZero D]
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hAdjointSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) :
    ∃ (n K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
      (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
      (S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
      (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (sigma k).PosDef) ∧ (∀ k, (sigma k).trace = 1) ∧
        (∀ B, T.peripheralProjection B = B ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e₀ e₀
              (Matrix.fromBlocks 0 0 0
                (Matrix.reindex e e
                  (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k)))) ∧
        IsPositiveMap S ∧ IsTracePreservingMap S ∧
        (let Tbar := Matrix.densityBlockDynamics e e₀ U hU sigma T
         let Sbar := Matrix.densityBlockDynamics e e₀ U hU sigma S
         (∀ X, Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma (Tbar X) =
            T (Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma X)) ∧
         (∀ X, Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma (Sbar X) =
            S (Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma X)) ∧
         Sbar.comp Tbar = LinearMap.id ∧
         Tbar.comp Sbar = LinearMap.id ∧
         Matrix.IsPositiveDirectSumMap Tbar ∧
         Matrix.IsPositiveDirectSumMap Sbar ∧
         Matrix.IsTracePreservingBetweenDirectSums Tbar ∧
         Matrix.IsTracePreservingBetweenDirectSums Sbar ∧
         ∃ F : Matrix.DirectSumFacePermutation Tbar Sbar,
           let pi := F.blockEquiv.symm
           (∀ X j, Tbar X j = Matrix.directSumBlockMap Tbar (pi j) j (X (pi j))) ∧
           (∀ Y i, Sbar Y i =
             Matrix.directSumBlockMap Sbar (pi.symm i) i (Y (pi.symm i))) ∧
           ∀ j, d (pi j) = d j) := by
  obtain ⟨n, K, d, m, e, e₀, U, sigma, hU, S, hd, hm, hsigma,
      hsigmaTrace, hfixed, hSPos, hSTP, hDynamics⟩ :=
    hPos.exists_peripheralDensityBlockDynamics hTP hAdjointSchwarz
  dsimp only at hDynamics
  rcases hDynamics with
    ⟨hTencode, hSencode, hST, hTS, hTPos, hSbarPos, hTTP, hSTPbar⟩
  let Tbar := Matrix.densityBlockDynamics e e₀ U hU sigma T
  let Sbar := Matrix.densityBlockDynamics e e₀ U hU sigma S
  let : ∀ k, NeZero (d k) := fun k ↦ ⟨Nat.ne_of_gt (hd k)⟩
  have hTBetween : Matrix.IsPositiveBetweenDirectSums Tbar := by
    exact hTPos
  have hSBetween : Matrix.IsPositiveBetweenDirectSums Sbar := by
    exact hSbarPos
  obtain ⟨F⟩ := Matrix.exists_directSumFacePermutation_of_mutualInverse
    hTBetween hSBetween hTTP hSTPbar hST hTS
  have hDimension : ∀ j, d (F.blockEquiv.symm j) = d j := by
    intro j
    simpa only [Equiv.apply_symm_apply] using
      F.dimension_eq (F.blockEquiv.symm j)
  refine ⟨n, K, d, m, e, e₀, U, sigma, hU, S, hd, hm, hsigma,
    hsigmaTrace, hfixed, hSPos, hSTP, ?_⟩
  dsimp only
  refine ⟨hTencode, hSencode, hST, hTS, hTPos, hSbarPos,
    hTTP, hSTPbar, F, ?_⟩
  exact ⟨F.map_apply, F.inverse_apply, hDimension⟩

end IsPositiveMap
