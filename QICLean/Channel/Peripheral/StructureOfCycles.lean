/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixReindexUnitary
import QICLean.Channel.Determinant.PositiveInverse
import QICLean.Channel.Peripheral.DensityBlockSchwarz

/-!
# Structure of cycles (Wolf Theorem 6.16)

This file assembles the source-facing density-block statement and dynamics in
Wolf Theorem 6.16, Equations (6.66)--(6.68).  The direct Schwarz hypothesis on
the map and the Schwarz hypothesis on its trace adjoint remain separate.

The formal density-block coordinates use the tensor order `sigma k ⊗ₖ X k`.
Wolf prints `x k ⊗ rho k`; the two conventions differ only by the canonical
interchange of the tensor factors.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines
1597--1664.
-/

open scoped Matrix MatrixOrder ComplexOrder Kronecker

noncomputable section

namespace Matrix

/-- The matched full-matrix maps in Wolf Theorem 6.16 are unitary
conjugations, expressed with Wolf's output-to-input permutation.

The face permutation `F.blockEquiv` sends an input block to its output block.
Thus Wolf's permutation is `pi := F.blockEquiv.symm`.  The unitary returned by
the positive-invertible Schwarz classification acts first on the input-indexed
copy of the matrix algebra; simultaneous reindexing along `d (pi k) = d k`
makes it an output-indexed unitary `V k`.

Source: Wolf Theorem 6.16, proof lines 1637--1663. -/
theorem DirectSumFacePermutation.exists_reindexedUnitaryBlockAction
    {K : ℕ} {d : Fin K → ℕ}
    {Tbar Sbar : Module.End ℂ
      (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)}
    (F : DirectSumFacePermutation Tbar Sbar)
    (hd : ∀ k, 0 < d k)
    (hSchwarz : ∀ i, IsSchwarzMap (F.matchedBlockEndomorphism i)) :
    let pi := F.blockEquiv.symm
    ∃ (hdpi : ∀ k, d (pi k) = d k)
      (V : ∀ k, Matrix.unitaryGroup (Fin (d k)) ℂ),
      ∀ X k,
        Tbar X k =
          (V k : Matrix (Fin (d k)) (Fin (d k)) ℂ) *
            Matrix.reindex (finCongr (hdpi k)) (finCongr (hdpi k))
              (X (pi k)) *
            (V k : Matrix (Fin (d k)) (Fin (d k)) ℂ)ᴴ := by
  classical
  dsimp only
  let : ∀ k, NeZero (d k) := fun k ↦ ⟨Nat.ne_of_gt (hd k)⟩
  have hdpi : ∀ k, d (F.blockEquiv.symm k) = d k := fun k ↦ by
    simpa only [Equiv.apply_symm_apply] using
      F.dimension_eq (F.blockEquiv.symm k)
  have hUnitary : ∀ i, ∃ W : Matrix.unitaryGroup (Fin (d i)) ℂ,
      F.matchedBlockEndomorphism i =
        unitaryChannel W := by
    intro i
    let hBij := F.matchedBlockEndomorphism_bijective i
    exact ChannelDeterminant.Internal.wolfPositiveInvertibleSchwarzMaps hBij
      (F.matchedBlockEndomorphism_isPositiveMap i)
      (F.matchedBlockEndomorphism_isTracePreservingMap i)
      (F.matchedBlockCanonicalInverse_isPositiveMap i hBij) (hSchwarz i)
  choose W hW using hUnitary
  let V : ∀ k, Matrix.unitaryGroup (Fin (d k)) ℂ := fun k ↦
    ⟨Matrix.reindex (finCongr (hdpi k)) (finCongr (hdpi k))
        (W (F.blockEquiv.symm k) :
          Matrix (Fin (d (F.blockEquiv.symm k)))
            (Fin (d (F.blockEquiv.symm k))) ℂ),
      Matrix.reindex_mem_unitaryGroup (finCongr (hdpi k)) _
        (W (F.blockEquiv.symm k)).property⟩
  refine ⟨hdpi, V, ?_⟩
  have hActionAtSource
      (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) (i : Fin K) :
      Tbar X (F.blockEquiv i) =
        (V (F.blockEquiv i) :
          Matrix (Fin (d (F.blockEquiv i)))
            (Fin (d (F.blockEquiv i))) ℂ) *
          Matrix.reindex (finCongr (hdpi (F.blockEquiv i)))
            (finCongr (hdpi (F.blockEquiv i)))
            (X (F.blockEquiv.symm (F.blockEquiv i))) *
          (V (F.blockEquiv i) :
            Matrix (Fin (d (F.blockEquiv i)))
              (Fin (d (F.blockEquiv i))) ℂ)ᴴ := by
    have hMatched :
        F.matchedBlockEndomorphism i (X i) =
          (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * X i *
            (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ := by
      simpa only [unitaryChannel, LinearMap.coe_mk, AddHom.coe_mk] using
        LinearMap.congr_fun (hW i) (X i)
    have hRawAtEquiv :
        Matrix.directSumBlockMap Tbar i (F.blockEquiv i) (X i) =
          Matrix.reindex (finCongr (F.dimension_eq i))
            (finCongr (F.dimension_eq i))
            ((W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * X i *
              (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ) := by
      let R := Matrix.reindexAlgEquiv ℂ ℂ (finCongr (F.dimension_eq i))
      apply R.symm.injective
      change R.symm (Matrix.directSumBlockMap Tbar i (F.blockEquiv i) (X i)) =
        R.symm (R ((W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * X i *
          (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ))
      rw [R.symm_apply_apply]
      simpa only [R, F.matchedBlockEndomorphism_apply,
        Matrix.symm_reindexAlgEquiv, Matrix.coe_reindexAlgEquiv] using hMatched
    rw [F.map_apply_blockEquiv, hRawAtEquiv]
    dsimp only [V]
    suffices ∀ (s : Fin K), s = i →
        ∀ hsi : d s = d (F.blockEquiv i),
          Matrix.reindex (finCongr (F.dimension_eq i))
              (finCongr (F.dimension_eq i))
              ((W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * X i *
                (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ) =
            Matrix.reindex (finCongr hsi) (finCongr hsi)
                (W s : Matrix (Fin (d s)) (Fin (d s)) ℂ) *
              Matrix.reindex (finCongr hsi) (finCongr hsi) (X s) *
              (Matrix.reindex (finCongr hsi) (finCongr hsi)
                (W s : Matrix (Fin (d s)) (Fin (d s)) ℂ))ᴴ by
      exact this (F.blockEquiv.symm (F.blockEquiv i))
        (F.blockEquiv.symm_apply_apply i) (hdpi (F.blockEquiv i))
    intro s hs hsi
    subst s
    have hhsi : hsi = F.dimension_eq i := Subsingleton.elim _ _
    cases hhsi
    rw [Matrix.conjTranspose_reindex]
    let R := Matrix.reindexAlgEquiv ℂ ℂ (finCongr (F.dimension_eq i))
    change R ((W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * X i *
        (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ) =
      R (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ) * R (X i) *
        R (W i : Matrix (Fin (d i)) (Fin (d i)) ℂ)ᴴ
    rw [map_mul, map_mul]
  intro X k
  obtain ⟨i, rfl⟩ := F.blockEquiv.surjective k
  exact hActionAtSource X i

end Matrix

namespace IsPositiveMap

/-- **Wolf Theorem 6.16, Equations (6.66)--(6.68).**

Let `T` be a positive trace-preserving map satisfying the Schwarz inequality,
and suppose separately that its trace adjoint is Schwarz as required by Wolf
Theorem 6.14.  Its asymptotic image has the zero-extended density-block form
of Equations (6.66)--(6.67).  The zero summand has dimension zero, every
density factor is maximally mixed, and the coordinate action permutes equal
`d`- and `m`-dimensional blocks and conjugates by output-indexed unitaries.
The final equality is the ambient form of Equation (6.68).

The formal coordinates retain `sigma k ⊗ₖ X k`, whereas Wolf prints
`x k ⊗ rho k`; these are related by the canonical tensor-factor swap.  The
explicit `e₀` and `Matrix.fromBlocks 0 0 0` are deliberately retained even
though `n = D`, avoiding a dependent rewrite of the zero summand.

Source: `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines
1597--1664, Equations (6.66)--(6.68). -/
theorem exists_wolfTheorem616
    {D : ℕ} [NeZero D]
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap T)
    (hAdjointSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) :
    ∃ (n K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
      (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
      (pi : Fin K ≃ Fin K)
      (hdpi : ∀ k, d (pi k) = d k)
      (V : ∀ k, Matrix.unitaryGroup (Fin (d k)) ℂ)
      (A : Module.End ℂ (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ)),
      (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (sigma k).PosDef) ∧ (∀ k, (sigma k).trace = 1) ∧
        (∀ B, B ∈ T.peripheralSubspace ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e₀ e₀
              (Matrix.fromBlocks 0 0 0
                (Matrix.reindex e e
                  (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k)))) ∧
        n = D ∧
        (∀ k, sigma k = (m k : ℂ)⁻¹ • 1) ∧
        (∀ k, m (pi k) = m k) ∧
        (∀ X k,
          A X k =
            (V k : Matrix (Fin (d k)) (Fin (d k)) ℂ) *
              Matrix.reindex (finCongr (hdpi k)) (finCongr (hdpi k))
                (X (pi k)) *
              (V k : Matrix (Fin (d k)) (Fin (d k)) ℂ)ᴴ) ∧
        ∀ X,
          T (Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma X) =
            Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma (A X) := by
  classical
  obtain ⟨n, K, d, m, e, e₀, U, sigma, hU, S, hd, hm, hsigmaPosDef,
      hsigmaTrace, hfixed, hSPos, hSTP, hDynamics⟩ :=
    hPos.exists_peripheralDensityBlockSchwarz hTP hSchwarz hAdjointSchwarz
  dsimp only at hDynamics
  rcases hDynamics with
    ⟨hTencode, hSencode, hST, hTS, hTPos, hSbarPos, hTTP, hSTPbar,
      F, hMap, hInverseMap, hDimension, hn, hsigma, hmMatch, hBlockOne,
      hRawSchwarz, hMatchedSchwarz⟩
  obtain ⟨hdpi, V, hAction⟩ :=
    F.exists_reindexedUnitaryBlockAction hd hMatchedSchwarz
  let pi : Fin K ≃ Fin K := F.blockEquiv.symm
  let A := Matrix.densityBlockDynamics e e₀ U hU sigma T
  have hmpi : ∀ k, m (pi k) = m k := fun k ↦ by
    simpa only [pi, Equiv.apply_symm_apply] using
      hmMatch (F.blockEquiv.symm k)
  have hperipheral : ∀ B, B ∈ T.peripheralSubspace ↔
      ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        star U * B * U = Matrix.reindex e₀ e₀
          (Matrix.fromBlocks 0 0 0
            (Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))) := fun B ↦
    (Module.End.peripheralProjection_apply_eq_self_iff T B).symm.trans
      (hfixed B)
  refine ⟨n, K, d, m, e, e₀, U, sigma, hU, pi, hdpi, V, A,
    hd, hm, hsigmaPosDef, hsigmaTrace, hperipheral, hn, hsigma, hmpi, ?_, ?_⟩
  · simpa only [A, pi] using hAction
  · intro X
    simpa only [A] using (hTencode X).symm

end IsPositiveMap
