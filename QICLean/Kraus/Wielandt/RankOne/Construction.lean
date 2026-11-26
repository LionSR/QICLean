/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fin.Tuple.Basic
import QICLean.Kraus.Word
import QICLean.Kraus.Wielandt.SpanGrowth.VectorToMatrixSpan
import QICLean.Spectral.Jordan.FittingRange
import QICLean.Kraus.WordSpan
import QICLean.Spectral.Eigenvalue.NonzeroTraceEigenvalue
import QICLean.Algebra.Matrix.MatrixMulRange
import QICLean.Kraus.Blocking
import QICLean.Kraus.Wielandt.RankOne.BoundedWord

/-!
# Rank-one construction for finite matrix families

This module contains the channel-generic row-spreading and rank-one construction
reductions used in the proof of Sanz, Pérez-García, Wolf, and Cirac,
arXiv:0909.5347, Lemma 2(b).

It also contains the following results.

* `Kraus.evalWord_pow_mem_wordSpan`: bounded word powers in a finite Kraus family.
* `Kraus.exists_nonzero_trace_word_of_wordSpan_eq_top`,
  `Kraus.exists_eigenvector_of_wordSpan_eq_top`: eigenvectors from a full exact word span.
* `Kraus.pow_single_mem_wordSpan`, `Kraus.exists_rankOne_mem_wordSpan_blockTensor`: full rank-one
  extraction for finite matrix families.
-/

open scoped Matrix

section Construction

namespace Kraus

variable {d D : ℕ}

/-- The pointwise transpose of a finite matrix family. -/
noncomputable abbrev transposeFamily
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun i ↦ (K i)ᵀ

/-- Full fixed-length word span is preserved by pointwise transposition. -/
theorem wordSpan_transposeFamily_eq_top_of_wordSpan_eq_top
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ}
    (h : wordSpan K N = ⊤) :
    wordSpan (transposeFamily K) N = ⊤ := by
  classical
  unfold wordSpan at h ⊢
  have hrange :
      Set.range (fun σ : Fin N → Fin d =>
        Kraus.evalWord (transposeFamily K) (List.ofFn σ)) =
        Set.range (fun σ : Fin N → Fin d =>
          (Kraus.evalWord K (List.ofFn σ))ᵀ) := by
    ext M
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨σ ∘ Fin.rev, ?_⟩
      have hrev : ((σ ∘ Fin.rev) ∘ Fin.rev) = σ := by
        funext i
        simpa only [Function.comp_apply] using congrArg σ (Fin.rev_rev i)
      simpa [transposeFamily, List.ofFn_reverse, hrev] using
        (evalWord_transpose K (List.ofFn (σ ∘ Fin.rev)))
    · rintro ⟨σ, rfl⟩
      refine ⟨σ ∘ Fin.rev, ?_⟩
      simpa [transposeFamily, List.ofFn_reverse] using
        (evalWord_transpose K (List.ofFn σ)).symm
  rw [hrange]
  let e : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    Matrix.transposeLinearEquiv (Fin D) (Fin D) ℂ ℂ
  have hmap :
      Submodule.map
          (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
          (Submodule.span ℂ
            (Set.range fun σ : Fin N → Fin d => Kraus.evalWord K (List.ofFn σ))) =
        Submodule.span ℂ
          (Set.range fun σ : Fin N → Fin d =>
            (Kraus.evalWord K (List.ofFn σ))ᵀ) := by
    rw [Submodule.map_span]
    have hrange' :
        (fun M : Matrix (Fin D) (Fin D) ℂ => Mᵀ) ''
            Set.range (fun σ : Fin N → Fin d => Kraus.evalWord K (List.ofFn σ)) =
          Set.range fun σ : Fin N → Fin d =>
            (Kraus.evalWord K (List.ofFn σ))ᵀ := by
      simpa [Function.comp_def] using
        (Set.range_comp (fun M : Matrix (Fin D) (Fin D) ℂ => Mᵀ)
          (fun σ : Fin N → Fin d => Kraus.evalWord K (List.ofFn σ))).symm
    simp [e, hrange']
  calc
    Submodule.span ℂ
        (Set.range fun σ : Fin N → Fin d =>
          (Kraus.evalWord K (List.ofFn σ))ᵀ) =
        Submodule.map
          (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
          (Submodule.span ℂ
            (Set.range fun σ : Fin N → Fin d => Kraus.evalWord K (List.ofFn σ))) := by
      symm
      exact hmap
    _ = Submodule.map
        (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) ⊤ := by
      rw [h]
    _ = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
      simp [Submodule.map_top, LinearEquiv.range (e := e)]

/-- Full cumulative word span is preserved by pointwise transposition. -/
theorem cumulativeSpan_transposeFamily_eq_top_of_cumulativeSpan_eq_top
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ}
    (h : cumulativeSpan K N = ⊤) :
    cumulativeSpan (transposeFamily K) N = ⊤ := by
  let e : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
    Matrix.transposeLinearEquiv (Fin D) (Fin D) ℂ ℂ
  have hmap :
      Submodule.map
          (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
          (cumulativeSpan K N) =
        cumulativeSpan (transposeFamily K) N := by
    unfold cumulativeSpan
    rw [Submodule.map_span]
    have hset :
        (fun M : Matrix (Fin D) (Fin D) ℂ => Mᵀ) ''
            {M | ∃ w : List (Fin d), w.length ≤ N ∧ M = Kraus.evalWord K w} =
          {M | ∃ w : List (Fin d), w.length ≤ N ∧
            M = Kraus.evalWord (transposeFamily K) w} := by
      ext M
      constructor
      · rintro ⟨M', ⟨w, hw, rfl⟩, hM⟩
        refine ⟨w.reverse, by simpa using hw, ?_⟩
        rw [← hM]
        simpa [transposeFamily] using evalWord_transpose K w
      · rintro ⟨w, hw, hM⟩
        refine ⟨Kraus.evalWord K w.reverse, ⟨w.reverse, by simpa using hw, rfl⟩, ?_⟩
        rw [hM]
        simpa [transposeFamily] using evalWord_transpose K w.reverse
    simp [e, hset]
  calc
    cumulativeSpan (transposeFamily K) N =
        Submodule.map
          (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
          (cumulativeSpan K N) := hmap.symm
    _ = Submodule.map
        (e : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) ⊤ := by
      rw [h]
    _ = (⊤ : Submodule ℂ (Matrix (Fin D) (Fin D) ℂ)) := by
      simp [Submodule.map_top, LinearEquiv.range (e := e)]

/-- The linear map `M ↦ ψ ᵥ* M` for a fixed row vector `ψ`. -/
noncomputable def vecMulLinearMap (ψ : Fin D → ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin D → ℂ) :=
  { toFun := fun M ↦ Matrix.vecMul ψ M
    map_add' := fun M N ↦ by
      simpa using Matrix.vecMul_add (A := M) (B := N) (x := ψ)
    map_smul' := fun c M ↦ by
      simpa using Matrix.vecMul_smul (v := ψ) (b := c) (M := M) }

/-- The span of row vectors obtained by right multiplication with words of length `n`. -/
noncomputable def rowSpreadSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) (n : ℕ) :
    Submodule ℂ (Fin D → ℂ) :=
  Submodule.span ℂ (Set.range fun σ : Fin n → Fin d =>
    Matrix.vecMul ψ (Kraus.evalWord K (List.ofFn σ)))

private theorem vecMul_evalWord_ofFn_eq_evalWord_transposeFamily_mulVec
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ)
    {n : ℕ} (σ : Fin n → Fin d) :
    Matrix.vecMul ψ (Kraus.evalWord K (List.ofFn σ)) =
      Kraus.evalWord (transposeFamily K) (List.ofFn (σ ∘ Fin.rev)) *ᵥ ψ := by
  calc
    Matrix.vecMul ψ (Kraus.evalWord K (List.ofFn σ)) =
        (Kraus.evalWord K (List.ofFn σ))ᵀ *ᵥ ψ := by
      simpa using Matrix.vecMul_transpose
        (A := (Kraus.evalWord K (List.ofFn σ))ᵀ) (x := ψ)
    _ = Kraus.evalWord (transposeFamily K) (List.ofFn σ).reverse *ᵥ ψ := by
      simp [evalWord_transpose]
    _ = Kraus.evalWord (transposeFamily K) (List.ofFn (σ ∘ Fin.rev)) *ᵥ ψ := by
      simp [List.ofFn_reverse]

/-- Row spreading is vector spreading for the pointwise-transposed family. -/
theorem rowSpreadSpan_eq_vectorSpreadSpan_transpose
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) (n : ℕ) :
    rowSpreadSpan K ψ n = vectorSpreadSpan (transposeFamily K) ψ n := by
  classical
  unfold rowSpreadSpan vectorSpreadSpan
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨σ, rfl⟩
    apply Submodule.subset_span
    refine ⟨σ ∘ Fin.rev, ?_⟩
    simpa using
      (vecMul_evalWord_ofFn_eq_evalWord_transposeFamily_mulVec
        (K := K) (ψ := ψ) (σ := σ)).symm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨σ, rfl⟩
    apply Submodule.subset_span
    refine ⟨σ ∘ Fin.rev, ?_⟩
    have h := vecMul_evalWord_ofFn_eq_evalWord_transposeFamily_mulVec
      (K := K) (ψ := ψ) (σ := σ ∘ Fin.rev)
    have hrev : ((σ ∘ Fin.rev) ∘ Fin.rev) = σ := by
      funext i
      simpa only [Function.comp_apply] using congrArg σ (Fin.rev_rev i)
    simpa [hrev] using h

/-- Mapping `wordSpan` along `M ↦ ψ ᵥ* M` yields `rowSpreadSpan`. -/
theorem map_wordSpan_eq_rowSpreadSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) (n : ℕ) :
    Submodule.map (vecMulLinearMap (D := D) ψ) (wordSpan K n) =
      rowSpreadSpan K ψ n := by
  classical
  unfold vecMulLinearMap wordSpan rowSpreadSpan
  rw [Submodule.map_span]
  have hrange :
      (Set.range fun σ : Fin n → Fin d =>
        Matrix.vecMul ψ (Kraus.evalWord K (List.ofFn σ))) =
        (fun M : Matrix (Fin D) (Fin D) ℂ => Matrix.vecMul ψ M) ''
          (Set.range fun σ : Fin n → Fin d => Kraus.evalWord K (List.ofFn σ)) := by
    simpa [Function.comp_def] using
      (Set.range_comp (fun M : Matrix (Fin D) (Fin D) ℂ => Matrix.vecMul ψ M)
        (fun σ : Fin n → Fin d => Kraus.evalWord K (List.ofFn σ)))
  simp [hrange]

/-- Full row spread realizes every standard basis row by a word-span matrix. -/
theorem exists_wordSpan_vecMul_eq_pi_single
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) {n : ℕ}
    (hRow : rowSpreadSpan K ψ n = ⊤) (j : Fin D) :
    ∃ M : Matrix (Fin D) (Fin D) ℂ,
      M ∈ wordSpan K n ∧ Matrix.vecMul ψ M = Pi.single j (1 : ℂ) := by
  classical
  have hmap :
      Submodule.map (vecMulLinearMap (D := D) ψ) (wordSpan K n) = ⊤ := by
    rw [map_wordSpan_eq_rowSpreadSpan K ψ n, hRow]
  have hj_mem :
      Pi.single j (1 : ℂ) ∈
        Submodule.map (vecMulLinearMap (D := D) ψ) (wordSpan K n) := by
    simp [hmap]
  rcases hj_mem with ⟨M, hM, hM_apply⟩
  exact ⟨M, hM, by simpa [vecMulLinearMap] using hM_apply⟩

/-- Cumulative spanning and a nonzero transpose eigenvector imply full row spread. -/
theorem rowSpreadSpan_eq_top_of_cumulativeSpan_eq_top_of_eigenvector_transpose
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (ψ : Fin D → ℂ) (hψ : ψ ≠ 0)
    (i₁ : Fin d) (ν : ℂ) (hν : ν ≠ 0)
    (heigψ : (K i₁)ᵀ *ᵥ ψ = ν • ψ)
    {N : ℕ} (hCum : cumulativeSpan K N = ⊤) :
    rowSpreadSpan K ψ (D - 1) = ⊤ := by
  have hCumT : cumulativeSpan (transposeFamily K) N = ⊤ :=
    cumulativeSpan_transposeFamily_eq_top_of_cumulativeSpan_eq_top K hCum
  have hcum : cumulativeVectorSpan (transposeFamily K) ψ (D - 1) = ⊤ :=
    eigenvector_spreading_of_cumulativeSpan_eq_top
      (transposeFamily K) ψ hψ hCumT
  have hvec : vectorSpreadSpan (transposeFamily K) ψ (D - 1) = ⊤ :=
    vectorSpreadSpan_eq_top_of_cumulativeVectorSpan_eq_top_of_eigenvector
      (transposeFamily K) ψ (D - 1) i₁ ν hν (by simpa [transposeFamily] using heigψ) hcum
  simpa [rowSpreadSpan_eq_vectorSpreadSpan_transpose K ψ (D - 1)] using hvec

/-- One rank-one word-span element and full row spread yield the rank-one basis. -/
theorem vecMulVec_pi_single_mem_wordSpan_of_rankOne
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (φ ψ : Fin D → ℂ) {m k : ℕ}
    (hRankOne : Matrix.vecMulVec φ ψ ∈ wordSpan K m)
    (hRow : rowSpreadSpan K ψ k = ⊤) :
    ∀ j : Fin D,
      Matrix.vecMulVec φ (Pi.single j (1 : ℂ)) ∈ wordSpan K (m + k) := by
  classical
  intro j
  obtain ⟨M, hM, hvec⟩ := exists_wordSpan_vecMul_eq_pi_single K ψ hRow j
  have hprod : Matrix.vecMulVec φ ψ * M ∈ wordSpan K (m + k) :=
    wordSpan_mul_le K m k (Submodule.mul_mem_mul hRankOne hM)
  simpa [Matrix.vecMulVec_mul, hvec] using hprod

/-- Vector spread, one rank-one element, and row spread imply full matrix span. -/
theorem wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOne
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (φ ψ : Fin D → ℂ) {n m k : ℕ}
    (hVec : vectorSpreadSpan K φ n = ⊤)
    (hRankOne : Matrix.vecMulVec φ ψ ∈ wordSpan K m)
    (hRow : rowSpreadSpan K ψ k = ⊤) :
    wordSpan K (n + (m + k)) = ⊤ := by
  have hRankOneBasis : ∀ j : Fin D,
      Matrix.vecMulVec φ (Pi.single j (1 : ℂ)) ∈ wordSpan K (m + k) :=
    vecMulVec_pi_single_mem_wordSpan_of_rankOne K φ ψ hRankOne hRow
  exact wordSpan_eq_top_of_vectorSpreadSpan_eq_top_of_rankOneBasis K φ hVec hRankOneBasis

end Kraus

end Construction

section Element

/-!
## Bounded word powers in a finite Kraus family

This file constructs a bounded-length word-span element whose range lies in the
sum of the generalized eigenspaces for nonzero eigenvalues. It gives only the
intermediate Fitting-projector-power step $A_1^r = A_1^r P$ in Sanz,
Pérez-García, Wolf, and Cirac, arXiv:0909.5347, Lemma 2(b), not the final
rank-one element $|\varphi\rangle\langle\psi|$.
-/

open Module

namespace Kraus

variable {d D : ℕ}

/-- A power of an evaluated word belongs to the word span at the multiplied length. -/
theorem evalWord_pow_mem_wordSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (w : List (Fin d)) (k : ℕ) :
    (Kraus.evalWord K w) ^ k ∈ wordSpan K (k * w.length) := by
  classical
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hw : Kraus.evalWord K w ∈ wordSpan K w.length :=
        evalWord_mem_wordSpan K w
      have hprod :
          (Kraus.evalWord K w) ^ k * Kraus.evalWord K w ∈
            wordSpan K (k * w.length + w.length) := by
        rw [wordSpan_add]
        exact Submodule.mul_mem_mul ih hw
      simpa [pow_succ, Nat.succ_mul] using hprod

end Kraus

end Element

namespace Kraus

section Extraction

/-!
## Eigenvectors from a full exact word span

A full exact word span contains a word with nonzero trace. The corresponding word matrix has a
nonzero eigenvalue and a nonzero eigenvector.
-/

variable {d D : ℕ}

/-- If `wordSpan K N = ⊤` and `[NeZero D]`, some word of length `N` has nonzero trace.

Paper: arXiv:0909.5347, Theorem 1 proof, first paragraph. -/
theorem exists_nonzero_trace_word_of_wordSpan_eq_top [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ} (htop : wordSpan K N = ⊤) :
    ∃ σ : Fin N → Fin d, (Kraus.evalWord K (List.ofFn σ)).trace ≠ 0 := by
  by_contra hall
  push Not at hall
  have hI : (1 : Matrix (Fin D) (Fin D) ℂ) ∈ wordSpan K N :=
    htop ▸ Submodule.mem_top
  let trMap : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] ℂ :=
    Matrix.traceLinearMap (Fin D) ℂ ℂ
  have hker : wordSpan K N ≤ LinearMap.ker trMap := by
    apply Submodule.span_le.mpr
    rintro M ⟨σ, rfl⟩
    exact LinearMap.mem_ker.mpr (hall σ)
  have htrI : (1 : Matrix (Fin D) (Fin D) ℂ).trace ≠ 0 := by
    simp only [Matrix.trace_one, Fintype.card_fin, ne_eq, Nat.cast_eq_zero]
    exact_mod_cast NeZero.ne D
  exact htrI (LinearMap.mem_ker.mp (hker hI))

/-- If `wordSpan K N = ⊤` and `[NeZero D]`, some word of length `N` has a nonzero eigenvalue
and a corresponding nonzero eigenvector.

Paper: arXiv:0909.5347, Theorem 1 proof, first paragraph. -/
theorem exists_eigenvector_of_wordSpan_eq_top [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ} (htop : wordSpan K N = ⊤) :
    ∃ (σ : Fin N → Fin d) (μ : ℂ) (φ : Fin D → ℂ),
      μ ≠ 0 ∧ φ ≠ 0 ∧
      Kraus.evalWord K (List.ofFn σ) *ᵥ φ = μ • φ := by
  obtain ⟨σ, hσ⟩ := exists_nonzero_trace_word_of_wordSpan_eq_top K htop
  obtain ⟨μ, φ, hμ, hφ, heig⟩ := exists_eigenvector_of_trace_ne_zero _ hσ
  exact ⟨σ, μ, φ, hμ, hφ, heig⟩

end Extraction

section ExtractionFull

/-!
## Full rank-one extraction for finite matrix families

This module constructs the bounded rank-one element used in Sanz, Pérez-García,
Wolf, and Cirac, arXiv:0909.5347, Lemma 2(b), for an arbitrary finite family of
square matrices whose fixed-length word span is full.
-/

variable {d D : ℕ}

/-- A power of one matrix in a finite family belongs to the corresponding word span. -/
theorem pow_single_mem_wordSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (i : Fin d) :
    (K i) ^ D ∈ wordSpan K D := by
  have heq : K i = Kraus.evalWord K [i] := by simp [Kraus.evalWord]
  have hmem :
      (Kraus.evalWord K [i]) ^ D ∈
        wordSpan K (D * ([i] : List (Fin d)).length) :=
    evalWord_pow_mem_wordSpan K [i] D
  rw [show D * ([i] : List (Fin d)).length = D from by simp] at hmem
  rwa [← heq] at hmem

private structure BlockedTensorRangeData
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (L : ℕ)
    (σ₀ τ₀ : Fin L → Fin d) (φ ψ : Fin D → ℂ) where
  B : Fin (Kraus.blockPhysDim d L) → Matrix (Fin D) (Fin D) ℂ
  P : Matrix (Fin D) (Fin D) ℂ
  Q : Matrix (Fin D) (Fin D) ℂ
  hB : B = Kraus.blockTensor K L
  hP : P ∈ wordSpan B D
  hQ : Q ∈ wordSpan B D
  hφ_range : φ ∈ LinearMap.range (Matrix.toLin' P)
  hψ_range : ψ ∈ LinearMap.range (Q.vecMulLinear)

private noncomputable def blockedTensorRangeData
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (L : ℕ)
    (σ₀ τ₀ : Fin L → Fin d) (φ ψ : Fin D → ℂ) (μ ν : ℂ)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (heigφ : Kraus.evalWord K (List.ofFn σ₀) *ᵥ φ = μ • φ)
    (heigψ : (Kraus.evalWord K (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ) :
    BlockedTensorRangeData K L σ₀ τ₀ φ ψ := by
  let B := Kraus.blockTensor K L
  let i₀ : Fin (Kraus.blockPhysDim d L) :=
    (Kraus.decodeBlockEquiv d L).symm σ₀
  let i₁ : Fin (Kraus.blockPhysDim d L) :=
    (Kraus.decodeBlockEquiv d L).symm τ₀
  have hBi₀ : B i₀ = Kraus.evalWord K (List.ofFn σ₀) := by
    simp [B, i₀, Kraus.blockTensor, Kraus.reindexPhysical]
  have hBi₁ : B i₁ = Kraus.evalWord K (List.ofFn τ₀) := by
    simp [B, i₁, Kraus.blockTensor, Kraus.reindexPhysical]
  refine
    { B := B
      P := (B i₀) ^ D
      Q := (B i₁) ^ D
      hB := rfl
      hP := pow_single_mem_wordSpan B i₀
      hQ := pow_single_mem_wordSpan B i₁
      hφ_range := ?_
      hψ_range := ?_ }
  · simpa [hBi₀] using
      Matrix.mem_range_toLin'_pow_of_eigenvector
        (M := Kraus.evalWord K (List.ofFn σ₀)) (φ := φ) (μ := μ) hμ heigφ
  · simpa [hBi₁] using
      Matrix.mem_range_vecMulLinear_pow_of_transpose_eigenvector
        (M := Kraus.evalWord K (List.ofFn τ₀)) (ψ := ψ) (ν := ν) hν heigψ

private theorem BlockedTensorRangeData.rankOne_mem_wordSpan_of_wordSpan_eq_top
    {K : Fin d → Matrix (Fin D) (Fin D) ℂ} {L : ℕ}
    {σ₀ τ₀ : Fin L → Fin d} {φ ψ : Fin D → ℂ}
    (data : BlockedTensorRangeData K L σ₀ τ₀ φ ψ)
    {N : ℕ} (htop : wordSpan data.B N = ⊤) :
    Matrix.vecMulVec φ ψ ∈ wordSpan data.B (D + N + D) := by
  have hrange_le :
      LinearMap.range
          ((LinearMap.mulLeft ℂ data.P).comp (LinearMap.mulRight ℂ data.Q)) ≤
        wordSpan data.B (D + N + D) := by
    rw [← biRectSpan_eq_range_of_wordSpan_eq_top data.P data.Q data.B htop]
    exact biRectSpan_le_wordSpan data.B data.P data.Q data.hP data.hQ
  exact hrange_le (Matrix.vecMulVec_mem_range_mulLeft_mulRight
    data.P data.Q φ ψ data.hφ_range data.hψ_range)

/-- **Full rank-one extraction for Wielandt Lemma 2(b).**

A positive level at which a finite matrix family's word span is full yields
nonzero right and transpose eigenvectors and a rank-one element in a bounded
word span of the blocked family. -/
theorem exists_rankOne_mem_wordSpan_blockTensor [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N₀ : ℕ}
    (hN₀ : wordSpan K N₀ = ⊤) (hN₀pos : 0 < N₀) :
    ∃ (σ₀ τ₀ : Fin N₀ → Fin d)
      (φ ψ : Fin D → ℂ) (μ ν : ℂ) (m_blocked : ℕ),
      φ ≠ 0 ∧ ψ ≠ 0 ∧ μ ≠ 0 ∧ ν ≠ 0 ∧
      Kraus.evalWord K (List.ofFn σ₀) *ᵥ φ = μ • φ ∧
      (Kraus.evalWord K (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ ∧
      Matrix.vecMulVec φ ψ ∈
        wordSpan (Kraus.blockTensor K N₀) m_blocked := by
  classical
  obtain ⟨σ₀, μ, φ, hμ, hφ, heigφ⟩ :=
    exists_eigenvector_of_wordSpan_eq_top K hN₀
  have hN₀T : wordSpan (transposeFamily K) N₀ = ⊤ :=
    wordSpan_transposeFamily_eq_top_of_wordSpan_eq_top K hN₀
  obtain ⟨τ₀', ν, ψ, hν, hψ, heigψ'⟩ :=
    exists_eigenvector_of_wordSpan_eq_top (transposeFamily K) hN₀T
  let τ₀ : Fin N₀ → Fin d := τ₀' ∘ Fin.rev
  have hτ₀_eq : List.ofFn τ₀ = (List.ofFn τ₀').reverse :=
    (List.ofFn_reverse τ₀').symm
  have heigψ : (Kraus.evalWord K (List.ofFn τ₀))ᵀ *ᵥ ψ = ν • ψ := by
    rw [hτ₀_eq, evalWord_transpose K (List.ofFn τ₀').reverse, List.reverse_reverse]
    exact heigψ'
  let data := blockedTensorRangeData K N₀ σ₀ τ₀ φ ψ μ ν hμ hν heigφ heigψ
  have hBtop : wordSpan data.B N₀ = ⊤ := by
    have hInjective : Kraus.IsInjective (Kraus.blockTensor K N₀) :=
      (Kraus.isNBlkInjective_iff_blockTensor_isInjective K N₀).mp hN₀
    have hB1 : wordSpan data.B 1 = ⊤ := by
      rw [wordSpan_one, data.hB]
      exact hInjective
    simpa using wordSpan_top_of_mul data.B hB1 N₀ hN₀pos
  exact ⟨σ₀, τ₀, φ, ψ, μ, ν, D + N₀ + D,
    hφ, hψ, hμ, hν, heigφ, heigψ, by
      simpa [data.hB] using data.rankOne_mem_wordSpan_of_wordSpan_eq_top hBtop⟩

end ExtractionFull

end Kraus
