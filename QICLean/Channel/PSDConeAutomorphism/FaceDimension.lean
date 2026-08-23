/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.CornerCompression
import QICLean.Analysis.MatrixSqrt

/-!
# Dimension of the span of Wolf's positive-semidefinite cone C(P)

This file formalizes the cone $C(P)$ from Wolf, Proposition 3.6, equation (3.42),
and identifies its complex linear span with the matrix corner supported on $P$.

## Main declarations

* `Matrix.psdConeFace`: Wolf's cone $C(P)=\{A\mid \exists c>0,\ P\geq cA\geq0\}$.
* `Matrix.span_psdConeFace_eq_cornerSubmodule_supportProj`: the span of $C(P)$ is the
  corner supported on `P`.
* `Matrix.finrank_span_psdConeFace_eq_rank_sq`: the dimension of that span is
  $\operatorname{rank}(P)^2$.

The source is Wolf, *Quantum Channels & Operations*, Chapter 3, Proposition 3.6,
equation (3.42), local source
`Notes/WolfNoteTexSource/ch03_positive_not_completely.tex`, lines 663--671.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {D : ℕ}

/-- Wolf's positive-semidefinite cone
$C(P)=\{A\in\mathcal M_D(\mathbb C)\mid \exists c>0,\ P\geq cA\geq0\}$ from
Proposition 3.6, equation (3.42).

The scalar $c$ is real; its action on a complex matrix is the canonical real
scalar action, and the two inequalities use the positive-semidefinite order. -/
def psdConeFace (P : MatrixAlg D) : Set (MatrixAlg D) :=
  {A | ∃ c : ℝ, 0 < c ∧ (0 : MatrixAlg D) ≤ c • A ∧ c • A ≤ P}

/-- A matrix belongs to Wolf's cone $C(P)$ exactly when it is positive
semidefinite and supported on the support projection of $P$. Thus $C(P)$ is the
support face of the positive-semidefinite cone. -/
theorem mem_psdConeFace_iff (P A : MatrixAlg D) (hP : P.PosSemidef) :
    A ∈ psdConeFace P ↔
      A.PosSemidef ∧ A ∈ cornerSubmodule hP.supportProj := by
  classical
  constructor
  · rintro ⟨c, hc, hcA0, hcAP⟩
    have hcA : (c • A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp hcA0
    have hsub : (P - c • A).PosSemidef := Matrix.le_iff.mp hcAP
    have hA : A.PosSemidef := by
      have hinv : (0 : ℝ) ≤ c⁻¹ := (inv_pos.mpr hc).le
      have hscaled := hcA.smul hinv
      simpa [smul_smul, ne_of_gt hc] using hscaled
    have hker : ∀ v : Fin D → ℂ, P *ᵥ v = 0 → A *ᵥ v = 0 := by
      intro v hv
      have hsum : ((c • A) + (P - c • A)) *ᵥ v = 0 := by
        have heq : (c • A) + (P - c • A) = P := by abel
        rw [heq, hv]
      have hcAv : (c • A) *ᵥ v = 0 :=
        Matrix.PosSemidef.mulVec_eq_zero_left hcA hsub v hsum
      simpa [Matrix.smul_mulVec, ne_of_gt hc] using hcAv
    have hright : A * hP.supportProj = A :=
      hP.isHermitian.mul_supportProj_eq_self_of_mulVec_kernel_le hker
    have hleft : hP.supportProj * A = A := by
      have hcongr := congrArg Matrix.conjTranspose hright
      simpa [Matrix.conjTranspose_mul, hP.supportProj_isHermitian.eq,
        hA.isHermitian.eq] using hcongr
    refine ⟨hA, ?_⟩
    change hP.supportProj * A * hP.supportProj = A
    rw [hleft, hright]
  · rintro ⟨hA, hcorner⟩
    have hker : ∀ v : Fin D → ℂ, P *ᵥ v = 0 → A *ᵥ v = 0 := by
      intro v hv
      have hPv : hP.supportProj *ᵥ v = 0 :=
        hP.supportProj_mulVec_eq_zero_of_mulVec_eq_zero v hv
      have hcorner' : hP.supportProj * A * hP.supportProj = A := hcorner
      rw [← hcorner', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPv,
        Matrix.mulVec_zero, Matrix.mulVec_zero]
    let q := ‖hP.supportInvSqrt * A * hP.supportInvSqrt‖
    let c : ℝ := (q + 1)⁻¹
    have hq : 0 ≤ q := norm_nonneg _
    have hc : 0 < c := inv_pos.mpr (by linarith)
    have hbound : c * q ≤ 1 :=
      (inv_mul_le_one₀ (by linarith : 0 < q + 1)).2 (by linarith)
    have hsub : (P - c • A).PosSemidef :=
      (hP.sub_smul_posSemidef_iff hA hc hker).mpr hbound
    refine ⟨c, hc, Matrix.nonneg_iff_posSemidef.mpr (hA.smul hc.le), ?_⟩
    exact Matrix.le_iff.mpr hsub

/-- The complex span of Wolf's cone $C(P)$ is the full support corner
$\operatorname{supp}(P)\,\mathcal M_D(\mathbb C)\,\operatorname{supp}(P)$.

This is the cone/corner step in Wolf, Proposition 3.6, immediately after
equation (3.42). -/
theorem span_psdConeFace_eq_cornerSubmodule_supportProj
    (P : MatrixAlg D) (hP : P.PosSemidef) :
    Submodule.span ℂ (psdConeFace P) = cornerSubmodule hP.supportProj := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    intro A hA
    exact ((mem_psdConeFace_iff P A hP).mp hA).2
  · intro A hA
    have hall : A ∈ Submodule.span ℂ {B : MatrixAlg D | B.PosSemidef} := by
      have htop : Submodule.span ℂ {B : MatrixAlg D | B.PosSemidef} = ⊤ := by
        simpa only [Matrix.nonneg_iff_posSemidef] using
          (CStarAlgebra.span_nonneg (A := MatrixAlg D))
      rw [htop]
      exact Submodule.mem_top
    have hcompressed :
        hP.supportProj * A * hP.supportProj ∈ Submodule.span ℂ (psdConeFace P) := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hall
      · intro B hB
        have hBPB : (hP.supportProj * B * hP.supportProj).PosSemidef := by
          have hcongr := hB.conjTranspose_mul_mul_same hP.supportProj
          simpa [hP.supportProj_isHermitian.eq] using hcongr
        apply Submodule.subset_span
        apply (mem_psdConeFace_iff P _ hP).mpr
        refine ⟨hBPB, ?_⟩
        change hP.supportProj * (hP.supportProj * B * hP.supportProj) *
            hP.supportProj = hP.supportProj * B * hP.supportProj
        calc
          hP.supportProj * (hP.supportProj * B * hP.supportProj) * hP.supportProj =
              (hP.supportProj * hP.supportProj) * B *
                (hP.supportProj * hP.supportProj) := by simp only [Matrix.mul_assoc]
          _ = hP.supportProj * B * hP.supportProj := by rw [hP.supportProj_idem]
      · simpa only [Matrix.mul_zero, Matrix.zero_mul] using
          (Submodule.zero_mem (Submodule.span ℂ (psdConeFace P)))
      · intro X Y _ _ hX hY
        simpa only [Matrix.mul_add, Matrix.add_mul] using
          (Submodule.add_mem _ hX hY)
      · intro c X _ hX
        simpa only [Matrix.mul_smul, smul_mul_assoc] using
          (Submodule.smul_mem _ c hX)
    exact hA ▸ hcompressed

/-- The complex dimension of the span of Wolf's cone $C(P)$ is
$\operatorname{rank}(P)^2$, as asserted after equation (3.42) in Wolf,
Proposition 3.6. -/
theorem finrank_span_psdConeFace_eq_rank_sq
    (P : MatrixAlg D) (hP : P.PosSemidef) :
    Module.finrank ℂ (Submodule.span ℂ (psdConeFace P)) = P.rank ^ 2 := by
  classical
  rw [span_psdConeFace_eq_cornerSubmodule_supportProj P hP]
  let hProj := hP.isOrthogonalProjection_supportProj
  let n := cornerRank hP.supportProj hProj
  have hn : n = P.rank := by
    have hnC : (n : ℂ) = (P.rank : ℂ) := by
      calc
        (n : ℂ) = Matrix.trace hP.supportProj := cornerRank_eq_trace _ hProj
        _ = (P.rank : ℂ) := hP.supportProj_trace
    exact_mod_cast hnC
  rw [← hn]
  have heq := (cornerSubmoduleMatrixLinearEquiv hP.supportProj hProj).finrank_eq
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self] at heq
  simpa [pow_two] using heq.symm

end Matrix
