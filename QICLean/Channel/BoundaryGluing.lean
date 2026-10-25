/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.PartialTrace
import QICLean.Analysis.RectangularTraceNormAlgebra

/-!
# Gluing a left state to a right half through its boundary contraction

Fix a cut of a tensor product `(A ⊗ S) ⊗ R`, where `A` is the part strictly left of a site,
`S` is that site and `R` is the part to its right. Let `W : ℂ^B → R` be an isometry. A vector
`v = (1 ⊗ W) x` has *left state* `x ∈ (A ⊗ S) ⊗ ℂ^B`, and its *boundary contraction* is
`tr_A |x⟩⟨x|`, a matrix on `S ⊗ ℂ^B`. A matrix `σ` on `(A ⊗ S) ⊗ ℂ^B` is glued back to the
right half as `σ' = (1 ⊗ W) σ (1 ⊗ W)*`.

## Main definitions

* `Matrix.partialTraceFirst`: the trace over `A` of a matrix on `(A ⊗ S) ⊗ C`.

## Main results

* `Matrix.conjTranspose_mulVec_gluing`: `x = (1 ⊗ W)* v` is the left state of `v`.
* `Matrix.partialTraceRight_gluing`: `tr_R σ' = tr_{ℂ^B} σ`.
* `Matrix.partialTraceFirst_gluing`: `tr_A σ' = (1 ⊗ W) (tr_A σ) (1 ⊗ W)*`.
* `Matrix.rectangularTraceNorm_partialTraceFirst_gluing_sub`: the boundary contraction of `σ'`
  is as far from that of `v` as the boundary contraction of `σ` is from that of `x`.
* `Matrix.re_trace_gluing_le`: for `H = H_L ⊗ 1 + 1 ⊗ K`, with `H_L` on `A ⊗ S` and `K` on
  `S ⊗ R`, `tr(σ' H) ≤ tr(σ (H_L ⊗ 1)) + ⟨v, (1 ⊗ K) v⟩ + ‖K‖ ‖tr_A σ - tr_A |x⟩⟨x|‖₁`.

These are the left state, the boundary contraction and Lemma `l:gluing` of Landau, Vazirani
and Vidick. In the source, `W = U_v` maps `|j⟩` to the `j`-th right Schmidt vector of `v`, so
that `x = U_v* v` is the left state `ls(v)`; the statements here hold for every isometry `W`
whose range contains the right Schmidt vectors of `v`. The constant `n` of the printed energy
bound is replaced by `‖K‖`, which is at most `n` for the chain Hamiltonian of the source.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`: boundary contractions,
  lines 409–417; Lemma `l:gluing`, lines 421–447.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator

namespace Matrix

variable {a s r b : Type*} [Fintype a] [Fintype s] [Fintype r] [Fintype b]
  [DecidableEq a] [DecidableEq s] [DecidableEq r] [DecidableEq b]

/-- The trace over the first factor `A` of a matrix on `(A ⊗ S) ⊗ C`, a matrix on `S ⊗ C`.
For `C` the right half or the bond of a cut, this is the trace `tr_{[1, i-1]}` over the sites
strictly left of the cut site. -/
noncomputable def partialTraceFirst {c : Type*} (X : Matrix ((a × s) × c) ((a × s) × c) ℂ) :
    Matrix (s × c) (s × c) ℂ :=
  partialTraceLeft (reindex (Equiv.prodAssoc a s c) (Equiv.prodAssoc a s c) X)

omit [DecidableEq r] in
/-- **The left state.** If `W` is an isometry and `v = (1 ⊗ W) x`, then `x = (1 ⊗ W)* v`:
the vector `x` is the left state `ls(v) = U_v* v` of arXiv:1307.5143v1, `algo53.tex`,
lines 412–414, when `W = U_v`. -/
theorem conjTranspose_mulVec_gluing (W : Matrix r b ℂ) (hW : Wᴴ * W = 1)
    (x : (a × s) × b → ℂ) :
    ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W)ᴴ *ᵥ (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x) =
      x := by
  rw [mulVec_mulVec, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
    Matrix.one_mul, hW, one_kronecker_one, one_mulVec]

omit [DecidableEq r] in
/-- **The trace over the right half of a glued matrix** (Lemma `l:gluing`, part 1,
arXiv:1307.5143v1, `algo53.tex`, lines 424–425). If `W` is an isometry, then
`tr_R ((1 ⊗ W) σ (1 ⊗ W)*) = tr_{ℂ^B} σ`. -/
theorem partialTraceRight_gluing (W : Matrix r b ℂ) (hW : Wᴴ * W = 1)
    (σ : Matrix ((a × s) × b) ((a × s) × b) ℂ) :
    partialTraceRight (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) * σ *
        ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W)ᴴ) = partialTraceRight σ := by
  simpa using partialTraceRight_kronecker_conj_of_right_isometry
    (1 : Matrix (a × s) (a × s) ℂ) W hW σ

omit [Fintype r] [DecidableEq r] [DecidableEq b] in
/-- **The trace over the left sites of a glued matrix.** For every matrix `W : ℂ^B → R`,
`tr_A ((1 ⊗ W) X (1 ⊗ W)*) = (1 ⊗ W) (tr_A X) (1 ⊗ W)*`. This is the computation in the proof
of Lemma `l:gluing`, part 2, arXiv:1307.5143v1, `algo53.tex`, lines 433–437. -/
theorem partialTraceFirst_gluing (W : Matrix r b ℂ)
    (X : Matrix ((a × s) × b) ((a × s) × b) ℂ) :
    partialTraceFirst (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) * X *
        ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W)ᴴ) =
      ((1 : Matrix s s ℂ) ⊗ₖ W) * partialTraceFirst X * ((1 : Matrix s s ℂ) ⊗ₖ W)ᴴ := by
  have hJ : reindex (Equiv.prodAssoc a s r) (Equiv.prodAssoc a s b)
      ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) =
        (1 : Matrix a a ℂ) ⊗ₖ ((1 : Matrix s s ℂ) ⊗ₖ W) := by
    rw [← one_kronecker_one, kronecker_assoc]
  have hprod : reindex (Equiv.prodAssoc a s r) (Equiv.prodAssoc a s r)
      (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) * X * ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W)ᴴ) =
        reindex (Equiv.prodAssoc a s r) (Equiv.prodAssoc a s b)
            ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *
          reindex (Equiv.prodAssoc a s b) (Equiv.prodAssoc a s b) X *
          (reindex (Equiv.prodAssoc a s r) (Equiv.prodAssoc a s b)
            ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W))ᴴ := by
    simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
  rw [partialTraceFirst, hprod, hJ, partialTraceLeft_kronecker_conj_of_left_isometry _ _
    (by rw [conjTranspose_one, Matrix.one_mul])]
  rfl

/-- **Boundary contractions of a glued matrix** (Lemma `l:gluing`, part 2, arXiv:1307.5143v1,
`algo53.tex`, lines 426–427). Let `W` be an isometry and `v = (1 ⊗ W) x`. Then the trace norm
of `tr_A σ' - tr_A |v⟩⟨v|` equals that of `tr_A σ - tr_A |x⟩⟨x|`, where
`tr_A |x⟩⟨x|` is the boundary contraction of `v`. -/
theorem rectangularTraceNorm_partialTraceFirst_gluing_sub (W : Matrix r b ℂ)
    (hW : Wᴴ * W = 1) (σ : Matrix ((a × s) × b) ((a × s) × b) ℂ) (x : (a × s) × b → ℂ) :
    rectangularTraceNorm
        (partialTraceFirst (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) * σ *
            ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W)ᴴ) -
          partialTraceFirst (vecMulVec (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x)
            (star (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x)))) =
      rectangularTraceNorm (partialTraceFirst σ - partialTraceFirst (vecMulVec x (star x))) := by
  set J := (1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W
  set K := (1 : Matrix s s ℂ) ⊗ₖ W
  have hv : vecMulVec (J *ᵥ x) (star (J *ᵥ x)) = J * vecMulVec x (star x) * Jᴴ := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
  have hK : Kᴴ * K = 1 := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul, hW,
      one_kronecker_one]
  rw [hv, partialTraceFirst_gluing, partialTraceFirst_gluing, ← Matrix.sub_mul, ← Matrix.mul_sub,
    rectangularTraceNorm_isometry_sandwich _ K K hK hK]

omit [DecidableEq r] in
/-- `|tr(Y K)| ≤ ‖K‖ ‖Y‖₁` for square matrices, with the operator norm of `K` and the trace
norm of `Y`. -/
theorem norm_trace_mul_le_l2_opNorm_mul_rectangularTraceNorm {n : Type*} [Fintype n]
    [DecidableEq n] (Y K : Matrix n n ℂ) :
    ‖(Y * K).trace‖ ≤ ‖K‖ * rectangularTraceNorm Y := by
  rcases eq_or_ne K 0 with rfl | hK
  · simp
  have hpos : 0 < ‖K‖ := norm_pos_iff.mpr hK
  have hU : ‖(‖K‖⁻¹ : ℂ) • K‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
      inv_mul_cancel₀ hpos.ne']
  have h := norm_trace_conjTranspose_mul_le_rectangularTraceNorm Yᴴ _ hU
  rw [conjTranspose_conjTranspose, rectangularTraceNorm_conjTranspose, Matrix.mul_smul,
    trace_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at h
  rwa [inv_mul_le_iff₀ hpos] at h

/-- **The energy of a glued matrix** (Lemma `l:gluing`, part 3, arXiv:1307.5143v1,
`algo53.tex`, lines 428–429 and 439–445). Let `W` be an isometry, `v = (1 ⊗ W) x`, and let
`H = H_L ⊗ 1 + 1 ⊗ K` with `H_L` acting on `A ⊗ S` and `K` acting on `S ⊗ R`. Then
`Re tr(σ' H) ≤ Re tr(σ (H_L ⊗ 1)) + Re ⟨v, (1 ⊗ K) v⟩ + ‖K‖ ‖tr_A σ - tr_A |x⟩⟨x|‖₁`.

For the chain Hamiltonian of the source, `H_L = H_1 + ⋯ + H_{i-1}` and `K = H_i + H_R`, whose
norm is at most the printed constant `n`. -/
theorem re_trace_gluing_le (W : Matrix r b ℂ) (hW : Wᴴ * W = 1)
    (σ : Matrix ((a × s) × b) ((a × s) × b) ℂ) (x : (a × s) × b → ℂ)
    (HL : Matrix (a × s) (a × s) ℂ) (K : Matrix (s × r) (s × r) ℂ) :
    (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) * σ * ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W)ᴴ *
        (HL ⊗ₖ (1 : Matrix r r ℂ) +
          reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
            ((1 : Matrix a a ℂ) ⊗ₖ K))).trace.re ≤
      (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re +
        (vecMulVec (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x)
            (star (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x)) *
          reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
            ((1 : Matrix a a ℂ) ⊗ₖ K)).trace.re +
        ‖K‖ * rectangularTraceNorm
          (partialTraceFirst σ - partialTraceFirst (vecMulVec x (star x))) := by
  set J := (1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W
  set e := Equiv.prodAssoc a s r
  set v := J *ᵥ x
  -- The left part: `Jᴴ (H_L ⊗ 1) J = H_L ⊗ Wᴴ W = H_L ⊗ 1`.
  have hleft : (J * σ * Jᴴ * (HL ⊗ₖ (1 : Matrix r r ℂ))).trace =
      (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace := by
    have h : Jᴴ * (HL ⊗ₖ (1 : Matrix r r ℂ)) * J = HL ⊗ₖ (1 : Matrix b b ℂ) := by
      simp only [J, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
        Matrix.one_mul, Matrix.mul_one, hW]
    calc (J * σ * Jᴴ * (HL ⊗ₖ (1 : Matrix r r ℂ))).trace
        = (J * (σ * (Jᴴ * (HL ⊗ₖ (1 : Matrix r r ℂ))))).trace := by
          simp only [Matrix.mul_assoc]
      _ = (σ * (Jᴴ * (HL ⊗ₖ (1 : Matrix r r ℂ))) * J).trace := Matrix.trace_mul_comm _ _
      _ = (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace := by
          rw [← h]; simp only [Matrix.mul_assoc]
  -- The right part as a pairing of boundary contractions with `K`.
  have hright (Y : Matrix ((a × s) × r) ((a × s) × r) ℂ) :
      (Y * reindex e.symm e.symm ((1 : Matrix a a ℂ) ⊗ₖ K)).trace =
        (partialTraceFirst Y * K).trace := by
    rw [partialTraceFirst, trace_partialTraceLeft_mul,
      ← trace_submatrix_equiv e.symm (Y * reindex e.symm e.symm _),
      ← submatrix_mul_equiv Y _ e.symm e.symm e.symm]
    simp only [reindex_apply, Equiv.symm_symm, submatrix_submatrix, Equiv.self_comp_symm,
      submatrix_id_id]
    rfl
  have hdiff : (J * σ * Jᴴ * reindex e.symm e.symm ((1 : Matrix a a ℂ) ⊗ₖ K)).trace -
      (vecMulVec v (star v) * reindex e.symm e.symm ((1 : Matrix a a ℂ) ⊗ₖ K)).trace =
        ((partialTraceFirst (J * σ * Jᴴ) - partialTraceFirst (vecMulVec v (star v))) *
          K).trace := by
    rw [hright, hright, Matrix.sub_mul, trace_sub]
  have hbound := norm_trace_mul_le_l2_opNorm_mul_rectangularTraceNorm
    (partialTraceFirst (J * σ * Jᴴ) - partialTraceFirst (vecMulVec v (star v))) K
  rw [rectangularTraceNorm_partialTraceFirst_gluing_sub W hW σ x] at hbound
  have hre := (Complex.re_le_norm _).trans hbound
  rw [← hdiff, Complex.sub_re] at hre
  rw [Matrix.mul_add, trace_add, Complex.add_re, hleft]
  linarith

end Matrix
