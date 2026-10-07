/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.CommutantDimension
import QICLean.Channel.PartialTrace
import QICLean.Algebra.MatrixAux

/-!
# Mass selection among the actual Schur sectors

Every density matrix on `(ℂ^q)^{⊗k}` gives mass at least `(k+1)^{-q²}` to some
Schur sector. For a unit vector with an arbitrary additional tensor factor,
this mass is the squared norm of its projection onto the same sector.
The projectors are the central isotypic projectors of the copy-permutation
representation; the reduced density matrix is obtained by the partial trace.

These are the finite-sector mass estimates used in the argument surrounding
`comparator:high-label` in *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 255–281. They do not impose an entropy window on the
selected label. In particular, they do not prove the accompanying asymptotic
formula for the irreducible dimension, select a common sequence for Bell
pinning, or establish positive occurrence on the initial uniform pair,
matching of the auxiliary labels, or the energy statement.
-/

/-
Original finite-dimensional Schur-sector mass selection supporting OpenAI,
A two-dimensional area law from a global spectral gap, September 24, 2026,
07-comparators.tex lines 255–281, comparator:high-label.
Only generic mass selection is proved; the entropy window, common Bell
sequence, initial positive occurrence, auxiliary-label matching, and energy
statement remain separate. No upstream Lean proof text reused.
Provenance-ID: 8753-qic-schur-sector-mass-01
TensorPower.exists_labelProj_trace_mass_ge
Provenance-ID: 8753-qic-schur-sector-mass-02
TensorPower.exists_labelProj_norm_mass_ge
-/

open Matrix PermutationRepresentation
open scoped Matrix ComplexOrder Kronecker

namespace TensorPower

variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] (k : ℕ)

/-- Some actual Schur sector has inverse polynomial mass in any density matrix.
This proves the generic mass selection step in `07-comparators.tex`,
`comparator:high-label`, lines 255–281; it does not select an entropy window. -/
theorem exists_labelProj_trace_mass_ge
    (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) :
    ∃ l : IrrepLabel (Equiv.Perm (Fin k)),
      (((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) : ℝ)⁻¹ ≤
        (ρ * labelProj (copyPerm Ω k) l).trace.re := by
  classical
  let L := Finset.univ.filter fun l : IrrepLabel (Equiv.Perm (Fin k)) =>
    labelProj (copyPerm Ω k) l ≠ 0
  let m := fun l => (ρ * labelProj (copyPerm Ω k) l).trace.re
  have hm (l) : 0 ≤ m l :=
    (Complex.nonneg_iff.mp (hρ.trace_mul_nonneg
      ((isHermitian_labelProj _ l).posSemidef_of_mul_self
        (labelProj_mul_self _ l)))).1
  have hsum : ∑ l ∈ L, m l = 1 := by
    rw [Finset.sum_filter_of_ne]
    · change ∑ l, (ρ * labelProj (copyPerm Ω k) l).trace.re = 1
      rw [← Complex.re_sum, ← trace_sum, ← Matrix.mul_sum,
        sum_labelProj, Matrix.mul_one, htr]
      rfl
    · intro l _ h
      contrapose! h
      simp [m, h]
  have hL : L.Nonempty := by
    obtain ⟨l, hl, _⟩ := (Finset.sum_pos_iff_of_nonneg (fun l _ => hm l)).mp
      (by rw [hsum]; norm_num)
    exact ⟨l, hl⟩
  have hN : 0 < (((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) : ℝ) := by positivity
  have hc : (L.card : ℝ) ≤ (((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast card_labelProj_ne_zero_le Ω k
  obtain ⟨l, _, hl⟩ := Finset.exists_le_of_sum_le hL (f := fun _ =>
      (((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) : ℝ)⁻¹) (g := m) (by
    rw [Finset.sum_const, nsmul_eq_mul, hsum]
    exact (mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr hN.le)).trans_eq
      (mul_inv_cancel₀ hN.ne'))
  exact ⟨l, hl⟩

/-- A unit vector with an arbitrary additional tensor factor has a nonzero
projection onto an actual Schur sector of inverse polynomial squared norm.
The mass is computed from its actual reduced density matrix. This is the
mass selection step in `07-comparators.tex`, `comparator:high-label`,
lines 255–281; the irreducible-dimension entropy window remains separate. -/
theorem exists_labelProj_norm_mass_ge {S : Type*} [Fintype S] [DecidableEq S]
    (v : EuclideanSpace ℂ (S × (Fin k → Ω))) (hv : ‖v‖ = 1) :
    ∃ l : IrrepLabel (Equiv.Perm (Fin k)),
      (((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) : ℝ)⁻¹ ≤
        ‖WithLp.toLp 2 (((1 : Matrix S S ℂ) ⊗ₖ
          labelProj (copyPerm Ω k) l).mulVec v.ofLp)‖ ^ 2 ∧
      WithLp.toLp 2 (((1 : Matrix S S ℂ) ⊗ₖ
        labelProj (copyPerm Ω k) l).mulVec v.ofLp) ≠ 0 := by
  classical
  let ρ := partialTraceLeft (vecMulVec v.ofLp (star v.ofLp))
  have hρ : ρ.PosSemidef := (posSemidef_vecMulVec_self_star v.ofLp).partialTraceLeft
  have htr : ρ.trace = 1 := by
    rw [trace_partialTraceLeft, trace_vecMulVec,
      ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hv]
    norm_num
  obtain ⟨l, hl⟩ := exists_labelProj_trace_mass_ge Ω k ρ hρ htr
  let P := labelProj (copyPerm Ω k) l
  let Q := (1 : Matrix S S ℂ) ⊗ₖ P
  have hQ : Q.IsHermitian := by
    change Qᴴ = Q
    rw [conjTranspose_kronecker, conjTranspose_one, (isHermitian_labelProj _ l).eq]
  have hQQ : Q * Q = Q := by
    rw [← mul_kronecker_mul, Matrix.one_mul, labelProj_mul_self]
  have hmass : (ρ * P).trace.re = ‖WithLp.toLp 2 (Q.mulVec v.ofLp)‖ ^ 2 := by
    rw [trace_partialTraceLeft_mul, trace_mul_comm, Matrix.mul_vecMulVec,
      trace_vecMulVec, dotProduct_comm]
    have hpair : star v.ofLp ⬝ᵥ Q.mulVec v.ofLp =
        star (Q.mulVec v.ofLp) ⬝ᵥ Q.mulVec v.ofLp := by
      calc
        star v.ofLp ⬝ᵥ Q.mulVec v.ofLp =
            star v.ofLp ⬝ᵥ Q.mulVec (Q.mulVec v.ofLp) := by
          rw [mulVec_mulVec, hQQ]
        _ = star (Qᴴ.mulVec v.ofLp) ⬝ᵥ Q.mulVec v.ofLp :=
          star_dotProduct_mulVec Q v.ofLp (Q.mulVec v.ofLp)
        _ = star (Q.mulVec v.ofLp) ⬝ᵥ Q.mulVec v.ofLp := by rw [hQ.eq]
    change (star v.ofLp ⬝ᵥ Q.mulVec v.ofLp).re = _
    rw [hpair]
    exact re_star_dotProduct_self_eq_norm_sq _
  rw [hmass] at hl
  refine ⟨l, hl, ?_⟩
  intro hz
  rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hl
  exact (not_le_of_gt (by positivity :
    0 < (((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) : ℝ)⁻¹)) hl

end TensorPower
