/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Spectral.Eigenvalue.ShiftedTracePowerSpectrum

/-!
# Shifted Zero Trace Powers Force Nilpotence

A finite complex square matrix whose powers of every exponent greater than one
have trace zero is nilpotent. In fact, its characteristic polynomial is a pure
power of `X`.

In arXiv:1703.09188, lines 405--410, the source derives vanishing traces for
every positive exponent. Newton--Girard directly handles that all-positive
hypothesis. This file also proves the stronger implication that assumes
vanishing only for exponents greater than one. For this shifted generalization,
passing to `A ^ 2` supplies all positive trace powers of the squared matrix;
spectral mapping, splitting of the characteristic polynomial, and
Cayley--Hamilton then prove nilpotence.

The all-positive specialization is the elementwise nilpotence step used before
the finite-dimensional nil-matrix theorem in arXiv:1703.09188, line 410. No
positivity, normality, or diagonalizability hypothesis is used.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1703.09188, line 410

Moved from TNLean, `TNLean/MPS/MPU/Symmetry/Phases/ConjugationDeterminantInvariant.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

open scoped Matrix
open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If all positive trace powers of a finite complex matrix vanish, its
characteristic polynomial is `X ^ n`.

This Newton--Girard auxiliary lemma supplies the powered-matrix step in the argument of
arXiv:1703.09188, line 410. -/
theorem charpoly_eq_X_pow_card_of_forall_trace_pow_eq_zero
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 0 < k → trace (A ^ k) = 0) :
    A.charpoly = X ^ Fintype.card n := by
  have hchar : A.charpoly = (0 : Matrix n n ℂ).charpoly :=
    charpoly_eq_of_forall_trace_pow_eq A 0 (fun k hk => by
      rw [h k hk]
      simp [hk.ne'])
  simpa using hchar

/-- A shifted zero-moment hypothesis becomes an all-positive zero-moment
hypothesis after replacing `A` by `A ^ m`, provided `m > 1`.

This reduction supports the stronger shifted generalization proved here. The
source passage arXiv:1703.09188, lines 405--410, itself supplies vanishing for
every positive exponent. -/
theorem forall_trace_pow_pow_eq_zero_of_forall_trace_pow_eq_zero_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 0)
    (m : ℕ) (hm : 1 < m) :
    ∀ k : ℕ, 0 < k → trace ((A ^ m) ^ k) = 0 := by
  intro k hk
  rw [← pow_mul]
  exact h (m * k) (hm.trans_le (Nat.le_mul_of_pos_right m hk))

/-- If all traces `tr(A ^ N)` with `N > 1` vanish, then every spectral
value of `A` is zero.

The proof passes to `A ^ 2`, whose characteristic polynomial is `X ^ n`.
Spectral mapping then forces the square of every spectral value to vanish, hence
the spectral value itself vanishes. This extends the spectral consequence of
arXiv:1703.09188, line 410, from its all-positive hypothesis to the weaker
shifted hypothesis. -/
theorem eq_zero_of_mem_spectrum_of_forall_trace_pow_eq_zero_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ k : ℕ, 1 < k → trace (A ^ k) = 0)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    μ = 0 := by
  have hpow2 :=
    forall_trace_pow_pow_eq_zero_of_forall_trace_pow_eq_zero_of_one_lt A h 2 (by omega)
  have hchar2 := charpoly_eq_X_pow_card_of_forall_trace_pow_eq_zero (A ^ 2) hpow2
  have hμ2root : IsRoot (A ^ 2).charpoly (μ ^ 2) :=
    mem_spectrum_iff_isRoot_charpoly.mp (spectrum.pow_mem_pow A 2 hμ)
  have hμpow : (μ ^ 2) ^ Fintype.card n = 0 := by
    rw [hchar2] at hμ2root
    simpa [IsRoot] using hμ2root
  have hμ2 : IsNilpotent (μ ^ 2) := ⟨Fintype.card n, hμpow⟩
  exact sq_eq_zero_iff.mp hμ2.eq_zero

/-- If `tr(A ^ N) = 0` for every `N > 1`, then
`charpoly A = X ^ n`.

This exact characteristic-polynomial form extends the conclusion used in
arXiv:1703.09188, line 410, from vanishing at every positive exponent to the
weaker hypothesis of vanishing only above one. It assumes no positivity,
normality, or diagonalizability. -/
theorem charpoly_eq_X_pow_card_of_forall_trace_pow_eq_zero_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ N : ℕ, 1 < N → trace (A ^ N) = 0) :
    A.charpoly = X ^ Fintype.card n := by
  classical
  let r := A.charpoly.roots
  have hr_card : r.card = Fintype.card n := by
    rw [← Matrix.charpoly_natDegree_eq_dim A]
    exact (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots.symm
  have hr_all_zero : ∀ z ∈ r, z = 0 := by
    intro z hz
    have hzroot : IsRoot A.charpoly z :=
      (Polynomial.mem_roots (A.charpoly_monic.ne_zero)).mp (by simpa [r] using hz)
    exact eq_zero_of_mem_spectrum_of_forall_trace_pow_eq_zero_of_one_lt A h
      (mem_spectrum_iff_isRoot_charpoly.mpr hzroot)
  have hr : r = Multiset.replicate (Fintype.card n) 0 :=
    Multiset.eq_replicate.mpr ⟨hr_card, hr_all_zero⟩
  rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic]
  rw [show A.charpoly.roots = r from rfl, hr]
  simp [Multiset.map_replicate, Multiset.prod_replicate]

/-- **Shifted zero trace powers force nilpotence.**

If `tr(A ^ N) = 0` for every `N > 1`, then `A` is nilpotent. This is a
stronger generalization of the matrix implication in arXiv:1703.09188,
line 410: the source supplies vanishing for every `N ≥ 1`, whereas this theorem
assumes only the exponents above one. The proof uses the exact characteristic
polynomial and Cayley--Hamilton and assumes no positivity, normality, or
diagonalizability. -/
theorem isNilpotent_of_forall_trace_pow_eq_zero_of_one_lt
    (A : Matrix n n ℂ)
    (h : ∀ N : ℕ, 1 < N → trace (A ^ N) = 0) :
    IsNilpotent A := by
  refine ⟨Fintype.card n, ?_⟩
  have hCH := A.aeval_self_charpoly
  rw [charpoly_eq_X_pow_card_of_forall_trace_pow_eq_zero_of_one_lt A h] at hCH
  simpa using hCH

end Matrix

section

open scoped Matrix Kronecker

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A complex square matrix whose powers of exponent at least two all have trace one has trace
one. The matrix `X - X²` has vanishing traces of its powers of exponent at least two, hence is
nilpotent, so `tr X = tr X² = 1`.

Source context: arXiv:1703.09188, MPU unitarity at lengths `N = 2, 3, …`, lines 319--335. -/
theorem trace_eq_one_of_forall_trace_pow_eq_one_of_one_lt (X : Matrix n n ℂ)
    (h : ∀ N : ℕ, 1 < N → trace (X ^ N) = 1) : trace X = 1 := by
  set Z := X - X ^ 2 with hZ
  have hpow : ∀ N : ℕ, 1 < N → trace (Z ^ N) = 0 := by
    intro N hN
    have hZ' : Z = X * (1 - X) := by rw [hZ, Matrix.mul_sub, Matrix.mul_one, sq]
    have hc : Commute X (1 - X) := (Commute.one_right X).sub_right (Commute.refl X)
    have hexp : (1 - X) ^ N = ∑ m ∈ Finset.range (N + 1),
        ((-1 : ℂ) ^ m * (N.choose m : ℂ)) • X ^ m := by
      rw [sub_eq_neg_add, ((Commute.one_right X).neg_left).add_pow]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [one_pow, Matrix.mul_one, ← neg_one_smul ℂ X, smul_pow, ← Nat.cast_comm,
        ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm (N.choose m : ℂ)]
    rw [hZ', hc.mul_pow, hexp, Finset.mul_sum, trace_sum]
    have hterm : ∀ m ∈ Finset.range (N + 1),
        trace (X ^ N * (((-1 : ℂ) ^ m * (N.choose m : ℂ)) • X ^ m)) =
          (-1 : ℂ) ^ m * (N.choose m : ℂ) := by
      intro m _
      rw [Matrix.mul_smul, trace_smul, ← pow_add, h (N + m) (by omega), smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl hterm]
    have := (Commute.one_right (-1 : ℂ)).add_pow N
    rw [neg_add_cancel, zero_pow (by omega)] at this
    rw [this]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [one_pow, mul_one]
  have hnil := isNilpotent_of_forall_trace_pow_eq_zero_of_one_lt Z hpow
  have h0 := (isNilpotent_trace_of_isNilpotent hnil).eq_zero
  rw [hZ, trace_sub, h 2 (by norm_num), sub_eq_zero] at h0
  exact h0

end Matrix

end
