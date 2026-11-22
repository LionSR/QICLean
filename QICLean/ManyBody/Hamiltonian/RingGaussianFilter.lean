/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.RingPropagation
import QICLean.ManyBody.Hamiltonian.GaussianFilterLocality
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Hamiltonian.NegativeFrequency

/-!
# Lieb–Robinson bound and Gaussian filters for translation-invariant interactions on the ring

Let `H_N` be the Hamiltonian of the translation-invariant interaction on the ring of `N`
sites of a Hermitian two-site operator `h` of norm at most one. Its Heisenberg evolution
satisfies the Lieb–Robinson bound of the ring with velocity `8 e^a`. This bound is the
short-time input of two filtering estimates, uniform in `N` and in the dimension of the sites,
with any ground energy and without frustration freedom:

* the Gaussian average `W_tilde` of `e^{itH_N} A e^{-itH_N}` nearly commutes with an operator
  `B` supported away from `A`; for the parameter `q = ℓ Δ / (16 e)` the error decays
  exponentially in `ℓ ≤ d(X, Y)`;
* the regularized negative-frequency part of `A` nearly commutes with `B`, uniformly in the
  regularizer.

A symmetric Gaussian filter by itself does not isolate the positive-energy part of an ordinary
connected correlation, and these estimates are not clustering statements.

Moved from TNLean at commit `49b78ed821` (Apache-2.0): the translation-invariant bound from
`TNLean/MPS/Preparation/FiniteRingLiebRobinson.lean`, the Gaussian filter estimates from
`TNLean/MPS/Preparation/FiniteRingGaussianFilter.lean`, and the negative-frequency estimate
from `TNLean/MPS/Preparation/FiniteRingNegativeFrequencyLocality.lean`. Changes: namespace
`ManyBody.Interaction` in place of the namespace of TNLean's tensors; the sites carry any finite
type in place of `Fin d`.

## Main results

* `ManyBody.Interaction.norm_hamiltonian_translationInvariant_commutator_le_exp_abs_of_disjoint`
  — the Lieb–Robinson bound of a translation-invariant interaction on the ring.
* `ManyBody.Interaction.norm_gaussianFilteredTerm_hamiltonian_translationInvariant_commutator_le`
  and its variant `..._le_exp` — locality of the Gaussian-filtered operator.
* `ManyBody.Interaction.norm_negativeFrequency_hamiltonian_translationInvariant_commutator_le`
  — locality of the regularized negative-frequency operator.

## References

* Hastings–Koma, arXiv:math-ph/0507008, Section 3 and Appendix A, Theorem A.2.
* Hastings, arXiv:cond-mat/0508554v3, equation `lbnd`, lines 266–283, proved at
  lines 1419–1456: short-time propagation plus a Gaussian tail.
* Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F, lines 929–953, where these estimates
  enter the argument from a physical gap.
-/

namespace ManyBody

namespace Interaction

open NormedSpace GaussianFilter
open scoped Matrix.Norms.L2Operator NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] {N : ℕ} [NeZero N]

/-- **The Lieb–Robinson bound of a translation-invariant interaction on the ring.** For a
Hermitian two-site operator `h` of norm at most one and `H_N` its translation-invariant
Hamiltonian on the ring of `N` sites (zero for `N = 1`),
`‖[e^{itH_N} A e^{-itH_N}, B]‖ ≤ 2 ‖A‖ ‖B‖ |X| e^{-a d(X, Y)} (e^{8 e^a |t|} - 1)` for `A`, `B`
supported on disjoint nonempty sets `X`, `Y`, every `a ≥ 0` and every time `t`. The bound is
uniform in `N` and in the dimension of the sites, with any ground energy. Hastings–Koma,
arXiv:math-ph/0507008, Appendix A. -/
theorem norm_hamiltonian_translationInvariant_commutator_le_exp_abs_of_disjoint
    (h : Matrix (Fin 2 → α) (Fin 2 → α) ℂ) (hHerm : h.IsHermitian) (hNorm : ‖h‖ ≤ 1)
    (A B : Matrix (Fin N → α) (Fin N → α) ℂ)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ supportedOperators (fun _ ↦ α) X)
    (hB : B ∈ supportedOperators (fun _ ↦ α) Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    ‖(exp (t • (Complex.I • (translationInvariant N h).hamiltonian)) * A *
        exp ((-t) • (Complex.I • (translationInvariant N h).hamiltonian))) *
          B -
      B * (exp (t • (Complex.I • (translationInvariant N h).hamiltonian)) *
        A * exp ((-t) • (Complex.I • (translationInvariant N h).hamiltonian)))‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card *
        Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
        (Real.exp ((8 * Real.exp a) * |t|) - 1) :=
  norm_heisenberg_commutator_le_ringSupportDistance
    (fun j => (translationInvariant N h).term j)
    (isHermitian_translationInvariant_term hHerm)
    (fun j => image_range_two_add j ▸ (translationInvariant N h).mem j)
    (fun j => (norm_translationInvariant_term_le h j).trans hNorm)
    A B X Y hX hY hA hB hXY a ha t

/-- **Locality of the Gaussian-filtered operator on the ring.** Gaussian averaging of the
Heisenberg evolution under the translation-invariant Hamiltonian `H_N` gives the sum of the
short-time propagation error and the Gaussian tail:
`‖[W_tilde, B]‖ ≤ 2 ‖A‖ ‖B‖ |X| e^{-a d(X, Y)} (e^{8 e^a T} - 1) + 2 ‖A‖ ‖B‖ e^{-(TΔ)²/(2q)}`,
uniformly in `N` and in the dimension of the sites. Hastings, arXiv:cond-mat/0508554v3,
equation `lbnd`, lines 266–283, for the interactions of the ring. -/
theorem norm_gaussianFilteredTerm_hamiltonian_translationInvariant_commutator_le
    (h : Matrix (Fin 2 → α) (Fin 2 → α) ℂ) (hHerm : h.IsHermitian) (hNorm : ‖h‖ ≤ 1)
    (A B : Matrix (Fin N → α) (Fin N → α) ℂ)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ supportedOperators (fun _ ↦ α) X)
    (hB : B ∈ supportedOperators (fun _ ↦ α) Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (a : ℝ) (ha : 0 ≤ a) {q Δ T : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T) :
    ‖gaussianFilteredTerm q Δ (translationInvariant N h).hamiltonian A * B -
        B * gaussianFilteredTerm q Δ (translationInvariant N h).hamiltonian A‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card *
          Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
          (Real.exp ((8 * Real.exp a) * T) - 1) +
        2 * ‖A‖ * ‖B‖ * Real.exp (-(T * Δ) ^ 2 / (2 * q)) := by
  have hExp : 0 ≤ Real.exp ((8 * Real.exp a) * T) - 1 := by
    apply sub_nonneg.mpr
    exact Real.one_le_exp (by positivity)
  refine norm_commutator_gaussianFilteredTerm_le hq
    (isHermitian_hamiltonian (isHermitian_translationInvariant_term hHerm)) A B hT
    (by positivity) ?_
  intro t ht
  have htAbs : |t| ≤ T := abs_le.mpr ht
  change ‖(exp (t • (Complex.I • (translationInvariant N h).hamiltonian)) *
      A * exp ((-t) • (Complex.I • (translationInvariant N h).hamiltonian))) * B -
    B * (exp (t • (Complex.I • (translationInvariant N h).hamiltonian)) *
      A * exp ((-t) • (Complex.I • (translationInvariant N h).hamiltonian)))‖ ≤ _
  refine (norm_hamiltonian_translationInvariant_commutator_le_exp_abs_of_disjoint h hHerm hNorm
    A B X Y hX hY hA hB hXY a ha t).trans ?_
  gcongr

/-- **Exponential locality of the Gaussian-filtered operator on the ring.** For
`0 < ℓ ≤ d(X, Y)`, `Δ > 0` and the parameter `q = ℓ Δ / (16 e)`, the commutator of the
Gaussian-filtered operator with `B` is at most
`2 ‖A‖ ‖B‖ |X| e^{-ℓ/2} + 2 ‖A‖ ‖B‖ e^{-ℓΔ/(32 e)}`. This is the balance of the short time and
the tail in Hastings, arXiv:cond-mat/0508554v3, equation `lbnd`, with the velocity `8 e` of the
ring. It bounds a filtered commutator, not an ordinary connected correlation. -/
theorem norm_gaussianFilteredTerm_hamiltonian_translationInvariant_commutator_le_exp
    (h : Matrix (Fin 2 → α) (Fin 2 → α) ℂ) (hHerm : h.IsHermitian) (hNorm : ‖h‖ ≤ 1)
    (A B : Matrix (Fin N → α) (Fin N → α) ℂ)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ supportedOperators (fun _ ↦ α) X)
    (hB : B ∈ supportedOperators (fun _ ↦ α) Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    {ℓ Δ : ℝ} (hℓ : 0 < ℓ) (hΔ : 0 < Δ)
    (hDist : ℓ ≤ ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) :
    let q := ℓ / (16 * Real.exp 1) * Δ
    ‖gaussianFilteredTerm q Δ (translationInvariant N h).hamiltonian A * B -
        B * gaussianFilteredTerm q Δ (translationInvariant N h).hamiltonian A‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card * Real.exp (-ℓ / 2) +
        2 * ‖A‖ * ‖B‖ * Real.exp (-ℓ * Δ / (32 * Real.exp 1)) := by
  let T := ℓ / (16 * Real.exp 1)
  have hT : 0 < T := div_pos hℓ (by positivity)
  have hTime : (8 * Real.exp (1 : ℝ)) * T = ℓ / 2 := by
    dsimp [T]
    field_simp [ne_of_gt (Real.exp_pos (1 : ℝ))]
    ring
  have hTail : -(T * Δ) ^ 2 / (2 * (T * Δ)) =
      -ℓ * Δ / (32 * Real.exp 1) := by
    dsimp [T]
    field_simp [ne_of_gt hℓ, ne_of_gt hΔ, ne_of_gt (Real.exp_pos (1 : ℝ))]
    ring
  refine (norm_gaussianFilteredTerm_hamiltonian_translationInvariant_commutator_le h hHerm hNorm
    A B X Y hX hY hA hB hXY 1 (by norm_num) (mul_nonneg hT.le hΔ.le) hT.le).trans ?_
  rw [hTime, hTail]
  refine add_le_add ?_ le_rfl
  calc
    2 * ‖A‖ * ‖B‖ * X.card *
          Real.exp (-1 * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
          (Real.exp (ℓ / 2) - 1) ≤
        2 * ‖A‖ * ‖B‖ * X.card *
          Real.exp (-1 * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
          Real.exp (ℓ / 2) := by gcongr; linarith
    _ = 2 * ‖A‖ * ‖B‖ * X.card *
        Real.exp (-1 * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY +
          ℓ / 2) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ 2 * ‖A‖ * ‖B‖ * X.card * Real.exp (-ℓ / 2) := by
      gcongr
      linarith

/-- **Locality of the regularized negative-frequency operator on the ring.** For the
translation-invariant Hamiltonian `H_N`, the commutator of the Gaussian negative-frequency
operator of `A` with `B` is bounded with `C = 2 ‖A‖ ‖B‖ |X| e^{-a d(X, Y)}` and `v = 8 e^a`,
uniformly in the regularizer `ε > 0`, in `N` and in the dimension of the sites; no propagation
or correlation estimate is assumed. Hastings–Koma, arXiv:math-ph/0507008, Section 3 and
Appendix A, for the interactions of the ring. -/
theorem norm_negativeFrequency_hamiltonian_translationInvariant_commutator_le
    (h : Matrix (Fin 2 → α) (Fin 2 → α) ℂ) (hHerm : h.IsHermitian) (hNorm : ‖h‖ ≤ 1)
    (A B : Matrix (Fin N → α) (Fin N → α) ℂ)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ supportedOperators (fun _ ↦ α) X)
    (hB : B ∈ supportedOperators (fun _ ↦ α) Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (s : ℝ≥0) {ε T a : ℝ} (hε : 0 < ε) (hT : 0 < T) (ha : 0 ≤ a) :
    ‖gaussianNegativeFrequencyOperator s ε (translationInvariant N h).hamiltonian A * B -
        B * gaussianNegativeFrequencyOperator s ε (translationInvariant N h).hamiltonian A‖ ≤
      kernel s⁻¹ 0 *
        ((2 * ‖A‖ * ‖B‖ * X.card *
            Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) *
            (8 * Real.exp a) * Real.exp ((8 * Real.exp a) * T) +
          (2 * ‖A‖ * ‖B‖ / T) * Real.exp (-T ^ 2 / (2 * (s : ℝ)))) := by
  apply norm_commutator_gaussianNegativeFrequencyOperator_le s
    (isHermitian_hamiltonian (isHermitian_translationInvariant_term hHerm))
    A B hε hT (by positivity) (by positivity)
  intro t
  exact norm_hamiltonian_translationInvariant_commutator_le_exp_abs_of_disjoint h hHerm hNorm
    A B X Y hX hY hA hB hXY a ha t

end Interaction

end ManyBody
