/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Irreducible.Growth.Exponential
import QICLean.Channel.Irreducible.Growth.OrthogonalTrace
import Mathlib.Tactic.TFAE

/-!
# Growth conditions for irreducible positive maps (Wolf Theorem 6.2, items 2–4)

This module packages the four equivalent characterizations of an irreducible
positive map $E$ on $M_D(\mathbb{C})$ from Wolf's Theorem 6.2.  The headline
`wolf_theorem_6_2_tfae` has exactly the source's positive-map scope; the former
completely positive declarations remain as direct specializations.

* **Item 2** — Growth condition: $(\mathrm{id} + E)^{D - 1}(A) > 0$ for every
  nonzero PSD matrix $A$, together with the underlying structural lemma on the
  support projection and strict kernel decrease.
* **Item 3** — Exponential condition: $\exp(tE)(A) > 0$ for every $t > 0$ and
  every nonzero PSD $A$, and its logical equivalence with irreducibility.
* **Item 4** — Orthogonal trace condition: every pair of nonzero PSD matrices
  $A$, $B$ with $\operatorname{tr}(BA) = 0$ admits an iterate $E^t(A)$ with
  $1 \leq t \leq D - 1$ and $\operatorname{tr}(B \cdot E^t(A)) > 0$.

The proof is split across five supporting sub-modules for readability:

* `QICLean.Channel.Irreducible.Growth.Preservation` — preservation lemmas for
  `id + E` and `E^n` under positivity, plus the binomial expansion of
  `(id + E)^n`.
* `QICLean.Channel.Irreducible.Growth.OneStep` — the structural
  `posDef_of_ker_subset_irreducible` lemma via the support projection.
* `QICLean.Channel.Irreducible.Growth.KernelDescent` — kernel-dimension induction
  yielding `growth_posDef_of_irreducible`.
* `QICLean.Channel.Irreducible.Growth.OrthogonalTrace` — binomial expansion of
  the growth witness producing `orthogonal_trace_pos_of_irreducible`.
* `QICLean.Channel.Irreducible.Growth.Exponential` — normed-algebra setup and
  `exp_posDef_of_irreducible`,
  `irreducible_iff_exp_posDef_forall_of_positive`.

## Main statements

* `posDef_of_ker_subset_irreducible` — support-projection structural lemma.
* `idPlusE_posSemidef`, `idPlusE_ne_zero`, `idPlusE_posDef` — preservation of
  PSD / nonzero / PosDef by `id + E`.
* `mulVecLin_ker_idPlusE_lt_of_not_posDef_of_positive` — strict kernel decrease.
* `growth_posDef_of_irreducible` — Wolf Theorem 6.2, item 2.
* `exp_posDef_of_irreducible` — Wolf Theorem 6.2, item 3.
* `orthogonal_trace_pos_of_irreducible` — Wolf Theorem 6.2, item 4.
* `wolf_theorem_6_2_tfae` — all four source conditions are equivalent.
* The former completely positive declarations remain as direct specializations.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2,
  Theorem 6.2][Wolf2012QChannels]

## Tags

irreducible, positive map, growth condition, exponential, Wolf theorem
-/

open scoped Matrix ComplexOrder BigOperators

variable {D : ℕ}

/-- **Wolf Theorem 6.2 (irreducible positive maps).**  For a positive linear
map `E` on `M_D(ℂ)`, the following four source conditions are equivalent:

1. `E` has no nontrivial invariant projection;
2. `(id + E)^(D - 1) A` is positive definite for every nonzero `A ≥ 0`;
3. `exp(tE) A` is positive definite for every `t > 0` and nonzero `A ≥ 0`;
4. every orthogonal pair of nonzero positive semidefinite matrices `A, B`
   has positive trace overlap `tr(B E^t(A))` for some `1 ≤ t ≤ D - 1`.

The proof follows Wolf's implication graph
`(1) → (2) → (3) → (1)` and `(2) → (4) → (1)`.  Complete positivity is not
assumed. -/
theorem wolf_theorem_6_2_tfae
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : IsPositiveMap E) :
    List.TFAE [
      IsIrreducibleMap E,
      ∀ A : Matrix (Fin D) (Fin D) ℂ, A.PosSemidef → A ≠ 0 →
        ((((LinearMap.id : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) + E) ^ (D - 1)) A).PosDef,
      ∀ t : ℝ, 0 < t → ∀ A : Matrix (Fin D) (Fin D) ℂ, A.PosSemidef → A ≠ 0 →
        ((NormedSpace.exp ((endEquiv (D := D)) ((t : ℂ) • E))) A).PosDef,
      ∀ A B : Matrix (Fin D) (Fin D) ℂ,
        A.PosSemidef → A ≠ 0 → B.PosSemidef → B ≠ 0 →
        Matrix.trace (B * A) = 0 →
        ∃ t : ℕ, 0 < t ∧ t ≤ D - 1 ∧ 0 < Matrix.trace (B * ((E ^ t) A))] := by
  tfae_have h12 : 1 → 2 := by
    intro hIrr A hA hA_ne
    exact growth_posDef_of_irreducible E hE hIrr A hA hA_ne
  tfae_have h23 : 2 → 3 := by
    intro hGrowth t ht A hA hA_ne
    exact exp_posDef_of_growth E hE A hA hA_ne (hGrowth A hA hA_ne) ht
  tfae_have h31 : 3 → 1 := by
    exact irreducible_of_exp_posDef_forall E
  tfae_have h24 : 2 → 4 := by
    intro hGrowth A B hA hA_ne hB hB_ne horth
    exact orthogonal_trace_pos_of_growth E hE A B hA
      (hGrowth A hA hA_ne) hB hB_ne horth
  tfae_have h41 : 4 → 1 := by
    exact irreducible_of_orthogonal_trace_pos_forall E
  tfae_finish
