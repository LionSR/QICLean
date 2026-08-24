/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Irreducible.Growth.Exponential
import QICLean.Channel.Irreducible.Growth.OrthogonalTrace

/-!
# Growth conditions for irreducible positive maps (Wolf Theorem 6.2, items 2–4)

This module collects the three positivity characterizations of an
irreducible positive map $E$ on $M_D(\mathbb{C})$ from Wolf's Theorem 6.2.
Item 2 is formalized here under Wolf's positivity hypothesis; the current
interfaces for items 3 and 4 retain their earlier complete-positivity
specializations.

* **Item 2** — Growth condition: $(\mathrm{id} + E)^{D - 1}(A) > 0$ for every
  nonzero PSD matrix $A$, together with the underlying structural lemma on the
  support projection and strict kernel decrease.
* **Item 3** — Exponential condition: $\exp(tE)(A) > 0$ for every $t > 0$ and
  every nonzero PSD $A$, and its logical equivalence with irreducibility.
* **Item 4** — Orthogonal trace condition: every pair of nonzero PSD matrices
  $A$, $B$ with $\operatorname{tr}(BA) = 0$ admits an iterate $E^t(A)$ with
  $1 \leq t \leq D - 1$ and $\operatorname{tr}(B \cdot E^t(A)) > 0$.

The proof is split across four supporting sub-modules for readability:

* `QICLean.Channel.Irreducible.Growth.Preservation` — preservation lemmas for
  `id + E` and `E^n` under positivity, plus the binomial expansion of
  `(id + E)^n`.
* `QICLean.Channel.Irreducible.Growth.OneStep` — the structural
  `posDef_of_ker_subset_irreducible` lemma via the support projection.
* `QICLean.Channel.Irreducible.Growth.KernelDescent` — kernel-dimension induction
  yielding `growth_posDef_of_irreducible`.
* `QICLean.Channel.Irreducible.Growth.OrthogonalTrace` — binomial expansion of
  the growth witness producing `orthogonal_trace_pos_of_irreducible_cp`.
* `QICLean.Channel.Irreducible.Growth.Exponential` — normed-algebra setup and
  `exp_posDef_of_irreducible_cp`, `irreducible_iff_exp_posDef_forall`.

## Main statements

* `posDef_of_ker_subset_irreducible` — support-projection structural lemma.
* `idPlusE_posSemidef`, `idPlusE_ne_zero`, `idPlusE_posDef` — preservation of
  PSD / nonzero / PosDef by `id + E`.
* `mulVecLin_ker_idPlusE_lt_of_not_posDef_of_positive` — strict kernel decrease.
* `growth_posDef_of_irreducible` — Wolf Theorem 6.2, item 2.
* `orthogonal_trace_pos_of_irreducible_cp` — Wolf Theorem 6.2, item 4.
* `exp_posDef_of_irreducible_cp`, `irreducible_iff_exp_posDef_forall` — Wolf
  Theorem 6.2, item 3.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2,
  Theorem 6.2][Wolf2012QChannels]

## Tags

irreducible, positive map, growth condition, exponential, Wolf theorem
-/
