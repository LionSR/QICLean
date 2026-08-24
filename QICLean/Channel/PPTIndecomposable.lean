/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.DecomposablePPT
import QICLean.Channel.PositiveMapDetection

/-!
# PPT entangled states yield indecomposable positive maps

This file proves the source-faithful easy direction of Wolf, Chapter 3,
Proposition 3.5: a PPT entangled density operator on
`ℂ^d ⊗ ℂ^{d'}` yields an indecomposable positive map
`T : M_d(ℂ) → M_{d'}(ℂ)`.

Wolf says this implication follows from Proposition 3.3. In the formalization,
the exact rectangular detector is Proposition 3.4:
`Matrix.exists_isNPositiveMap_tensorMapId_not_posSemidef` at `n = 1` produces
a positive map whose ampliation detects the entangled state. The contrapositive
of rectangular decomposable-PPT preservation then proves that this map is
indecomposable.

The reverse implication in Proposition 3.5 is not claimed here. The normalized
compact convex set of decomposable witnesses and the trace-adjointness of
first-factor partial transpose are formalized in
`QICLean.Channel.DecomposableWitness`. What remains is normalization of the
nonzero block-positive Choi witness and the separating-hyperplane argument
used in Lewenstein--Kraus--Cirac--Horodecki, arXiv:quant-ph/0005014v3,
Theorem 3.
The exact remaining boundary is recorded in
`docs/paper-gaps/wolf_prop3_5_reverse_implication.tex`.

## Main result

* `Matrix.exists_isIndecomposablePositiveMap_of_isPPT_not_isSeparable` -- a
  PPT entangled density operator yields a rectangular indecomposable positive
  map.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Proposition 3.5][Wolf2012QChannels]
* M. Lewenstein, B. Kraus, J. I. Cirac, and P. Horodecki,
  *Optimization of entanglement witnesses*, arXiv:quant-ph/0005014v3,
  Theorem 3.
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {d d' : ℕ}

/-- **PPT entanglement gives an indecomposable positive map (Wolf Proposition 3.5,
easy direction).** If `ρ` is a density operator on `ℂ^d ⊗ ℂ^{d'}`, has positive
first-factor partial transpose, and is not separable, then there is an
indecomposable positive map `T : M_d(ℂ) → M_{d'}(ℂ)`.

The map is the `n = 1` detector from the rectangular positive-map criterion
(Wolf Proposition 3.4). One-positivity is positivity, and decomposable maps
preserve positivity on PPT states, so a map detected by `ρ` cannot be
decomposable. -/
theorem exists_isIndecomposablePositiveMap_of_isPPT_not_isSeparable [NeZero d']
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) (hPPT : IsPPT ρ)
    (hentangled : ¬ IsSeparable ρ) :
    ∃ T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ,
      IsIndecomposablePositiveMap T := by
  rw [← hasSchmidtNumberLE_one_iff_isSeparable] at hentangled
  obtain ⟨T, hT, hneg⟩ :=
    exists_isNPositiveMap_tensorMapId_not_posSemidef 1 hρ.isHermitian hρtr hentangled
  refine ⟨T, ?_⟩
  exact (isNPositiveMap_one_iff_isPositiveMap.mp hT)
    |>.isIndecomposablePositiveMap_of_isPPT_not_tensorMapId_posSemidef hρ hPPT hneg

end Matrix
