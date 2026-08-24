/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.LorentzNormalForm.Basic
import QICLean.Channel.LorentzNormalForm.CanonicalQubitChannels
import QICLean.Channel.LorentzNormalForm.Infimum
import QICLean.Channel.LorentzNormalForm.InvertibleFilter
import QICLean.Channel.LorentzNormalForm.NormalForm
import QICLean.Channel.LorentzNormalForm.PauliBlockTruncation
import QICLean.Channel.LorentzNormalForm.QubitNormalForm
import QICLean.Channel.LorentzNormalForm.SpinorAction
import QICLean.Channel.LorentzNormalForm.SpinorCover
import QICLean.Channel.LorentzNormalForm.SpinorExponential

/-!
# Lorentz normal form for quantum channels (Wolf Section 2.4, Propositions 2.8–2.11)

Thin module assembling the normal-form development for quantum channels under
filtering operations from eight focused submodules.

* `QICLean.Channel.LorentzNormalForm.Basic` — SL-filtering operations, the
  doubly-stochastic predicates, and the shared Kronecker-conjugation and
  partial-trace identities.
* `QICLean.Channel.LorentzNormalForm.CanonicalQubitChannels` — the exact
  non-diagonal and singular qubit representatives, their Pauli-transfer
  action, and their Choi/Kraus ranks.
* `QICLean.Channel.LorentzNormalForm.Infimum` — the compactness/minimisation
  argument (Wolf Equation (2.36)): attainment of the infimum and the AM–GM
  optimality lemmas.
* `QICLean.Channel.LorentzNormalForm.InvertibleFilter` — the general
  invertible Kraus-rank-one filters used in Wolf Proposition 2.11, including
  their scalar/determinant-one decomposition.
* `QICLean.Channel.LorentzNormalForm.NormalForm` — Wolf Proposition 2.9, the
  generic normal form for CP maps with full Kraus rank, in square and
  rectangular forms.
* `QICLean.Channel.LorentzNormalForm.PauliBlockTruncation` — the valid forward
  implications of Wolf Proposition 2.10 for Pauli-block truncation.
* `QICLean.Channel.LorentzNormalForm.QubitNormalForm` — the Pauli-basis
  predicates for the qubit Lorentz normal form (Wolf Proposition 2.11;
  existence pending).
* `QICLean.Channel.LorentzNormalForm.SpinorAction` — the four-dimensional
  Hermitian congruence action of `SL(2,ℂ)` and its action on Pauli transfer
  matrices (Wolf Equations (2.41)--(2.43)).
* `QICLean.Channel.LorentzNormalForm.SpinorCover` — the spinor epimorphism
  `SL(2,ℂ) → SO⁺(1,3)`: the bundled homomorphism, the rotation-block
  reduction, the boost lift, and the exact two-point fibres (Wolf
  Equations (2.42)--(2.44)).
* `QICLean.Channel.LorentzNormalForm.SpinorExponential` — the boost and
  corrected-sign rotation exponential formulas in Wolf Equation (2.44).

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 2.4][Wolf2012QChannels]
-/
