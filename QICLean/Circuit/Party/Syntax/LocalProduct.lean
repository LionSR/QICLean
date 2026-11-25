/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Syntax.Local

/-!
# Mixed products of local party circuits

The operator of a party circuit without gates is the Kronecker product of its party operations.
Hence the product of the operator of one such circuit, the operator of a second one on the input
system, and the adjoint of the operator of a third one is the Kronecker product over the parties
of the corresponding products of party operations. The three circuits are arbitrary and their
party operations may vanish.

## Main results

* `QuantumCircuit.Party.PartyCircuit.op_mul_op_mul_conjTranspose_op_eq_piKronecker`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Theorem 5.2, `04-compression.tex`,
  lines 409–434 and 565–588.
-/

open Matrix ManyBody

namespace QuantumCircuit.Party.PartyCircuit

variable {P : Type} [DecidableEq P] [Fintype P]
  {G : Finset P → (P → Type) → (P → Type) → Type 1} [GateFamily G] [GateFamily.UniqueOutcome G]
  {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]

/-- **A mixed product of local circuits factors over the parties**: for circuits `w`, `v` from
`X` to `Y` and `u` on `X`, all without gates, `w u v†` is the Kronecker product over the parties
of the products of their party operations. No factorization is assumed. Source: Theorem 5.2,
`04-compression.tex`, lines 409–434 and 565–588. -/
theorem op_mul_op_mul_conjTranspose_op_eq_piKronecker (ev : Interpretation G)
    (w v : PartyCircuit G X Y) (u : PartyCircuit G X X)
    (hw : w.IsLocal) (hv : v.IsLocal) (hu : u.IsLocal) :
    w.op ev * u.op ev * (v.op ev)ᴴ =
      piKronecker fun p ↦ w.partyOp p * u.partyOp p * (v.partyOp p)ᴴ := by
  rw [op_eq_piKronecker_partyOp ev w hw, op_eq_piKronecker_partyOp ev u hu,
    op_eq_piKronecker_partyOp ev v hv, conjTranspose_piKronecker, piKronecker_mul,
    piKronecker_mul]

end QuantumCircuit.Party.PartyCircuit
