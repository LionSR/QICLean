# Shared elementary operator Schmidt rank bounds

`Algebra/OperatorSchmidtProducts.lean` contains the elementary bound
$\operatorname{OSR}(A\otimes B)\le1$ and its identity specialization.
The former is the existing private proof from
`OneMarkerWeightedSchmidtRank.lean`, relocated with the precise public
name `operatorSchmidtRank_kronecker_le_one`. Its one-term decomposition
proof is unchanged. The existing one-marker consumer imports this small
leaf and uses the shared result; the private duplicate and old private
name are removed. `OperatorSchmidtBounds.lean` is unchanged.

The identity and elementary-tensor statements use only `Finite` on the
second local index type, and include empty local index spaces. The
identity statement additionally requires decidable equality for its
matrix identities. These are algebraic statements without support,
spectral, positivity or state hypotheses.

The actual new module and modified consumer passed strict private checks
in 2.18 and 2.48 seconds respectively, against fully checked QIC source
`ec3434f7d6fbdfc5318dc55934feb9532e239b81` and the exact matching package
of fully checked TN mathematical source
`28e38efedb8621056c907c8ad20e1edd24003a20`, documentation successor
`7f87bdc8f1b2354be4950ad515dedda7ee9bec96`.
A temporary imported foundation audit covers both new public results
and the modified consumer, as part of eleven inspected public results,
and found only `propext`, `Classical.choice`, and `Quot.sound`.
The two new declarations are included in the existing algebraic-rank
blueprint entry. No new chapter registration or aggregator is needed.

All selected provider sources and ordinary objects and own private
objects were guarded. Outputs are confined to a temporary namespace;
no provider source, cache or build artifact was edited or copied,
no Mathlib source was built, and no ordinary build was queued.
Ordinary build and compiled blueprint verification remain integration
gates. This auxiliary supports the corrected physical ALVV rank bound;
it does not assert the false printed additive constant.
