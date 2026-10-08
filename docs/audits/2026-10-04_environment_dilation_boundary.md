# Shared finite-environment dilation boundary

The circuit/preparation compiler in LionSR/TNLean#8640 needs finite-dimensional
channel dilation and deferred partial traces. These statements have no spatial
or tensor-network assumptions and belong in QICLean.

## Reused primitive and compatibility

`Matrix.fixedEnvEmbedding` already existed in
`Channel/KoashiImoto/MarkovDilation/Basic.lean`. It is moved, with the same definition
and public name, into `Channel/EnvironmentEmbedding.lean`. Its existing generic
isometry, multiplication, naturality and unitary-extension proofs move with it and
become reusable public declarations:

- `Matrix.fixedEnvEmbedding_conjTranspose_mul_self`
- `Matrix.mul_fixedEnvEmbedding_apply`
- `Matrix.fixedEnvEmbedding_mul`
- `Matrix.exists_unitary_mul_fixedEnvEmbedding_eq`

The old Markov-dilation module imports this narrow interface. The established
`Matrix.firstEnvEmbedding` in `Channel/OpenSystem.lean` now uses the same primitive;
its defining matrix is unchanged and its isometry theorem uses the shared proof.
No public declaration is removed or renamed.

## New ownership

`Channel/EnvironmentDilation.lean` owns pure-basis initialization, column-block Kraus
maps, Choi-bounded retained-system unitary dilation, basis reindexing, and reference
preservation. The environment size depends on the system dimension, not the length
of a supplied redundant Kraus family.

`Channel/DeferredEnvironmentTrace.lean` owns the composition identity with distinct
fresh environments. The intermediate system and old environment may be correlated.
Its product-index permutations are mathematical coordinates, not assertions about
free spatial operations.

TNLean owns wire/site layouts, physical-port preservation, supported onsite placement,
and communication-depth accounting. QICLean imports no TNLean module and does not
claim a spatial circuit theorem or the source QCcc phase classification.

## Regression contract

`QICLeanTest/EnvironmentDilation.lean` checks a prescribed nonzero environment basis,
a qutrit channel with a nine-dimensional environment, arbitrary external references,
the zero-wire boundary, correlated intermediate operators, and the composed unitary.
Guarded axiom assertions require only `propext`, `Classical.choice`, and `Quot.sound`.
The PR workflow executes the suite strictly after the full library build.

The migrated Markov and open-system clients remain part of the root build. Narrow
local checks do not replace their exact-revision CI validation.
