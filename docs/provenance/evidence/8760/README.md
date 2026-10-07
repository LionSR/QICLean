# Issue 8760 exact-source verification

Source repository: `LionSR/QICLean`.
Published immutable source revision: `075e8f562c0efd7b5d603b8e75f639c8deacada0`.

Each recorded module was checked by a real direct Lean invocation with the
package options, Mathlib standard linter set, warnings-as-errors, one thread and
a 90-second timeout. The module logs contain actual invocation metadata and the
unmodified compiler output. The axiom log is the unmodified printed output for
all declarations in this repository's issue 8760 shard. All dependencies are
limited to `propext`, `Classical.choice`, and `Quot.sound`.

This is strict direct elaboration evidence, not a claim that a linter-bearing
Lake build, whole-repository CI, or full blueprint `checkdecls` has completed.
Those gates are registered in CI. TNLean's consumer additionally requires the
reviewed QICLean companion revision to be pinned before publication is complete.

Validation reused only artifacts with matching recorded source/artifact hashes
and an unchanged Lean/Mathlib/package-option configuration. Missing project
prerequisites were compiled serially. No Mathlib source build, forged cache trace,
custom axiom, proof hole, or native kernel bypass was used.

QIC source revision used by the private integration overlay: `075e8f562c0efd7b5d603b8e75f639c8deacada0`.
TN model base: `0db97621a2733f87a752df63c8bb85b439fdd845`.

The command logs were captured while checking local source snapshot
`b6aea0fd40759a74ed4cc9f7b4006139dde936f8`. The separately published snapshot has exactly the same
Git tree, `bba70edde76970ab9e1f6e6a47e2c45b1a156c23`; see the explicit tree attestation.
`dependency-audit.json` is the initial source/artifact reuse audit;
`dependency-builds.json` records the subsequent successful checks of all 30
project prerequisites whose reusable artifacts were initially missing.
