# Matrix reindex consolidation

Addresses [QICLean #465](https://github.com/LionSR/QICLean/issues/465).

`Matrix.reindexStarAlgEquiv` in `Algebra/MatrixReindex.lean` combines Mathlib's
`Matrix.reindexAlgEquiv` and `Matrix.conjTranspose_reindex`. Its evaluation,
inverse, and composition lemmas are the only additional equivalence API.
The module imports only Mathlib; it imports no Skolem--Noether, functional
calculus, quantum-channel, or TNLean module.
Mathlib's conjugate-transpose import does transitively load
`Mathlib.Tactic.ContinuousFunctionalCalculus`, a meta-only tactic module;
the recursive import closure contains no functional-calculus mathematics.

The previous `Matrix.matrixReindexStarAlgEquiv` implementation in
`Algebra/SkolemNoetherUnitary.lean` is replaced by a definition abbreviation.
Its QICLean consumer now calls the canonical name. The abbreviation preserves
the actual TNLean consumer in `TNLean/Algebra/CommutingStarSubalgebraProduct.lean`
(TNLean checkout `3af48c1843059427e4ab3eb84caf9539ac4efa91`).

The removed declarations `Matrix.reindexStarAlgHom` and
`Matrix.reindexStarAlgHom_apply` were used only within
`Analysis/CfcConjugation.lean`; searches of QICLean, its tests and blueprint,
and TNLean's source and blueprint found no other consumers. Their replacements
are `(Matrix.reindexStarAlgEquiv e).toStarAlgHom` and the canonical evaluation
lemma together with Mathlib's homomorphism evaluation. The CFC theorem now
uses that derived homomorphism directly. No compatibility homomorphism or
second implementation is retained.
This removal uses the repository-local pass-through exception: both names
designated the reindexing step now written directly in the CFC proof, and no
blueprint tag cites either removed declaration.

The product-reindex identities live beside their operations:
`Matrix.bipartiteSlice_reindex_prod` in `Channel/TensorMap.lean` and
`Matrix.operatorBlock_reindex_prod` in `Algebra/OperatorBlock.lean`. The former
keeps the first tensor factor, and the latter keeps the second. Both use inverse
equivalences on the fixed indices. Neither identity requires finiteness;
the operator-block identity also permits arbitrary coefficient types.

PR #506 removed an unused former `MatrixReindex` module. This change restores
only the module name: the new canonical equivalence has live Skolem--Noether
and CFC consumers, and none of the retired unused wrappers is reintroduced.

## Validation

- Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`;
  all dependency revisions match the unchanged manifest. The environment's
  completed `lake exe cache get` supplied the prebuilt Mathlib artifacts.
- Targeted build of the five production modules passed. Only twelve QICLean
  modules were compiled; all Mathlib tasks used their cached artifacts.
- Serial direct elaboration of those five modules and
  `QICLeanTest/MatrixReindexAxioms.lean` passed with strict implicit variables,
  the standard Mathlib linter set, and warnings treated as errors.
- All nine declaration guards passed, including both migrated consumer theorems.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur; the operator-block
  identity needs only `propext` and `Quot.sound`.
- Targeted Mathlib text-style lint, generated-import checks, source-aware
  blueprint synchronization and new-declaration coverage, reader-facing prose,
  recursive import checks, and whitespace/proof-integrity checks passed.
- The repository's Lake-option style-loader code hit a Lean interpreter
  assertion under direct `lean --run`. The targeted text-style check instead
  called the same Mathlib linter directly, with its default style options and
  the repository exceptions, and passed.

No full-library build, whole-blueprint compiled declaration check, PDF rendering,
TNLean rebuild, push, or pull-request publication was performed.
