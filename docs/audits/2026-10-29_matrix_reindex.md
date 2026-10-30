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

The local validation did not include a full-library build, whole-blueprint
compiled declaration check, PDF rendering, or TNLean rebuild.

## Independent review

A separate native subagent reviewed commit
`d035187edd439976fe1816e456d31e4de1f85a60` read-only and returned **PASS**,
with no semantic or regression defects. Its independent strict Lean fixture
checked non-involutive order-three/order-four relabellings on `Fin 3 × Fin 4`,
literal inverse indices and whole-matrix identities for both coefficient
orientations, multiplicativity, adjoints, and TNLean's actual
`finProdFinEquiv` compatibility call. It also reran the committed nine-name
axiom fixture successfully.

The reviewer checked the actual Schumacher--Werner source in TNLean's
`Papers/quant-ph_0405174/qca.tex`, lines 1137–1169 and 1218–1226; the
coefficient convention agrees. The GNVW source was not directly checked.
Hosted CI and draft-publication status are recorded on the pull request.
