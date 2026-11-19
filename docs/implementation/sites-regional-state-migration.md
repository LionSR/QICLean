# Regional states over finite basis types

This continuation of #1051 was originally developed on main at
`e9cc1cc6cd52c6dfc27d7b3aab4b1ba39ea7ed19`, after the core and expectation
changes in #1058 and #1059. It leaves their signatures unchanged.

For PR review, the validated work was reapplied to main
`4fd4962204b7abdd012d4d0495d52d9d77003688` on a separate branch, preserving
`codex/1051-sites-migration` at `9cddef90`. Main’s Dynamics and commutant
additions (#1063 and #1064) are preserved. The only conflicts were the Sites
architecture description and the appended blueprint sections; both contributions
were retained. No overlapping open regional-state PR was found.

## Scope

- `ManyBody/Sites/RegionState`: cut vectors, unnormalized regional pure states,
  positivity, trace, regional entropy, expectations, the commuting-filter trace
  argument, and consistency of reduction on a disjoint union.
- `ManyBody/Sites/RegionUnion`: configurations of disjoint regions and placement
  of a tensor product as the product of the two placements.
- `ManyBody/Sites/Relabel`: site and basis bijections, vector transport, norm
  preservation, regional-state covariance, and entropy invariance.
- `Algebra/PureStateExpectation`: the site-independent trace-pairing identity
  previously proved in `Entropy/FilterMoment`, and separation of matrices
  by their trace pairings from `Entropy/SchmidtPinning`.

All Sites statements use an unbundled family of finite basis types. They allow
empty basis types and unnormalized vectors. The supported-observable trace
argument uses membership in `supportedOperators` and no reference configuration.
The placement product and conjugation statements retain their actual matrix
products and inverses; no commutation, normalization, or positivity hypotheses
have been added to ease the proofs.

## Existing consumers

`Entropy.LocalLift`, `RegionCovariance`, `RegionUnion`, `RegionEntropy`,
`FilterMoment`, `FilterOptimizer`, and `SchmidtPinning` retain their existing declaration names and
signatures. Definitions become reducible specializations, and theorem bodies
call the generic results. In particular the reference configuration in the old
supported-observable trace theorem remains accepted but is unused. The
entropy-specific feasible-filter theorem remains in `Entropy.RegionUnion`.
No public declaration is removed. Equation lemmas preserve `rw` and `unfold`
behavior for the regional-state and regional-entropy abbreviations. Their reduced
bodies also preserve entrywise `ext` followed by `simp only`, as used in
`FilterChainEnergy.regionState_smul`. The site
and regional equivalence abbreviations retain their original reduced bodies,
so TNLean physical-interval transport can still simplify the old names alone.
The legacy disjoint-union equivalence keeps its original construction because
conditional-movement frames simplify its inverse directly; the placement theorem
delegates to the generic Sites result.

The downstream source audit used TNLean commit
`7e8438a32f1f0435e3acec579a89656de1b3f07b` and covered `TNLean/Circuit/LiebRobinson` (in particular
`GraphPropagation`), the regional state bridges in `TNLean/Lattice`, and
`TNLean/PEPS/ParentHamiltonian/DependentRegionCoordinates`. The latter unfolds
`Entropy.regionState`, so the regression suite checks the original partial-trace
rewrite sequence as well as definitional compatibility. The Lieb–Robinson
support signatures are unchanged by this extension; this is not its pilot port.

## Remaining work

Product vectors and their factorized expectations, site-supported projections,
Schmidt-rank APIs, the remaining regional entropy results (including strong
subadditivity over arbitrary basis types), and the downstream TNLean consumer
sweep remain outside this branch. Main now contains separate Dynamics and
Lieb–Robinson work; this PR neither replaces nor claims that work. Existing dimension-indexed wrappers remain until
the coordinated consumer sweep. This change does not claim to complete #1051.

## Validation

Validated with the repository's pinned Lean `v4.36.0-rc1`, after successfully
fetching all 9,047 Mathlib cache artifacts:

- `lake build`: passed, 21,405 jobs, including the root `QICLean` aggregate.
- `python3 scripts/ci_lean_checks.py strict --base 4fd4962204b7abdd012d4d0495d52d9d77003688 --jobs 3 --timeout 300`:
  all 13 changed source files and 70 affected test files passed, with warnings
  treated as errors.
- `lake exe checkdecls blueprint/lean_decls`: passed against the compiled library.
- `lake exe lint_style`: passed.
- Blueprint/source synchronization, generated imports, added-prose checks,
  file-size policy, numbered-file policy, and `git diff --check`: passed.
- Kernel axiom reports for the placement, regional marginal, covariance and
  supported-observable trace theorems contain only `propext`, `Classical.choice`,
  and `Quot.sound`.

`QICLeanTest/ManyBodyRegionState.lean` checks product-valued site bases, empty
bases, the reference-free supported-observable theorem, definitional agreement
with the legacy state and entropy, legacy rewrite sequences, the entrywise
scaling proof, and the disjoint-union inverse computation. The TNLean-style
site-equivalence simplification is checked explicitly. TNLean itself was source
audited at the revision recorded above, not built; downstream caller migration
remains separate work.

The repository does not contain the optional `scripts/tactic_pattern_scan.py`
mentioned in `CLAUDE.md`; migrated proof repetition was reviewed directly.
