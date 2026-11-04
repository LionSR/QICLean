# Ordinary Petz overlap data processing

This contribution addresses a bounded slice of QICLean issue #46, linked as
`Refs #46`. It proves Wolf Equation (8.35) for exponents in `[0,1]` only.
The reverse inequality on `[-1,0]`, the inverse/support audit for that interval,
and all remaining quasi-relative-entropy and hypothesis-testing items stay open.

## Source and public boundary

Source: `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 480–486.
The theorem concerns ordinary `Re Tr(ρ^α σ^(1−α))`, not a sandwiched power.

`Matrix.petzOverlap_data_processing` assumes precisely a pair of PSD trace-one
matrices, `α ∈ [0,1]`, and a rectangular `IsKrausCPTP` map. Its input
and output coordinate types are independent finite types. There is no public
invertibility, support, commutation, output-domain or equal-dimension premise.
Trace one supplies nonempty input dimension. The stronger
`Matrix.petzOverlap_le_map` needs only PSD inputs in positive input dimension.
`Matrix.petzOverlap_le_partialTraceRight` allows an empty retained space and
requires a nonempty discarded factor.

The existing CFC convention has `A^(0:ℝ)=1` for every PSD matrix, including a
singular one. At α=0 the overlap is `Re Tr σ`; at α=1 it is `Re Tr ρ`.
Consequently both density-state endpoint overlaps equal one. This convention
is stated explicitly in the production docstrings, Blueprint and regressions.
The source passage does not specify a competing zeroth-power convention; no
support-projector endpoint theorem or source correction is claimed here.

## Construction and dependencies

Fresh main was fetched at `14ecc5b64bb61cccb01a6583bbab3252bee1486b`.
The issue, all seven issue comments and the open-PR list were refreshed before
edits; no competing claim or PR for this slice was found.

The exact published #997 head
`18be0a849d6a7cc0c4cbae0b13624355d5c62bef` was fetched successfully and
verified against GitHub PR metadata. The draft is stacked on that head,
targeting the dependency branch of PR #997. The generic DPI implementation is
unchanged and is called through `Matrix.ConvexMatrixFunctional.map_le`.
No unpublished dependency commit was substituted. The original local
implementation remains preserved separately from the publication snapshot.

The new owner is `QICLean/Channel/Schwarz/PetzOverlapDataProcessing.lean`.
It imports only `Analysis.LiebConcavity` and
`Channel.ConvexFunctionalMonotonicity`. The new module's repository proof
closure contains 42 modules. The whole 1,373-module production import graph
is acyclic. A prohibited-proof-token scan of the 42-module closure found no
hits. No new assumptions or logical axioms were introduced.

Negative overlap on PSD pairs is jointly convex by the existing
`lieb_concavity_psd` at auxiliary matrix `K=1`. The finite-`Fin` theorem is
transported to arbitrary finite coordinates. Unitary covariance of powers and
trace cyclicity prove unitary invariance. Functional-calculus covariance and
trace reindexing prove coordinate invariance. PSD Kronecker power factorization
and `τ^α τ^(1−α)=τ` prove common-density-ancilla invariance. The latter identity
uses finite-spectrum CFC multiplication and `Real.rpow_add_of_nonneg`, so it
includes singular ancillas and both endpoints without an `IsUnit` hypothesis.
PSD domain closures are proved directly; CPTP output membership follows from
`IsKrausCPTP.map_posSemidef`.

Lean is unchanged at `v4.35.0-rc3`; Mathlib is unchanged at
`c55e6e786f49471c72fbddbec5415808896aec1e`. All manifests, dependency pins
and toolchains are byte-unchanged from the published dependency head. Before
builds, the pinned prebuilt Mathlib cache fetch reported no files
to download and 8,943 already decompressed artifacts. Build logs contain zero
rebuilt Mathlib Lean modules. The native text-linter executable built C objects
from cached generated C; this was not a Mathlib proof-source build.

## Independent review

A separate native agent read the exact Wolf
passage, all new proof bodies, all convex-functional hypotheses, rectangular
dimensions, arbitrary ancilla normalization, endpoint conventions, tests and
Blueprint. It found no mathematical or proof-integrity blocker. It independently
ran strict production and regression checks successfully (6.84 seconds) and
confirmed all 15 guarded declarations use only `propext`, `Classical.choice`
and `Quot.sound`. This is an automated independent audit, not human approval.

## Validation

- Targeted Lake builds of the existing Lieb/generic-DPI dependencies and the
  new production module passed. The new module built in 2.8 seconds. The
  changed `QICLean.Channel.Schwarz` import aggregator also built successfully.
- The unchanged CI strict selector passed against `18be0a84`: both changed
  production sources (including the aggregator) and the retained regression
  file passed. Its initial run identified missing local aggregator artifacts;
  the targeted aggregator build supplied them before the successful rerun.
- Strict production and regression elaboration passed with the repository
  flags: `autoImplicit=false`, `relaxedAutoImplicit=false`,
  `pp.unicode.fun=true`, `maxSynthPendingDepth=3`,
  `linter.mathlibStandardSet=true`, `warningAsError=true`.
- Retained actual-name guards cover all nine public production declarations
  and six test lemmas. All 15 transitive axiom sets are exactly the three
  standard foundations above.
- Boundary tests prove the concrete states `diag(1,0)` and
  `½ [[1,1],[1,1]]` are PSD, trace one, singular and noncommuting. They test
  both endpoint values, the raw source inequality at both endpoints through
  arbitrary 2-to-3 CPTP maps, an actual 2-to-3 preparation channel,
  a singular density ancilla across the exponent interval, a 2-by-3 partial
  trace, and an empty retained space. No positive-definite surrogate or commuting-only boundary is used.
- Generated imports, global import acyclicity, Blueprint source synchronization
  and reverse coverage of every new public declaration, added prose, module
  policies, whitespace and the native production text-style scan passed.
- All 52 repository Python unit tests passed after fetching the pinned tenkz
  dependency and installing the pinned Blueprint tooling in an isolated
  temporary virtual environment. Paper-gap references passed (78 slugs).
- The new Blueprint section was compiled twice as a two-page isolated excerpt
  with the project common/print macros; the mathematical page was visually
  inspected. The excerpt omits external chapters and therefore leaves their
  cross-references unresolved. This is not a full Blueprint render.

The full-library build, full strict suite, downstream TNLean build, compiled
global Blueprint declaration check, full Blueprint PDF/web render and browser
render integration tests were not run. The nine new Blueprint declaration
names are compiled by the retained actual-name/axiom guards.

The publication snapshot preserves every Lean proof, theorem statement, test,
Blueprint entry and dependency pin from the independently audited implementation.
Only this audit's local operational details were removed before public review.
The public commit uses the author's established GitHub noreply identity.
Publication is a draft stacked on #997; readiness, dependency merge ordering
and final integration remain separate review steps.

OpenAI Codex assisted with the formal proofs, source audit and validation,
including a separate native mathematical reviewer. No human approval is claimed.
