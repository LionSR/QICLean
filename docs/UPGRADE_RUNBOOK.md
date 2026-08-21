# Two-repo Mathlib upgrade runbook

QICLean and TNLean are two Lake packages sharing one Lean/Mathlib toolchain.
TNLean depends on QICLean as an ordinary package requirement pinned to a
released tag; QICLean has no dependency back on TNLean. A Mathlib (or Lean
toolchain) upgrade therefore has to land in QICLean first and propagate to
TNLean afterward — the two repositories must never sit on different
toolchains or different Mathlib revisions for longer than the single PR that
moves between the two consistent states below.

This note exists because the split otherwise creates a class of failure a
single-repo library never sees: a silent toolchain or Mathlib-revision
mismatch between the two repositories does not fail cleanly. TNLean's own
Mathlib requirement (needed because Lake resolves the whole dependency graph
to one root-selected Mathlib revision) can silently override QICLean's pin,
so a stale QICLean tag paired with a bumped TNLean Mathlib rev produces
confusing kernel/elaboration errors deep in QICLean-sourced code, not an
obvious version conflict. Follow this procedure exactly, and keep the CI
guard in §3 wired on both sides.

## 1. Lockstep invariants

These must hold at every point except the deliberate transition window in
§2:

- **I1 — identical toolchain.** `lean-toolchain` in QICLean and in TNLean are
  byte-identical.
- **I2 — identical Mathlib revision.** QICLean's `lake-manifest.json` and
  TNLean's `lake-manifest.json` pin the same Mathlib commit. (Lake resolves
  the whole dependency graph to TNLean's root-selected Mathlib revision, so
  TNLean's requirement is authoritative for what actually builds; QICLean's
  own pin only matters for QICLean's standalone CI and its published
  prebuilt archive, which is olean-valid only at the revision and toolchain
  it was built against.)
- **I3 — tag pin, never a branch.** TNLean's `[[require]] name = "QICLean"`
  points at an immutable released tag, never at `main` or a branch name.

## 2. Procedure (QICLean first, then TNLean)

1. **QICLean**: dispatch the ordinary Mathlib-update workflow
   (`update.yml`), which opens a toolchain/Mathlib/manifest bump PR. Run
   `lake exe cache get`, then `lake build`, then the blueprint build and
   `leanblueprint checkdecls`. Merge once green.
2. **QICLean**: tag a release. `create-release.yml` auto-mints a toolchain
   tag on every `lean-toolchain` change on `main`; in addition, push a
   semantic-version tag `vX.Y.Z` — this is the tag TNLean actually pins, and
   using semver (rather than only the toolchain tag) lets a later
   content-only hotfix land as `vX.Y.(Z+1)` without another toolchain bump.
   The tag push triggers a release build (`lake build && lake upload
   vX.Y.Z`), producing a prebuilt archive TNLean's CI can fetch instead of
   recompiling QICLean from source.
3. **TNLean**, one PR:
   - Copy QICLean's `lean-toolchain` byte-for-byte.
   - Bump the `QICLean` requirement to the new tag.
   - Bump the `mathlib` requirement to the same revision now in QICLean's
     manifest (TNLean's root Mathlib requirement must match QICLean's, per
     invariant I2).
   - `lake update QICLean mathlib`, `lake exe cache get`,
     `lake build QICLean:release` (or an equivalent prebuilt-archive fetch),
     then `lake build`.
   - Let ordinary CI and the auto-fix loop handle any proof fallout from the
     Mathlib bump; this PR is not required to be a pure version bump if a
     handful of TNLean proofs need adjustment, but it must not touch
     QICLean-side files.
4. **TNLean's `update.yml`**: the stock `mathlib-update-action` is
   QICLean-unaware. Keep it in report-only mode
   (`on_update_succeeds: issue`) rather than auto-opening a PR, so a
   Mathlib bump on the TNLean side is never proposed out of step with
   QICLean's release — or add a pre-step that fails the moment TNLean's
   proposed Mathlib revision does not match QICLean's currently pinned tag.
   This reconfiguration must land in the same PR that first adds the
   QICLean requirement, not as a follow-up.

## 3. CI guard

Both repositories run a small step in `pr-ci.yml`'s build job comparing:

- their own `lean-toolchain` against `.lake/packages/QICLean/lean-toolchain`
  (TNLean side only; QICLean has no such dependency to check), and
- the `mathlib` entry in their own `lake-manifest.json` against the
  `mathlib` entry in `.lake/packages/QICLean/lake-manifest.json`.

A mismatch fails the build with a message pointing back at this file. This
guard is load-bearing, not cosmetic: it is what turns a silent lockstep
violation (invariant I2, above) into a clean CI failure at the point the
mismatch was introduced, rather than a confusing downstream elaboration
error discovered later.

## 4. Hotfix path (no toolchain change)

A QICLean fix that does not touch `lean-toolchain` or the Mathlib revision —
a proof fix, a new lemma, a signature correction covered by the
downstream-compatibility rule in `CLAUDE.md` — merges and tags
`vX.Y.(Z+1)` as usual (step 2 above), and TNLean only needs to bump the
`QICLean` tag, not the Mathlib revision. Every build cache stays hot on both
sides.

## 5. Cache and cost notes

`lake exe cache get` only restores prebuilt Mathlib; it does nothing for
QICLean itself. Without a prebuilt QICLean archive, a TNLean run with a
cold cache would recompile all of QICLean from source on every build,
reintroducing the multi-hour CI cost that the shared-cache-eviction fix
(`docs/lake_build_cache.md`) already solved once for TNLean's own modules.
The mitigation, in order of preference:

1. **Primary**: QICLean's release tags publish a prebuilt archive (`lake
   upload`); TNLean's CI fetches it (`lake build QICLean:release` or
   equivalent) instead of compiling from source. Verify the exact `lake
   upload` / `lake build ...:release` invocation against the pinned Lean
   toolchain before relying on it in CI — the Lake release-archive feature's
   exact flags are toolchain-version-sensitive.
2. **Backstop**: include QICLean's build directory
   (`.lake/packages/QICLean/.lake/build`) in TNLean's `BUILD_CACHE_PATHS`,
   saved only from `main`, same as TNLean's own build cache. This keeps the
   net cost inside the shared 10GB repository cache LRU budget as long as it
   is not duplicated per-PR (see `docs/lake_build_cache.md` for why saving
   from every PR run, rather than only `main`, previously evicted useful
   cache entries within minutes).

## 6. Checklist

Before merging a QICLean Mathlib/toolchain bump:

- [ ] QICLean: `lake exe cache get && lake build` green
- [ ] QICLean: blueprint builds, `leanblueprint checkdecls` green
- [ ] QICLean: semver tag pushed, release archive built

Before merging the corresponding TNLean bump:

- [ ] `lean-toolchain` byte-identical to QICLean's
- [ ] `mathlib` revision in TNLean's manifest equals QICLean's
- [ ] `QICLean` requirement pins the new semver tag, not a branch or bare SHA
- [ ] TNLean's own `lake exe cache get && lake build` green
- [ ] The toolchain/Mathlib-comparison CI guard (§3) passes
