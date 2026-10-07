# Excitation-subset counting estimates

The four results in `QICLean/Analysis/ExcitationSubsetCounts.lean` establish the
scalar counting step preceding the inverse-compression inequality in OpenAI's
*A two-dimensional area law from a global spectral gap*, September 24, 2026,
Section 7, lines 577–590. The manuscript assumes `0 < τ < 1/2` at line 154;
the formal bounds also include both endpoints. The proofs include zero copies
and count actual finite subsets, rather than assuming a counting formula.

The verified mathematical source revision is
`40d9ab9edbdbd96bf49e4934eb785e02417852e9`, based on QICLean revision
`48425ea8ed2390a94c71870ac19142490e5df5b7`. The manuscript revision is
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` of `openai/math`.
`source.json` records the immutable manuscript's byte length, SHA-256 digest,
and exact relevant lines. The proofs are original; no upstream Lean proof text
is reused.

## Verification

The targeted build and strict source elaboration passed. The strict command
uses all project Lean options and treats warnings as errors. The complete
QICLean build passed with 9761 jobs; its existing warnings are retained in the
raw log. Every new theorem's imported kernel report lists only `propext`,
`Classical.choice`, and `Quot.sound`. The integrity scan finds no `sorry`,
`admit`, `axiom`, `native_decide`, or `unsafeCast` in the new module.

The PDF and web blueprint builds passed. Native declaration checking passed
for the generated list of 3381 declarations, including all four new results.
The rendered web check passed on 42 pages at mobile and desktop widths,
with 37208 typeset mathematical elements. The PDF page containing both new
theorem statements was visually inspected. The generated declaration list is
retained as `lean_decls.txt`; these checks do not constitute a fresh kernel
audit of the existing 3377 declarations.

`metadata.json` records source-file digests and the commands, return codes,
and raw-log digests. The four-entry provenance shard refers to the same frozen
source revision. The source-faithful statements and proof argument received an
independent mathematical review. No inverse-compression or area-law theorem
is claimed by these four scalar results.

## Reproduction

Fetch the pinned prebuilt Mathlib cache before any build; do not rebuild
Mathlib from source. On macOS the recorded cache and Lake commands were run
through the TNLean worktree's repository lock, explicitly changing directory
to this QICLean worktree. All dependency checkouts matched the pinned manifest;
no dependency version was changed and no cache tree was copied.

Run the build, strict elaboration, imported kernel driver, blueprint builds,
and native declaration checker using the exact commands in `metadata.json`.
The audit driver disables only the linter forbidding `#print` commands, since
printing kernel dependencies is its purpose.

For the four-entry provenance check, supply the shared TNLean validator and
schema explicitly:

```sh
uv run --with jsonschema python docs/provenance/evidence/8750-excitation-subset-counts/check_provenance.py \
  --validator /path/to/TNLean/scripts/check_openai_provenance.py \
  --schema /path/to/TNLean/docs/provenance/openai-math.schema.json \
  --upstream-root /path/to/openai-math.git
```

The validator's immutable TNLean revision and digest are in `metadata.json`.
The check validates the four new entries, exact source bytes, manuscript
references, recorded log digests, and kernel dependencies. It does not check
all inherited QICLean provenance, and it does not invoke Lean itself.
