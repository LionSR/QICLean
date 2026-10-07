# Actual pure tensor-power identities: frozen leaf verification

The two results in `QICLean/Entropy/PureTensorPower.lean` identify the actual
reduced density of the regrouped product vector and its squared mass after
an orthogonal projection on the second system. Both hold for arbitrary
one-copy vectors and zero copies, including empty factors and singular
reduced densities. Taking the projector to be an actual Schur label
projector gives the sector mass directly. Concentration, entropy-window
selection and the common sequence of labels remain separate results.

The mathematical source, standalone fragment and repetition record are
frozen at `c3c228ced821c1da85f3064b52eda3a2fee3cc6a`, based exactly on
main revision `0c3485a499660de80843affa0b25b964c12a5193`.
The target build passed with 2,770 jobs; strict whole-file checking, the
two exact stock-kernel reports, changed-prose checking and validation of
the one owned provenance shard passed. The reports use only `propext`,
`Classical.choice`, and `Quot.sound`. Root independently reviewed both
frozen proofs, including the empty-factor and zero-copy cases.
All 196 parent evidence and provenance files in the preservation record
remain byte-for-byte unchanged. No fresh audit of parent declarations is
claimed. No generated aggregator or chapter input is changed in this leaf.

The isolated worktree was seeded from an idle owned worktree by APFS
cloning of dependency packages. Cross-revision QIC build artifacts were
omitted. Its own explicit prebuilt cache fetch passed after cloning
completed, and both the named and checked-out Mathlib revision equal
`c55e6e786f49471c72fbddbec5415808896aec1e`; `Mathlib.olean` was present.
An early exploratory dependency check overlapped the completion of this
own fetch. It is retained as an excluded attempt and was repeated after
the completed guard. Neither dependency log records Mathlib source
compilation.

One initial kernel-audit capture failed when the filesystem filled while
the wrapper wrote its exit record. The wrapper exited 1; the child exit
was not durably recorded, and its raw log was empty. That attempt is
retained under `excluded-audit-resource-failure.*` and is excluded from
the verification claim. After evidence writes became possible again,
the repeated audit passed and its actual exit and complete raw reports
were captured. The current complete build and book integration have not
yet been checked; they require adequate disk capacity and separate evidence.

`checks.json` contains the actual frozen command records and raw log
hashes. Exploratory diagnostics remain explicitly excluded from the final
provenance. `source-freeze.json` and `mathematical-review.json` record the
whole-file hashes and manuscript binding. `evidence-sha256.json` records
every other artifact in this directory.
