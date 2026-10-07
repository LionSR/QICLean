# Replica copy symmetry: complete integration verification

The five results in `QICLean/Analysis/ReplicaPermutationCovariance.lean`
prove copy-permutation commutation for the actual replica sum and constant
tensor power, transfer this commutation to real functions of the actual
excitation count, and preserve simultaneous copy symmetries and fixed
auxiliary sectors after applying a physical spectral function.
They include zero copies and require no normalization of the one-copy vector.
The tensor-power result supplies permutation invariance of the actual
independent-copy density. Concentration and entropy-window selection remain
separate assertions.

The mathematical source is frozen at
`8c611f14b4e6162790157e86935caeaf17d0cc17`; its leaf evidence is
`b4651efe05390747285c125ebe6f3fb8b01e1be7`. The two-line inclusion at
`7c35cc9da08c5c566190fb792ad133f4fa5f03ca` adds the generated analysis
import and the unique entropy-chapter fragment. All commands in this directory
are bound to that inclusion revision and the whole-file hashes in
`source-freeze.json`.

The genuine complete library build passed with 9,709 jobs. Complete PDF and
web generation, the native declaration checker for all 3,283 generated names,
the import check, the changed-prose check, and the registry check for 60
referenced paper-gap slugs passed. The new five-name stock-kernel report
contains only `propext`, `Classical.choice`, and `Quot.sound` and is
byte-identical to the leaf report. The one new provenance shard, containing
five declarations, passed the frozen TNLean policy validator.

The complete PDF has 427 pages. Physical pages 407–408 contain all five new
statements and proofs; page 316 shows the entropy chapter heading. Visual
inspection found legible formulas, resolved citations, and no clipped or
overlapping text. The final LaTeX log has no unresolved references and no
overfull box in the new fragment. Other book entries retain overfull-box
warnings. Web generation used the documented tenkz PDF fallback after its
xdv canary failed; generation completed successfully. The inspected web
section, exact declaration references, rendered pages, and final writer log
are preserved here.

The twelve earlier production files, the two replica source files, their two
fragments, and the replica document remain byte-for-byte unchanged. All 475
parent provenance and evidence files, including the 89 earlier kernel
reports, remain unchanged against parent
`3cc74d334c21d5693c6e2072c2e82e17630142c8`. Their original bindings are
preserved in `../replicaSymmetry8750/parent-evidence-preservation.json`.
The fresh kernel audit covers only the five new declarations; it does not
claim a new audit of the parent reports or of other contributors' results.

The required main revision was merged at
`502ba621d485f15b72d8aa5582eaad62f351096b` to obtain the existing copy
action. Only generated import and chapter-input conflicts were resolved by
union. The exact original six-line entropy header was retained.
The named Mathlib revision and checked-out dependency both equal
`c55e6e786f49471c72fbddbec5415808896aec1e`. A successful prebuilt fetch
and `Mathlib.olean` guard followed the completed APFS copy; the initial
overlapping fetch is retained as an excluded operational attempt in the leaf
directory. The complete build log records no Mathlib source compilation.

`verification.json` records actual commands, exits, source hashes, and audit
scope. Large raw logs use deterministic gzip with timestamp zero;
`compressed-logs.json` records both compressed and uncompressed hashes.
`evidence-sha256.json` records every other artifact in this directory.
