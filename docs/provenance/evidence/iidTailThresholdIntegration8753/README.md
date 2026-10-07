# Numerical independent-copy tail threshold: complete verification

The one numerical theorem and its exposition are frozen at
4665d148b770a504e4dd3cb8ac402e11cc68b5d4. Leaf evidence is committed at
663dc8bd. The separate inclusion 1681609e adds exactly one generated
Analysis import and one chapter input. The contribution is based on the
released independent-copy concentration revision 1d7c3bc9.

The complete library build passed with 9696 jobs. The nineteen actual
commands in `verification.json` all exited successfully: explicit prebuilt
cache fetch, both named Mathlib guards, library build, five-name kernel audit,
two-shard frozen provenance, import/prose checks, diagram fetch, paper-gap
registry, declaration sync, PDF, bibliography, web, native declarations,
rendering and focused/complete web checks. No Mathlib source was rebuilt.
Each raw log is tracked and paired with deterministic gzip and two hashes.

All five kernel reports contain only `propext`, `Classical.choice` and
`Quot.sound`. The full native list contains 3194 names, including all five
owned declarations. Each has one exact rendered documentation link.
`native-targets.json` records the literal list hash and containment check.

Source preservation checks retain all 767 inherited Lean files except the
intentionally regenerated Analysis import file, all 113 inherited iid
evidence/exposition files, and the three new frozen source/exposition files.
The inherited frozen proofs and provenance entries are unchanged.

The complete PDF and web views were inspected. The numerical theorem and
proof appear on physical page 398, printed page 397. The formula places one
half inside the exponential. Desktop and 360-pixel mobile views are legible
without page overflow. The whole web regression passes on 38 pages with
36100 typeset mathematical elements.

`validate-manifest.py` verifies the command exits, all listed file hashes,
tracked raw logs, gzip decoding, inherited source bytes, and five exact
kernel reports. This is a numerical eventual threshold; the source theorem
contains no spectral, label or concentration hypothesis.
