# Complete verification of the joint density contribution

The mathematical source is frozen at 05dc0048 and its source-bound leaf evidence
at f94ea7d4. Inclusion 69b31fc6 adds exactly one generated Analysis import and
one chapter input. It leaves the literal source, exposition and earlier evidence
unchanged. The two released prerequisites are #640 at 551f1cd4 and #643 at
72f13fda; their merge and its sole incoming production difference are recorded
in the leaf evidence.

`verification.json` records actual complete-library and book commands, hashes
of the evidence and artifacts, native declaration containment and visual
inspection. The fresh mathematical audit is limited to the two new public
exports. Earlier kernel reports are preserved; this record does not claim a
new semantic review of every inherited theorem.

The named Mathlib guard verifies the exact c55 revision and six prebuilt
artifacts before building QICLean. No Mathlib source build or cross-revision
artifact copying is used. Raw command logs have deterministic gzip companions.
Any failed attempt is retained and excluded from successful verification claims.

The native check follows all active fragment inputs, verifies every declared
target, and checks the rendered documentation links. PDF and web inspection
covers the full definition, theorem and open proof, including narrow screens
and any horizontally scrollable formulas. The full web reader checks every
content page. `parent-preservation.json` inventories all 3,213 tracked
leaf-parent files, allowing only the two exact inclusion lines.
