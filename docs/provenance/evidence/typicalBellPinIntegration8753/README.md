# Integrated verification of the one-copy Bell contraction

The integration source is frozen at
`0e98b2bb797daead5312190905de9b20658182b9`, over the published compressed-vector
parent `c8d6b2f7e576407d180c853a7ebb5ad84b342422`. The mathematical Bell source
remains exactly `90e6071e32453006906390bd4e4f71ff4c5251a0`, and its original
strict-source, target and seven-declaration evidence remains exactly
`cec84e2532a4a4f77c0300528f07d15acd5f81db`. The integration adds one generated
import and one chapter input; neither the proofs nor their individual logs
were changed.

The complete library build passed with 9,683 jobs after an explicit pinned
prebuilt Mathlib cache fetch and artifact guard. Existing warnings were
replayed from inherited modules. The Bell target and entire frozen source had
already passed without warnings. All 69 public declarations in the nine owned
provenance shards have exact-name stock Lean kernel reports containing only
`propext`, `Classical.choice` and `Quot.sound`. The frozen provenance policy
validates their individual immutable source bytes and proof-bound logs, original
notices, and the new combined kernel report. All nine production modules retain
their previously verified bytes.

The complete PDF and strict web builds passed. The PDF has 412 physical pages.
The Bell section, numbered 13.21, occupies physical pages 396–397, printed
pages 395–396. Both pages were rendered and inspected: the selected isometry,
uniform pair, Bell vector, orthogonal projection, actual prevector and
postvector, exact coefficient and its finite contraction proof are legible.
There are no unresolved references or new overfull lines in this section.
Inherited overfull paragraphs elsewhere in the book are unchanged.

The web test passed on all 36 generated pages with 35,827 typeset elements.
The new section was separately rendered and inspected at desktop and mobile
widths, with both proofs expanded after their opening animations finished.
All seven declaration links are present and the 32 mathematical elements have
no MathJax errors. The mobile page has no horizontal overflow. The longer
coefficient calculation scrolls within its display; both ends were inspected.

The final native declaration check passed on all 3,117 distinct declarations,
after the web build finished writing the declaration list. An earlier invocation
used the blueprint directory as its working directory and could not find the
native executable (exit 255). Its raw log is retained as `checkdecls-attempt1.log`.
A preliminary successful check before the web build finished is also retained;
the final complete check supplies the reported result. Both operational issues
were resolved without changing any mathematical source.

Generated import verification, Lean–blueprint synchronization, the changed-prose
check and the actual paper-gap registry check passed. The registry resolves all
60 referenced notes. The source remains the one-copy Bell calculation with
positive actual selected mass; tensor powers, complementary label projections,
sector probabilities and the complete ground-state area law are subsequent
arguments. This branch does not import the concurrent tensor or 73-result
integration developments.

`verification.json` records the exact sources, commands, exits and hashes.
The larger build, PDF, web and writer logs use lossless deterministic gzip;
both original and compressed hashes are recorded. Individual leaf logs are
retained verbatim. `render-inspection.json` records the complete-book pages and
web views inspected. No previous evidence record was overwritten.

These proofs and checks were prepared with assistance from OpenAI Codex
(GPT-6). Human mathematical review is separate from kernel verification.
