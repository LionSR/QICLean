# Typesetting correction after mobile inspection

The initial complete book commands passed, but visual inspection found that the
long inline coordinate decomposition in the definition was clipped on a narrow
screen. Automated page-width checks did not detect this. The initial PDF, web
captures, helper scripts, command records and visual failure are preserved in
`initial-book-verification.json` and `visual-inspection-initial.json`.

Exposition commit 7840e716 changes only the owned fragment. The retained and
traced factors are now displayed in two rows, with their order unchanged.
The literal Lean definition and theorem remain byte-identical to mathematical
source 05dc0048; no proof or library rebuild was needed. The successful full
library and two imported kernel reports remain bound to their actual earlier
revision 69b31fc6. A new complete PDF, bibliography, strict web, native check,
focused reader, whole-web reader and PDF rendering were run at 7840e716.

`exposition-freeze.json` binds the current fragment separately. Historical leaf
hashes for its original form are checked against source commit 05dc0048; every
other leaf file is checked against the current bytes. All prior evidence is
unchanged. `validate-revised-manifest.py` is the final validator; the earlier
validator script is retained as part of the initial attempt inventory.

The final visual review confirms both coordinate rows, the complete definition,
and the theorem and proof on desktop and narrow screens, and on physical PDF
pages 412–413. No formula requires horizontal scrolling in the revised view.

The initial final-manifest validator also had a reporting error: a filename loop
shadowed the native-report variable. All validation assertions had passed before
the last print statement failed. Its helper snapshot and actual exit-1 command
record are preserved; the corrected validator changes only that variable name.
This metadata failure is excluded from successful checks.
