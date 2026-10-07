# Shifted density truncation: exact-source verification

Published source revision: `d4ce6280ba30a0176214a5dd5b22ec9b2b0fdc0b`.
Locally checked revision: `445b333ec172cf5ad38160d1f6743c05b739eb27`.
Both have the exact Git tree `b1e42ed9f15b1ad49feea4a847dd4b17bd0f3faa`.

The production module, eighteen regression examples and all twenty-one public
axiom reports passed actual serial direct Lean checks with a 90-second module
limit, one thread, package options, standard linters and warnings-as-errors.
Regressions also disable auto-implicit variables. Raw compiler output is
unchanged; silent successful runs have empty logs. `checks.json` records
actual invocations, timings, output paths and source/artifact hashes, including
exact pre/post source-closure snapshots. Every public axiom set contains only
propext, Classical.choice and Quot.sound.

The independent artifact overlay uses only exact-source-audited project outputs
from recorded successful invocations. The pinned prebuilt Mathlib cache was
present; no cold Mathlib rebuild or fabricated Lake trace was used. Package
pins, root inputs and import source hashes are audited separately. The public
name scan found no declaration collision in the remaining QIC or Mathlib source.

Import-generation, file-policy and build-hotspot tests passed (9, 16 and 7 tests).
Documentation validation results and limits for the planned source snapshot are
recorded in docs-validation.json. Both provenance checker contracts pass for the
21 activated rows; their actual output is preserved in active-provenance.log.
The new strict regression workflow step follows the full project build.

These focused checks are distinct from a full local Lake build, aggregate
checkdecls and full blueprint rendering; those remain CI gates. This module
proves inside-space head/tail estimates only. Ordered supported-prefix
integration, stationarity, entropy-tail estimates, regulator growth, and the
full source Proposition 4.1 are outside this QIC batch.
