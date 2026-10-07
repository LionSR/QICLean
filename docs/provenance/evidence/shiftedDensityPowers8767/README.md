# Shifted density powers: exact-source verification

Published source revision: `81ca38e523242fe7d1be1195f3e974c7a5da6134`.
Locally checked revision: `bbce2a919afaa015802d90038212adeda02da0e3`.
Both have the exact Git tree `a819d147d9c0cb4f67cce82978d9e6f3d439b89c`.

The production module, ten regression examples and all seven public axiom
reports passed actual serial direct Lean checks with a 90-second module limit,
one thread, package options, standard linters and warnings-as-errors. Regressions
also disable auto-implicit variables. Raw compiler output is unchanged; silent
successful runs have empty logs. `checks.json` records actual invocations,
timings, output paths and source/artifact hashes, including exact pre/post
source-closure snapshots. All seven axiom sets contain only propext,
Classical.choice and Quot.sound.

The independent artifact overlay contains only source-audited project outputs
from recorded successful invocations. Mathlib's pinned prebuilt cache was
present; no cold Mathlib build or fabricated Lake trace was used. Package pins,
root inputs and import source hashes are audited separately. All eight published
source files match the frozen local snapshot byte for byte.

Import-generation, file-policy and build-hotspot tests passed (9, 16 and 7 tests).
Blueprint source sync covers 2,835 references including all seven new names.
Changed-file prose, both provenance contracts, pinned latexindent 3.24.7, and a
focused two-page XeLaTeX PDF passed. The full prose scan has nine unchanged
pre-existing findings. The new strict regression workflow step follows the full
project build.

These direct checks are distinct from a full Lake build, aggregate checkdecls
and full blueprint rendering; those remain CI gates. The seven facts support
regional regularization only. The native ordered minimum, stationarity, energy
estimates and the full source Proposition 4.1 are outside this QIC batch.
