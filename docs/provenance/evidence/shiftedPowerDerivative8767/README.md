# Shifted power derivatives: exact-source verification

Published source revision: `493a53ce373d04663910c2039ba37636128ae24d`.
Locally checked source revision: `23270709ef0afb13fbd123564d492b61694edb98`.
Both have the exact Git tree `f23b79657392b46f4b94fbe68713c32cddad329c`.

The production module, thirteen regression examples and all three public
axiom reports passed serial Lean checks with a 90-second per-module limit,
one thread, package options, Mathlib standard linters and warnings-as-errors.
Regressions also disable auto-implicit variables. The axiom-only driver
permits hash commands so that it can print the actual axiom sets. Raw compiler
output is unchanged; silent successful runs have empty logs. Every public
axiom set contains only propext, Classical.choice and Quot.sound.

`checks.json` records actual invocations, timings, source/output paths and
hashes, including exact source-closure and imported-artifact pre/post
snapshots. The ten project dependency artifacts were matched to successful
prior compiler records and exact current sources. Package pins and the
prebuilt Mathlib cache were verified; no cold Mathlib or full Lake build,
fabricated trace, or binary artifact is included in this evidence packet.

New/diff reader-facing prose, all three blueprint entries, the chapter and
Lean import routes, planned source notices, and the strict CI regression step
were checked. The full repository prose scan retains inherited violations;
its raw output is preserved and is not claimed clean. Import-generation,
file-policy and build-hotspot tests passed (9, 16 and 7 tests). The focused
new blueprint chapter passes ChkTeX with the unmodified distro configuration
and repository configuration.

These focused checks are distinct from a full local Lake build, aggregate
compiled checkdecls, and full blueprint rendering; those remain CI gates.
The scalar-shift derivative, exp(-R) chain rule and inverse contraction do
not prove the ordered-product derivative, minimum envelope, regulator growth,
or the full source Proposition 4.1.
