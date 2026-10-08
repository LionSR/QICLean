# Repeated pure vectors: complete verification

This record verifies the two actual-product identities in `QICLean/Entropy/PureTensorPower.lean`. For an arbitrary bipartite vector, the reduced density of its regrouped repeated vector is the literal tensor power of its one-copy reduced density. For any actual orthogonal projector on the retained repeated system, the projected squared norm is the corresponding real trace mass. The identities require neither normalization nor invertibility and include zero copies and empty one-copy factors. They do not assert concentration, an entropy window, a common Schur-label sequence, or an area law.

The manuscript passage is Section 7, lines 255–281, of the September 24, 2026 source, pinned at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The immutable manuscript file has SHA256 `5c8d8dd55a283a7ffe9573067c631ea70d93b01c207a297aee02352c25d2573b`.

## Source and scope

- Parent: `0c3485a499660de80843affa0b25b964c12a5193`.
- Mathematical source: `c3c228ced821c1da85f3064b52eda3a2fee3cc6a`.
- Frozen leaf evidence: `8c3495a27178d65daef820768aec0ae096dab7c7`.
- Final inclusion and verification source: `b9c8bd663c081e6128353eee979d266b1c4bdce0`.

The inclusion adds only the generated entropy import and the unique chapter input. All mathematical source, the fragment and the pattern-ledger entry remain byte-identical to the frozen source. All 196 parent provenance/evidence files remain byte-identical. The audit covers exactly the two new declarations and one owned provenance shard; no fresh audit of other owners' unchanged declarations is claimed.

## Actual checks

The full library build passed with 9,695 jobs using pinned prebuilt Mathlib artifacts. No Mathlib source compilation appears in either full-build log. Two fresh stock-kernel reports passed with only `propext`, `Classical.choice`, and `Quot.sound`; their raw contents are byte-identical to the frozen leaf reports. The frozen-policy provenance validator, generated imports, reader-facing prose, 59-slug gap registry, native declaration checker and source continuity checks all passed. The native checker examined 3,191 distinct collected names, with both exact new names retained in `lean_decls` and `native-inventory.json`.

The complete PDF and web commands passed. The PDF has 415 pages, SHA256 `224c5a64a47c814353faf2cccc6f9f165065e4d2ed16865a9e1d52f51d42ceaa`. Physical page 314 contains the resolved Quantum Entropy heading; physical page 396 contains both new statements and proofs. Their formulas, conjugation bars, source citation, scope statement and surrounding references were visually inspected. The final TeX log has one 1.2038pt overfull warning in the new section heading; no clipping, overlap or equation overflow is visible. This warning is recorded rather than suppressed, and the frozen fragment is preserved.

Focused browser checks passed at widths 360 and 1440, with all three new anchors present and no page overflow. Both new statements and expanded proofs were visually inspected in retained screenshots. Whole-web reader checks passed on 38 pages with 36,045 typeset elements. The web renderer used its documented PDF fallback after the XDV canary failed; its actual exit was zero.

## Preserved unsuccessful attempts

The leaf retains the interrupted disk-capacity audit capture and the earlier overlapping dependency/cache attempt, both excluded from canonical evidence. This record also retains the initial complete-library exit 1 caused by operating-system file-table exhaustion during output-hash removal in an unchanged dependency. One sequential warm full-library retry passed without a source edit. An initial validator invocation omitted its required repository argument. Two local collection assumptions were corrected: a bibliography target uses a valid named anchor, and the new heading has the small warning described above. These operational records under `excluded/` are not presented as passing verification.

Every canonical command has its actual arguments, exit status, elapsed time, source revision and raw-output hash. Large outputs use lossless gzip with zero modification time and both compressed and uncompressed SHA256 hashes. `verification.json`, `render-inspection.json`, `compressed-logs.json` and `evidence-sha256.json` retain the complete check and artifact inventory.
