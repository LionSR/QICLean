# Reusing the existing logarithmic reference estimates

Two existing private proofs in RefinementOutputPolynomialBound are public:

- Real.reference_accuracy_log_profile_bounds, formerly the private
  accuracy_log_profile_bounds;
- Real.reference_profile_polynomial_bound, with its descriptive name retained.

Both proof bodies are byte-for-byte unchanged. Their recorded SHA256 hashes
are 9be3b3d3952fcd5517476aa1e61fba81a17cb73fa3f315df9fe0793c63c68ea3 and
a5422028eeba704a05622f34c13f0d140357afe0aabf0b79693d97e8100a1185.
The existing complete-cost theorem keeps its byte-identical signature and
continues to use these proofs; only its two calls to the renamed accuracy
helper change. No compatibility alias is retained for the old private name.

The first estimate turns an inverse-accuracy bound epsilon^(-1)<=K Z^4
into 1<=b<=b0+log(Z^5). The second bounds a monotone logarithmic reference
expression by an explicit constant times a natural power. Future independent
truncation estimates can use Z'=Z^Q to cover larger polynomial accuracy
costs, without repeating either logarithmic argument. Both are numerical
auxiliaries supporting ALVV, arXiv:1602.08828v2, proof of t:alg1,
lines 1801–1817; no new physical construction or runtime bound is asserted.

## Verification

The selected immutable provider was TNLean 20cad76ebfa6e770263c4a5d5333917c5b226ed9,
with its own QICLean 98ba564e3c9603dc93d2173e3dc87a85ce750456 after the full
ordinary build. The source worktree has no .lake and belongs to the separate
QICLean Git common directory. No provider/cache sources or artifacts were
modified or copied.

- Changed QIC module: strict 31.243 seconds, 2 protected source/object pairs.
- Existing TNLean PhysicalDGTreePolynomialBond importer, re-elaborated against
  that fresh QIC object: 16.113 seconds, 759 pairs.
- Imported inspection of the two newly public lemmas, the existing complete
  scalar theorem and its existing physical polynomial caller: 7.796 seconds,
  760 pairs, only propext, Classical.choice and Quot.sound.

The temporary inspection source was deleted. The selected importer closure
was re-elaborated with explicit fresh source/object overrides; no unchanged
importer compiled against the prior helper source was reused. Source/object,
root-input and Mathlib artifact hashes were guarded. Proof-body and old-public
signature identity checks, blueprint/source coverage, reader-facing prose,
generated imports, forbidden-token and whitespace checks passed. The ledger
records reuse of these mathematical lemmas. Ordinary combined builds and
compiled blueprint validation remain integration gates.
