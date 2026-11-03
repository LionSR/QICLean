# The finite identity for partial replacements

The existing `sum_centered_sub_partially_replaced_eq` in EnergyTruncation becomes public
at its current owner. The only Lean source change is removal of the private modifier;
the signature and proof are unchanged. Its existing restricted-norm consumer and every
other public declaration of the module remain unchanged. The public identity permits
reuse when identifying the actual selected regional soft sum with a finite MPO assembly,
without repeating the finite additive proof.

Strict checking of the actual owner used the immutable warmed TNLean provider
f7bae89a06741bb61820b50cd4b421a2d42951e7 and its own QICLean package
00ca963e4a79afd68d9d6f875dd468a21f1dccdd, with selected source/object/configuration and
warmed Mathlib guards. It passed in 6.746 seconds. The imported foundation audit of the
exposed identity and existing restricted-discrepancy theorem passed in 4.208 seconds,
with only propext,
Classical.choice and Quot.sound. All check outputs remain under /tmp; no provider or
cache was changed and no Mathlib source was built. No fixtures are committed.

This is an additive identity supporting ALVV, arXiv:1602.08828v2,
Corollary `c:goodagsphardtrunc`, lines 979–1005. It does not supply an MPO, physical
residual, spectral comparison, GEN construction or running-time bound. Source-to-blueprint synchronization, added-prose and whitespace checks
pass. Ordinary combined
builds and compiled blueprint checks remain required after adoption.
