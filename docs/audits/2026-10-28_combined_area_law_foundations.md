# Common foundations for the area-law constructions

The immutable revision `98ec7c9f4b75fea27b369b4edac8663b98568eea`
combines the following contributions with QICLean main `acda92aa`:

- Finite matrix moments, sampling, simultaneous word-frequency bounds,
  and the existence of one sample satisfying both matrix and frequency bounds.
- One-marker interpolation, the partition of actual low-frequency word
  coefficients, and the effective-width exponent estimate for AKLV.
- Variable-accuracy low-energy clusters, ground-space coordinate and
  entropy identifications, the cubic dyadic entropy bound, and improving
  families transferred between nearby targets.
- Error reduction between nested low-energy target spaces without a
  gap assumption on the intervening spectral band.

The common main already contains the general matrix Bernstein inequality.
Its dilation, scalar estimates and trace-exponential results are preserved.
The ALVV additions were selected from their original implementation commits;
the removed finite-image rank helper and historical test fixtures were not
restored. Dimension estimates use Mathlib's finite-sum rank lemmas directly.

The worktree was created at exact main `acda92aa` and canonically seeded
from clean, fully warmed hot-main before any contribution was applied.
Toolchain, Mathlib pin and other resolved dependencies are unchanged.
Cache operations and ordinary builds used TNLean's common lock, fetching
and verifying prebuilt Mathlib artifacts before building QICLean.

## Verification

The combined revision passed the full library build (10,344 jobs), strict
checks of 24 changed sources and 16 existing dependent test files, blueprint
synchronization and the compiled blueprint declaration check. The ordinary
combined target build had already passed 3,983 jobs. Neither build compiled
Mathlib source.

A manual imported foundations inspection covered 73 public declarations in
the changed production modules and reported only `propext`,
`Classical.choice`, and `Quot.sound`. Its temporary source and output are
local evidence; no permanent Lean fixture was added. The checked strict
sources used the unchanged package options and a 50-second limit per file.

These results provide common mathematical ingredients. They do not by
themselves prove the physical LVV power-filter application, the ALVV
low-density bootstrap or sampled merge tree, or the AKLV entropy argument.
