# A common polynomial for the explicit refinement expression

The new numerical theorem fixes gamma,g,u,Ktree,Kref and the integer filter count D
before choosing its positive coefficient and natural exponent. Length L, multiplicity r,
spectral width A, precision eta, actual reference budgets and sample size come afterward.
It assumes exactly the scalar reference profiles and sample inequality and derives the
bound on the entire recorded product. No physical approximation or running time is assumed
or concluded by this numerical auxiliary.

The common variable is Z=(L+1)(r+1)(1+1/eta). The existing cubic/quartic inverse-accuracy
bounds and r(L+1)≤Z place both reference profiles below b0+log(Z^5). The existing
integer-power reference estimate gives Btree,Bref≤Cb Z^(5p0). The proof then derives
common≤Cb Z^(5p0+2), N≤CN Z^3 and count≤Ccount Z^6. The final exponent is
10p0+23, equivalently the natural expression ((5p0+2+3)*2)+(1+6*2) used in the proof.
The coefficient is selected before every variable in Z. The exact algebraic definitions
of Cb,CN,Ccount and p0 are recorded in the blueprint.

This is an auxiliary to ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817.
The physical same-output application is owned by TNLean. This scalar theorem does not
identify the modified tree with the printed algorithm or supply a success probability,
source energy-estimation invariant, gap-sharp bound or computational running time.

## Verification and compilation time

The strict actual-module check used immutable warmed TNLean
cd17d76b290c83200b59b48bc816e4856e3c9c1a and its own QICLean package
0c26d87e4efdd19c85aaa402b4c0b153d3f65657. It passed in 27.674 seconds with the default
heartbeat budget and strict package options. This is recorded as a compilation-time
warning; no timing-only retry or increased limit was used. A failed earlier local ring
normalization was replaced by an abstract algebraic identity and structural power rewrites,
without changing the mathematical bound. Later factoring may reduce elaboration time.

The imported audit checks this theorem and its actual dependent physical corollary.
It passed in 8.089 seconds, with only propext, Classical.choice and Quot.sound.
Temporary audit commands and output objects remain under /tmp. Selected source/object,
configuration, warmed Mathlib and changed-importer guards were checked; no provider,
production cache or Mathlib source was modified. No fixtures are committed.

Generated imports, complete source-to-blueprint synchronization, added-prose and whitespace
checks pass; the new contribution has no repeated tactic pattern at the scan thresholds.
The physical blueprint role check also passes. Ordinary combined builds and compiled blueprint checks remain required after adoption.
