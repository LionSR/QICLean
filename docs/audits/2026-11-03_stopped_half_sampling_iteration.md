# The actual stopped sampling and trimming iteration

The actual current matrix determines whether another round is taken.
Above a fixed rank threshold, the construction uses the existing canonical
sample at the natural quotient of its rank by 2D^2, applies one fixed
finite operator family and collectively trims the resulting actual image.
The output is the coordinate matrix of that trimmed orthogonal projection.
Below the threshold the current matrix is retained.

The literal iteration has a Borel matrix at every predetermined round.
Two unitary sequences agreeing at all earlier rounds give the same current
matrix. Thus updating the next coordinate leaves the current input fixed.
These assertions apply to arbitrary initial matrices and do not assume a
successful sample or a supplied measurable basis.

The construction uses repeated sampling, in distinction to the displayed
sample-once procedure in ALVV, arXiv:1602.08828v2, Figure fig:merge-prime,
lines 1664–1673. The merge process, lines 711–736, motivates the repeated
amplification. The distinction is recorded in the existing soft-family
calibration note. No running-time or joint probability conclusion is
asserted here; the all-seed dimension bound and actual probability
argument are separate results.

## Verification

The production module passes strict elaboration in 5.850 seconds against
the fully built TNLean 8f85b0be / QICLean cc2569b6 pair, with fresh
rank-dependent sampling and trimming dependencies. Standard linters,
warnings as errors and default proof-resource limits are retained.
The five public declarations pass an imported foundation inspection in
4.748 seconds and use only propext, Classical.choice and Quot.sound.
The temporary inspection source is deleted.

Initial proofs using implicit measurable composition exceeded the ordinary
200,000-heartbeat elaboration limit. Naming the actual input pair and
supplying that map explicitly resolves the reduction cost. The recursion
and its mathematical statements are unchanged; no limit is increased.
Those failed attempts are retained as diagnostics, rather than passing
checks.

Complete source/blueprint synchronization and reverse coverage, generated
imports, reader-facing prose, forbidden-token and whitespace checks pass.
Two definitions and one supporting lemma cover the five declarations.
Their one-page mathematical excerpt was rendered and inspected with no
overfull boxes. The tactic-pattern ledger records explicit measurable
composition and the ordinary equality transport used for earlier seeds.

Ordinary combined build and compiled blueprint verification remain pending.
Private objects remain separate from the ordinary cache. No held provider,
ordinary build artifact or Mathlib source cache was changed.
