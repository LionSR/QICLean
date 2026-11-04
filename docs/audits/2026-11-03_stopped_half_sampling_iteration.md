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
amplification. The distinction is recorded in
docs/paper-gaps/alvv16_bootstrap_constants.tex. No running-time or joint
probability conclusion is asserted here; the all-seed dimension bound and
actual probability argument are separate results.
