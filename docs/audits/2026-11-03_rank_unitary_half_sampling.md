# The literal half-sampling and reference-trimming step under product Haar measure

The new theorem Entropy.exists_measurable_randomRangeSubspace_half_trim_event
uses the existing Matrix.rankUnitaryProduct d and Matrix.rankUnitaryHaar d.
For an arbitrary matrix P on Fin d, it takes q=P.rank and the actual
Matrix.rangeOrthonormalBasis of its range. A fixed finite coordinate
isometry transports that basis onto W, the image of the actual range.
No orthogonal-projection hypothesis, prescribed rank equation, or arbitrary
basis comparison is supplied.

The sample is literally Matrix.randomRangeSubspace P s U, transported by
that coordinate isometry, where s=q/(2D^2) is natural division. The image is
the span of the same fixed family applied to that sample. The output is the
existing collective trim of the standard orthonormal basis of that same
image. The fixed-rank theorem is invoked once with the mapped canonical
range basis, retaining all its target-family and reference hypotheses.

One measurable event is pulled back from that invocation through evaluation
at q. The existing measure-preserving coordinate marginal gives the exact
measures of that event and its complement. No second measurable hull is
chosen, and no measurable selection of events as P varies is asserted.
On the event, the same image has error 4Delta/alpha^2 for every improving
target, error 27/2500 for the original target, and its literal trim has
error 3/200 for that original target. For all seeds, including those outside
the event, the sample lies in W and has dimension s, and both the image
and output have dimension at most q/2. The true output-failure set has outer
measure at most the unchanged bootstrapFailure D q (dim Graw).

The improving family, nearby targets and original-target reference remain
explicit intermediate hypotheses. They are not physical conclusions of
this auxiliary, and no adaptive joint law or running-time bound is claimed.
The index set of improving targets need not be finite: the one original-
target event gives all the target conclusions by deterministic transfer,
without a measurable intersection over that index set.
