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

## Verification

The entire actual-name module passes strict checking at the default limits
in 6.801 seconds, against immutable TNLean
8f85b0be007c009ca208e82cbec4873dff2427e6 and its own QICLean package
cc2569b660d020e2946cdc979488d639add36d9f. Its selected closure contains
78 guarded QICLean source/object pairs. The three new fixed-rank supporting
modules use the complete immutable map from the separately frozen
QICLean 7a6e4887f438293742a0cd20df12b9f8edcb5b27; their checked source
bytes match the source-only dependency adoption in this worktree.
All existing selected dependencies use the verified provider.

The source uses only the old public canonical sampler and product-law
signatures. The separately developed requested-rank-size extension is not
mixed into this private check. Its combined ordinary importer verification
remains part of the next parent integration. Initial missing explicit
submodule types and dependent finite-rank transport diagnostics are retained;
no elaboration budget is increased. A private geometric identity first
checks that mapping a basis maps the actual existing random subspace.

The imported public foundation inspection passes in 4.763 seconds and
uses only propext, Classical.choice and Quot.sound; its temporary command
source is deleted subsequently. Generated imports, complete source/blueprint synchronization
and reverse public coverage, reader prose, proof integrity, whitespace and
the repeated-pattern scan pass. The new theorem and proof are rendered
for reader inspection. Ordinary combined compilation and complete compiled
blueprint declarations remain integration checks. No provider, cache,
dependency pin or Mathlib source is modified or rebuilt.
