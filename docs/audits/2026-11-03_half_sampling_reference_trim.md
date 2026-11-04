# A half-dimensional sample with original-target reference trimming

This contribution proves one fixed-input sampling step. A single measurable
Haar event for the original target certifies the same sample and common-family
image for every improving target. No intersection of center-indexed measurable
events is assumed. The actual sample has size `q / (2 * D^2)`; its image and its
literal collective trim have dimension at most `q / 2` for every unitary.

The intermediate hypotheses remain explicit: the common family improves every
nearby target; the original-to-improving-target error is at most
`((3/100)/D^2)^2/100`; the reverse error is at most `1/200`; and
`D^12 * Delta <= 1/100000`. On the success event, the image retains the
quantitative error `4 * Delta / alpha^2` for every improving target. Its error
for the original target is at most `27/2500`. A two-sided original-target
reference of error at most `1/100000`, with threshold budget
`xi * sqrt(m * b) <= 1/1000`, gives final error at most `3/200`.

The accompanying bootstrap note distinguishes repeated resampling from the
sample-once Figure in the paper. These conditional one-step results neither
construct the physical family and reference nor establish the repeated loop,
its adaptive probability, or a running-time bound.
