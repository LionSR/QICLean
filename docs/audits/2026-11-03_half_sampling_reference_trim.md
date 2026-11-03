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

The three new modules were checked separately against the immutable verified
TNLean provider `8f85b0be007c009ca208e82cbec4873dff2427e6`, with its own
QICLean revision `cc2569b660d020e2946cdc979488d639add36d9f`. The scalar
module uses Mathlib alone and was previously checked against the unchanged
pinned Mathlib sources. Final core and trimming checks took 5.756 and 7.100
seconds. An imported inspection of all six public declarations took 4.744
seconds and found only `propext`, `Classical.choice`, and `Quot.sound`.
Temporary foundation commands were removed. No library cache was written and
no Mathlib source was compiled.

The accompanying bootstrap note distinguishes repeated resampling from the
sample-once Figure in the paper. These conditional one-step results neither
construct the physical family and reference nor establish the repeated loop,
its adaptive probability, or a running-time bound. Ordinary combined library
and compiled-blueprint checks remain part of the subsequent integration.
