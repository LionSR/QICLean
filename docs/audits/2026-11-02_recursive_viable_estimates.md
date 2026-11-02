# Estimates for recursive viable-subspace constructions

This contribution supplies finite-dimensional estimates for powers of
spectral filters, sampling a fixed viable space, and combining spaces on
disjoint regions. The recursive construction for an actual quantum chain
belongs to TNLean and is not a conclusion of these estimates.

## Operator powers and sampling

An actual decomposition \(K=\sum_{i=1}^N A_i\otimes B_i\) gives
\[
K^a=\sum_{w\in\{1,\ldots,N\}^a}A_{w_1}\cdots A_{w_a}
 \otimes B_{w_1}\cdots B_{w_a}.
\]
The factors need not commute. A spectral filter with squared suppression
\(\Delta\) has squared suppression \(\Delta^a\) after taking its power.
The span of the corresponding images of a \(\delta\)-viable space has
dimension at most \(N^a\dim S\) and viability error at most
\(\Delta^a/(1-\delta)^2\), for \(\delta<1\). A common polynomial
decomposition supplies one family before the power and input space are
chosen.

For a fixed input of dimension \(Q\), the construction samples
\(\min(s,Q)\) coordinates after a Haar unitary. If \(Q\le s\), the
sample equals the input for every unitary. Otherwise a measurable event
uses the corrected complex-sphere failure estimate. The actual sampled
word-image span has dimension at most \(N^a\min(s,Q)\), for every
unitary; its viability follows on the success event. The error-reduction
property is an explicit hypothesis of this composition and is proved
separately for a spectral filter. No adaptive measurability or probability
estimate for an entire random tree is asserted.

For integers \(D\ge2\), \(r\ge1\), and \(0<\beta\le1\), put
\[
A=1+\log r+\log D+\log(1/\beta),\qquad
s=\lceil4096rA\rceil,\qquad
a=\lceil\log_D(D^2s)\rceil.
\]
Then \(s\le4097rA\), \(D^2s\le D^a\le D^3s\), and a family of at
most \(D^2\) operators gives dimension at most \(D^6s^3\). The same
sampling size bounds the corrected failure probability by \(\beta\)
for every input dimension \(Q\le D^{12}s^6\) at viability error \(1/4\).
These are auxiliary numerical choices, not the printed algorithm's
parameter prescription.

## Regions and trimming

The tensor-coordinate identifications retain the full exterior of a
region when computing a Schmidt rank. Viable spaces on two disjoint
regions merge into a space on their union, with the sum of the two
viability errors. The global target may be entangled across all factors.
The results also identify the full regional space and bound the dimension
of the merged space.

For \(D_{\mathrm{ref}}\ge1\), the radius
\(\xi=(1000D_{\mathrm{ref}}\sqrt{L+1})^{-1}\) reserves error at most
\(1/250\) for any number of cuts up to \(L\). The inequality
\(\xi^2 R\le M\) gives the integer rank bound
\(R\le10^6D_{\mathrm{ref}}^2(L+1)M\). The squared reference dimension
is retained.

## Source and verification

The source is ALVV, arXiv:1602.08828v2: tensoring (`l:t`, lines 500–523),
sampling (`l:rs`, 530–558), error reduction (`l:er`, 597–622), collective
trimming (`lem:trimming`, 660–697), and the merge analysis (1662–1677 and
1777–1817). The corrected sampling count is documented in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.

Sixteen modules are extracted from local revision
`e51354163d2dd9cf2a15d65722c544c6b4736182` onto main
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`. Existing main definitions and
proofs are retained. All 56 new public declarations have active blueprint
references. The blueprint/source check passes, active labels are unique,
and all references in the changed sections resolve. The sections pass the
pinned formatter and individual-file LaTeX lint. No forbidden proof token
is introduced.

The mathematical revision `000d65159e3f737730a3f6c718584300456b3440`
passed all hosted checks in
[run 41491122088](https://github.com/LionSR/QICLean/actions/runs/41491122088),
including the full Lean build, strict changed-module checks, compiled
blueprint declarations, policy checks and blueprint compilation.
All 56 new public declarations were also audited locally against the
compiled exact revision used by TNLean. Each depends only on the standard
kernel axioms `propext`, `Classical.choice` and `Quot.sound`.
The new mathematical sections were rendered and inspected in a PDF excerpt.

The shared helper in `EnergyTruncation.lean` proves Hermiticity of a
centered, partially clipped sum and replaces three repeated downstream
proofs. It is included in both the hosted verification and the axiom audit.
The subsequent verification-record commit changes only this document.
