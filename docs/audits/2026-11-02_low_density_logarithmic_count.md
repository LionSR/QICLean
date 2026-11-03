# A regularized logarithmic bound for the actual low-density count

The generic count calculation is separated from the absorption and
suppression argument. Its base estimate is moved from TNLean's private
`log_base_bound` proof, with the statement and proof unchanged and a
descriptive public name. The existing public ceiling bound is reused;
the corresponding private TNLean copy is removed by the companion
consumer change. The new generic count theorem retains both the sharper
linear-in-degree bound used in suppression and the cubic logarithmic
bound used in the final dimension estimate. No physical hypothesis is
an input of these scalar results.

For fixed bandwidth `eta > 0`, define `B = max(12, eta)` and
`F = 102 + log B`. At deficit `0 < v ≤ eta`, the cap
`vbar = min(v, eta/2)` satisfies `vbar ≥ v/2`. Thus
`g = min(vbar/6, 1)` has `1/g ≤ B/v`. Choosing
`m = q * ceil(exp 100)` gives `log m ≤ log q + 101` and meets the
dyadic count regularity. The actual initial count satisfies

    log(D³) ≤ K / v * (1 + log q + log(1 + 1/v))³,

where

    K = 66 * (C + 1) * (6 + 2 * log(C + 1)) * B * F³.

This coefficient depends only on the ceiling constant and bandwidth,
before the local dimension or deficit. The positive regularized
logarithm and consistent power are explained in
`docs/paper-gaps/alvv16_low_density_sampling.tex`.

Both final production modules passed strict actual-name private checks
against immutable TNLean `71db89efb903199a223ce22a9704d5e5ba3698f4`
and its own QICLean package `602972abe8a0463ee04c586e029cd73d8ebc894b`.
The generic count module took 4.533 seconds; the bandwidth comparison
module took 4.391 seconds. An imported inspection of all five new public
declarations, six affected TNLean scalar declarations and the physical
logarithmic corollary passed in 8.705 seconds with only standard axioms.
The temporary diagnostic source was removed. Selected source/object
hashes, root inputs and the prebuilt Mathlib sentinel were guarded.
Source-to-blueprint synchronization and reverse coverage, prose and
whitespace checks passed. Ordinary combined compilation and compiled
blueprint checking remain integration checks.
