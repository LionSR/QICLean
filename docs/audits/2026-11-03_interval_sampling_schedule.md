# A scalar schedule for finite interval resampling

For fixed q >= 2, D >= 2 and natural leaf width w, the new numerical theorem
chooses natural K,C >= 1 before the length L, target multiplicity r, or any
sampling carrier. It uses the already proved bootstrap threshold at exponent
four and error coefficient eta = 1/q. The source context is ALVV,
arXiv:1602.08828v2, the informal repeated amplification and trimming procedure
at lines 749–755, and the joint merge estimate in `t:alg1`, lines 1777–1817.

## Constants and bounds

`Submodule.exists_uniform_interval_sampling_schedule` invokes
`exists_bootstrapFailure_polynomial_threshold` once at a = 4 and eta = 1/q.
For the resulting K it takes

    C = q^w + 4*D^2*K,
    theta = K*(r+1)*(L+2)^2,
    R = q*L,
    count = max(q^w, D^2*theta),
    Z = (L+1)*(r+1).

The theorem derives theta >= 4D^2 and theta >= 2. For EVERY actual input
dimension Q >= theta, the existing corrected failure is at most
eta/(L+2)^4. Thus its conclusion is usable at varying active ranks; it does
not only evaluate the failure at the threshold itself.

For every s <= L it proves q^s <= q^L <= 2^(q*L). The inequality q <= 2^q
uses Mathlib's `Nat.lt_two_pow_self`. Actual interval configuration counts
follow by the existing cardinality formula and the interval site count <= L.
No interval or second recursive tree is defined in QICLean.

The inequalities L+2 <= 2(L+1) and r+1 <= (r+1)^2 give
D^2*theta <= 4D^2*K*Z^2. Since Z >= 1, the full common count is at most
C*Z^2. The scalar theorem also permits w = 0; the positive leaf-width
condition of a physical balanced recursion is a separate structural input.

## Failure budget and endpoints

The public real and extended-nonnegative-real lemmas both prove

    (L-1)_+ * (q*L) * ((1/q)/(L+2)^4) <= 1/(L+1)^2.

After cancelling q, the numerator is bounded by L^2. The remaining inequality
is L^2*(L+1)^2 <= (L+2)^4. In particular L = 0 and L = 1 cause no division
by zero and give zero on the left. The ENNReal version follows from the
monotonicity and multiplicativity of `ofReal` on nonnegative factors.
It is returned by the uniform schedule in the form needed for the two finite
union counts: at most L-1 parents and R rounds per parent.

These are scalar estimates, not a probability theorem. They can be applied
to the actual guarded Raw-history failure estimates once the corresponding
fixed-child analytic hypotheses have been discharged. Terminal retained-space
viability alone is not substituted for the stronger RawGood history needed
to control the same last untrimmed family image and its energy.

The choices do not use the reference space, sampled output, successful event,
or a carrier chosen from a varying rank. Dependence is polynomial in L and r
at fixed q,D,w; no polynomial dependence in varying w, inverse-gap sharpness,
printed logarithmic threshold, or running-time estimate is claimed.
The existing net-count correction remains recorded in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
