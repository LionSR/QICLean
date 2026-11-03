# A polynomial output bond with the honest variable count

The coefficient and natural exponent in
Real.exists_interleaved_output_polynomial_bound precede length, multiplicity,
count, sample size and requested accuracy. The count D is NOT held fixed
while length varies. Its actual logarithmic constraint logD<=KD*w is used,
where w=1+log r+2log(L+1), and KD is a fixed physical-parameter coefficient.
The nominal sample constraint is the actual upper ceiling bound
s<=4097r(logD+w). These numerical premises are to be discharged by the
physical construction; this auxiliary does not itself choose the output.

## Costs retained

For a common size Z>=(L+1)r with Z>=1, the count and sample estimates give
D<=exp(KD) Z^p and s<=Cs Z^2, where p=ceil(2KD) and Cs=8194(KD+1).
The independent-scale count bound is linearized using the already checked
sixteenth-power lemma; no desired polynomial bound is substituted.

The literal overlap a=3/(32D^12 s^5) and tau=a^2/2^20 have exact reciprocals
1/a=(32/3)D^12s^5 and 1/tau=(2^30/9)D^24s^10. Their bounds retain degrees
24p+20 for inverse clipping accuracy and 12p+10 for ceil(1/a), the tree's
common-radius factor. The final refinement retains actual A,c,rho and
epsilon=c^2 rho/32768. With gamma<=A<=L+1, its inverse accuracies have
the existing cubic and quartic bounds.

Use Z=(L+1)(r+1)(1+1/eta), Q=24p+21 and Y=Z^Q. The already shared
logarithmic-profile lemma applies to BOTH actual reference accuracies at Y.
Both reference bonds are at most CB Z^PB for constants fixed before L,r,eta.
No logarithmic-profile proof is copied. The final common factor remains

    common=max(r^2 Btree ceil(1/a), r^2 Bfinal),
    N=ceil(100D^12/(c*rho)), count=D^6s^3.

The complete recorded MPS bond 10^6(common*N)^2(L+1)count^2 is at most C Z^k,
with k=2PB+60p+43. This is a coarse polynomial consequence at fixed physical
parameters, not the printed sharp count profile, a physical algorithm or a
running-time result. The source is ALVV, arXiv:1602.08828v2, lines 1797–1817.

## Verification

The source stack contains the unchanged reference-profile exposure
b3f27c5d6c2129919e5bddcd954df8772090817e and the count-core source from
b96e17e26f139790912bb395005cb15b416e093b. The latter was selected on this
private branch as e34b4fcc, without changing the frozen original commit.
The source worktree has no .lake and uses the separate QICLean Git common
directory. No provider/cache source or artifact was copied or modified.

The immutable provider was TNLean 20cad76ebfa6e770263c4a5d5333917c5b226ed9,
own QICLean 98ba564e3c9603dc93d2173e3dc87a85ce750456. Actual-name strict checks
used explicit fresh overrides for the count core, exposed reference module
and new cost module. Selected source/object pairs, root inputs, Mathlib
artifact and changed-importer provenance were guarded.

- InterleavedPolynomialCosts: strict 4.318 seconds, 2 protected source/object pairs.
- InterleavedOutputPolynomialBound: strict 9.486 seconds, 5 pairs.
- Imported six-public-declaration inspection: 3.655 seconds, 6 pairs;
  only propext, Classical.choice and Quot.sound. Temporary source deleted.

An initial expanded-monomial calculation exceeded the unchanged default
heartbeat budget. Generalizing the monomial identities before substituting
the defined size variable resolved it; no budget increase was used. The
existing exposed reference module's 31.243-second check remains recorded in
its own audit; it was not repeated for timing alone.

Blueprint/source coverage, generated imports, reader-facing prose, whitespace
and forbidden-token checks passed. The tactic ledger records the shared
monomial algebra and reuse of the existing logarithmic-profile proofs.
Ordinary combined builds and compiled blueprint checking remain integration
gates. The actual new-tree physical polynomial corollary is the next caller;
none is claimed by this numerical contribution alone.
