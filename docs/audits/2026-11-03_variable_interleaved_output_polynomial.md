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
The independent-scale count bound is linearized using the existing
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
