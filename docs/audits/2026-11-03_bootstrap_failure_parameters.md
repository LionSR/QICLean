# Uniform polynomial thresholds for the half-size sampling failure

In Submodule.bootstrapFailure the sample dimension is exactly Q/(2D^2),
with natural division. The corrected complex-sphere exponent remains 2r.

The existing proof that the failure is below one already controls the
covering-net base by 21D and gives a logarithmic budget. The strengthened
public theorem Submodule.bootstrapFailure_le_exp_neg_of_ge_mul_pow uses
that proof to show

    bootstrapFailure D Q r <= exp(-Q/(128D^2))

whenever D >= 2 and Q >= max(1,r)D^24. Thus r=0 is included. The old
private strict bound remains an active corollary with its original
signature and threshold Q >= rD^24 for r >= 1.

The new leaf Analysis/BootstrapFailureParameters.lean proves that, for
fixed D >= 2, natural a and real eta > 0, one natural coefficient K >= 1
can be chosen before all natural r,N,Q. Its explicit choice is

    K=max(D^24,ceil(128D^2(a+abs(log eta)+1))).

It derives from Q >= K(r+1)(N+2)^2 both Q >= 4D^2 and

    bootstrapFailure D Q r <= eta/(N+2)^a.

The proof has no supplied success-probability, floor, net, logarithmic or
large-Q premise besides that single threshold. It includes r=0,N=0,a=0,
and eta>1, and places no upper bound on Q. The coefficient precedes the
length, target dimension and input dimension. It is a sufficient numerical
threshold for the corrected half-size sampling bound, not the printed
optimal logarithmic scale or an adaptive-algorithm probability theorem.
