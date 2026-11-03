# Uniform polynomial thresholds for the half-size sampling failure

The existing Submodule.bootstrapFailure is retained without any change to
its definition. Its sample dimension is exactly Q/(2D^2), with natural
division. The corrected complex-sphere exponent remains 2r.

The existing proof that the failure is below one already controls the
covering-net base by 21D and gives a logarithmic budget. The strengthened
public theorem Submodule.bootstrapFailure_le_exp_neg_of_ge_mul_pow uses
that proof to show

    bootstrapFailure D Q r <= exp(-Q/(128D^2))

whenever D >= 2 and Q >= max(1,r)D^24. Thus r=0 is included. The old
private strict bound remains an active corollary with its original
signature and threshold Q >= rD^24 for r >= 1. The existing public
quantitative bootstrap theorem continues to use that corollary. The
natural floor estimate, net estimate and logarithmic-budget proof above
the strengthened theorem are unchanged.

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

## Verification

The strengthened owner module and the new parameter leaf pass actual-name
strict checking at the default limits in 9.140 and 5.295 seconds. All four
existing direct production importers pass with fresh explicit overrides:
ViableSubspaceMinimum in 4.904 seconds, ViableSubspaceNestedSampling in
6.020 seconds, NestedSamplingNaturalParameters in 5.193 seconds, and
ViableSubspaceSampleOrFull in 4.954 seconds. No artifact compiled against
the earlier owner is reused as one of these changed importers. The immutable
provider is TNLean 8f85b0be007c009ca208e82cbec4873dff2427e6 with its own
QICLean package cc2569b660d020e2946cdc979488d639add36d9f. This source-only
worktree begins at that exact QICLean commit; the toolchain and two build
inputs are unchanged. No elaboration allowance is increased. Initial
explicit-type errors and a tactic-style warning are retained as failed
checks, not counted as successful strict verification.

An imported inspection of the two new public theorems and the existing
quantitative bootstrap consequence passes in 4.762 seconds, with only
propext, Classical.choice and Quot.sound. Temporary command sources are deleted afterwards.
Generated imports, source/blueprint synchronization and reverse public
coverage, reader prose, proof integrity, whitespace and the repeated-pattern
scan pass. The two numerical theorem statements and proofs are rendered
for reader inspection. Ordinary combined compilation and complete compiled
blueprint declarations remain parent integration checks. No provider,
cache, pin or Mathlib source is changed or rebuilt.
