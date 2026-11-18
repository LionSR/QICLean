# Finite spatial Hamiltonian truncation (issue #1115)

The new `ManyBody/Dynamics/TruncatedEvolution.lean` compares the canonical
Heisenberg evolutions of two Hamiltonians. It introduces no alternative support,
interaction, restriction, or evolution definitions. The regional conditional
expectation from `GraphLocalization` is not used as a surrogate for truncated
evolution.

The interaction-picture derivative gives a reusable comparison from a uniform
commutator bound on the interval between zero and time t. Only the reference
Hamiltonian must be Hermitian in this bridge. The finite-sum version then combines
with the existing two-region numeric Lieb–Robinson estimate. The spatial theorem
retains precisely the interaction terms whose supports are subsets of L.

Assumptions are finite site and term types, finite local basis types, Hermitian
terms, support diameter at most R, support cardinality at most vR, and per-site
sum of term norms at most b. No separate graph-degree assumption is used: the
support cardinality bound is supplied directly. If every exterior site has
distance at least d+R from the observable support S, the result is

    error ≤ 4 |S| ‖A‖ M_deleted |t| exp(4 vR |b| exp(2 μ R) |t| − μ d),

for μ ≥ 0. Empty supports, disconnected graphs, and negative times are allowed.
For fixed positive μ and uniformly bounded other parameters, the displayed
bound decays exponentially in d. The theorem does not provide a uniform bound on
M_deleted, establish an infinite-system limit, or prove a boundary-weighted
summability theorem. In particular the per-site budget alone does not turn the
deleted total norm into a volume-independent constant. This is a derived finite
consequence of the existing GraphPropagation estimate, not a new attribution of
an infinite-volume theorem to its sources.

## Circuit integration acceptance plan

PR #1116 owns the active circuit production files. No changes to those files are
part of this increment. After that PR is integrated and its interfaces reviewed:

1. Identify the canonical Interaction associated with the placed local terms of
   `norm_dual_trotterCircuit_sub_le_restrict`.
2. Prove that its kept-term sum is the Hamiltonian of the existing `restrictTo`
   family, preserving all support and Hermiticity hypotheses.
3. Rewrite the existing exact-evolution remainder using that equality and, if
   necessary, symmetry of the norm difference; apply the spatial theorem.
4. Add the resulting bound to the existing product-formula error, without adding
   another circuit, support, or evolution representation.
5. Test the no-deletion case, negative and zero times, and disconnected regions;
   state any additional uniform-volume assumptions explicitly.

This plan is not a formal circuit-composition theorem. Issue #1115 remains open
for that integration and sharper volume-controlled estimates.
