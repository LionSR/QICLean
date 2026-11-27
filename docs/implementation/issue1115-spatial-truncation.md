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

## Circuit integration

PR #1117 merged the finite comparison package, and #1116 merged the circuit API.
`Circuit/Simulation/TruncatedProductFormula.lean` now supplies the integration without changing
Core/Sites or introducing another interaction or evolution definition:

1. `sum_place_localFamilyInside` identifies the sum of placed restricted local
   terms with the filtered kept Hamiltonian. The existing API is
   `localFamilyInside`, not `restrictTo`; Hermiticity is not needed for this identity.
2. `norm_heisenbergEvolution_localFamilyInside_sub_le_graphDistance` instantiates
   the canonical Interaction with placed local terms and bounds the exact remainder.
3. `norm_dual_trotterCircuit_localFamilyInside_sub_le_graphDistance` bounds the
   restricted circuit against full evolution without a circuit-light-cone assumption.
4. `norm_dual_trotterCircuit_sub_le_restrict_graphDistance` replaces the exact
   remainder in the existing full-circuit theorem. This version retains its
   additional n*m-fold support-neighbourhood containment hypothesis.

Both circuit estimates add the restricted commutator-sum product-formula error
`2 ‖A‖ (t²/(2n)) c_L` to the explicit truncation bound above, with n > 0 and any
real t. They use finite site and local basis types as required by the circuit API.
The truncation contribution decays with distance under uniform deleted-mass and
other-parameter control; the product-formula contribution separately depends on
c_L and n. No decay of the entire error in distance alone is claimed.

## Remaining work

Issue #1115 remains open for stronger volume-controlled or boundary-weighted
estimates. The integration retains M_deleted explicitly and does not prove its
uniform boundedness, nor an infinite-system limit. Acceptance requires independent
review of the composition and exact-head CI.
