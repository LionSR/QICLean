# A polynomial bound at the explicit geometric-tail order

For fixed real b,W,xi with 0 < b < 1, W > 0 and xi > 0, and fixed natural
q >= 1,s,k, the theorem Real.exists_geometric_order_polynomial_bound
chooses natural C >= 1 and p before every natural N. At the actual order

    r_N=max(1,ceil[(log(max(1,N^2))-log(log(1+xi/W)))/(-log b)]),

it proves the natural inequality

    (2s r_N^2 q^r_N)^(2k) <= C(N+1)^p.

There is no supplied order or polynomial bound. The proof includes N=0,
q=1, s=0 and k=0. In particular, the zero power is handled with the same
choice of a coefficient at least one.

Write d=-log b, L=log(log(1+xi/W)), a0=2+abs(L)/d and a1=2/d.
The proof establishes r_N <= a0+a1 log(N+1), including a negative
ceiling argument. It bounds r_N^2 by (a0+a1)^2(N+1)^2 and q^r_N by
exp(a0 log q)(N+1)^p0, where p0=ceil(a1 log q). It then takes

    K=2s(a0+a1)^2 exp(a0 log q),
    C=max(1,ceil(K^(2k))),
    p=(p0+2)(2k).

All these choices precede N. The result is a scalar auxiliary for the
soft heat approximation; it does not prove a physical family theorem,
a bound for degrees growing with length, or a running-time estimate.
No source theorem is marked complete on the strength of this numerical
lemma. The blueprint states the auxiliary with exactly its hypotheses.

## Verification

The final Mathlib-only module passes actual-name strict checking at the
standard default limits in 4.283 seconds. The first complete draft also
passed, in 4.285 seconds; the subsequent check removes an unused import
and an unused local fact. Neither check changes an elaboration limit.
The immutable provider is TNLean 8f85b0be007c009ca208e82cbec4873dff2427e6
with its own QICLean package cc2569b660d020e2946cdc979488d639add36d9f.
The source-only worktree starts at eb79d840b8c9be27c0420b941a88093f316e3cc6;
its toolchain and two build/dependency inputs match the provider byte for
byte. The selected production module imports only Mathlib, so it needs
no old QICLean declaration or artifact override.

An imported foundation inspection passes in 3.865 seconds and reports only
propext, Classical.choice and Quot.sound. Temporary command sources are deleted afterwards.
Generated imports, complete source/blueprint synchronization and reverse
coverage, reader prose, proof integrity, whitespace and the repeated-pattern
scan pass. The theorem and proof were rendered for reader inspection.
Ordinary combined compilation and the complete compiled blueprint remain
parent integration checks. No provider, cache, pin or Mathlib source was
changed or rebuilt.
