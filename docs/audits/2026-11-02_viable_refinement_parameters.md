# Explicit error and common-threshold parameters

The internal target rho=eta*gamma/(2A+eta*gamma) fits the final projected
trial-space estimate exactly: A*rho/(1-rho)=eta*gamma/2. The one reference
accuracy epsilon=c^2*rho/32768, with c=gamma/A, is positive, at most 1e-4
and within the stable filter-and-trim budget. This relates closeness to
energy without asserting the iteration count printed in ALVV.

The common integer scale is N=ceil(100 D_filter^12/(c*rho)), and the
threshold is xi=1/(1000 max(D_tree,b) N sqrt(L+1)). The all-vector bond b
of the same reference is compared with its dimension r through r<=b.
Both the original tree radius and the final whole-exterior reference
trimming budget follow. The actual source threshold inequality
sqrt(L*r*b)*xi < 1e-4 eta D_filter^(-12) is strict. The explicit D_filter^12
factor is retained; a ceiling chosen only from 1/(c*rho) would not supply it.

These are scalar auxiliaries. Constructing the physical reference and
actual tree and composing their literal iterates with Ritz extraction are
separate. The integer-radius rank conversion already in the library applies
to max(D_tree,b)*N; no per-generator bound is assigned to the entire span
without its additional generator-count factor.

## Verification

The actual Mathlib-only module passed strict checking with package linter
options and warnings as errors in 6.398 seconds, against immutable ordinary
TNLean 71db89efb903199a223ce22a9704d5e5ba3698f4 and its own QICLean
602972abe8a0463ee04c586e029cd73d8ebc894b. Selected root inputs and the
prebuilt Mathlib object were guarded before and after. There are no
QICLean or TNLean source dependencies in this numerical leaf.

An imported foundation inspection of both public theorems passed in
3.648 seconds over the one new selected source-object pair, using only
propext, Classical.choice and Quot.sound. The temporary source was deleted. No permanent fixture or Lake directory is
introduced, no provider/cache is modified, no compiled artifact is copied
and Mathlib is not rebuilt. Ordinary combined library, regression, compiled
blueprint and timing checks remain required after integration.
