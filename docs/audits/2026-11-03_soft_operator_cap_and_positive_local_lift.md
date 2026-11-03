# Soft operator caps and positive regional coordinates

Two finite-dimensional auxiliary statements support the central regional
soft replacement of ALVV, arXiv:1602.08828v2, lines 1152-1173 and
Figure `fig:algo1`, lines 1631-1632. Neither is presented as the efficient
filter theorem.

For a positive matrix A, t>0 and m>=1, the actual finite soft function
satisfies

    h_{m,t}(A) <= t(1+log m)I.

The proof applies the existing corrected scalar bound at each spectral
value and uses the order of the continuous functional calculus. The scale
and order are independent; the printed harmonic-cap error is retained in
[the existing note](../paper-gaps/alvv16_soft_truncation_log_bound.tex).

If a positive matrix X is supported on a region D and norm(X)<=M, there
is an actual positive matrix K on D with norm(K)<=M and X=localLift(K).
Choose one full configuration and restrict to its complementary coordinates.
The resulting principal matrix is positive, and the restricted order bound
X<=MI gives K<=MI and its norm bound. The support identity proves the
exact identity extension. When no full configuration exists, K=0 suffices.
No positive local dimensions or preselected regional matrix are assumed.

Both actual production modules passed private strict checking at default
budgets (4.783 and 4.575 seconds). The imported foundation audit includes
both public declarations and reports only propext, Classical.choice and
Quot.sound. The checked provider is TNLean
20cad76ebfa6e770263c4a5d5333917c5b226ed9 with its own QICLean
98ba564e3c9603dc93d2173e3dc87a85ce750456; selected sources, objects, root
inputs and the prebuilt Mathlib object were guarded. The source-only QICLean
worktree belongs to the primary QICLean repository, not a dependency checkout.
All new proof objects and temporary audit commands are under /tmp. No
provider source or shared cache changed, and no Mathlib source was built.
The manifest records exact hashes and evidence. Ordinary combined and
compiled blueprint checks remain required after adoption.
