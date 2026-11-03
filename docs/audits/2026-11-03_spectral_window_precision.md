# A common positive precision for finite spectral windows

The scalar estimates separate the actual norm and cutoff from their known
ceilings. If 0 <= A <= M and 0 <= c <= R, then the actual lower endpoint
min(c-1,-(A+xi)) produces at most ceil((R+M+xi+1)/(2xi)) windows. This
bounds the literal finite-window loss by one common envelope. When
0 < xi <= 1, the ceiling estimate gives the upper bound
2xi(R+M+4)/w^2. Hence xi <= beta*w^2/[4(R+M+4)] gives loss at most beta/2.

For M,R >= 0 and w,beta > 0, the minimum of one and that positive
quotient is an explicit positive choice before A or c is known. At
R=4+g, w=g/5 and beta=tau/200, this is exactly
min(1,tau*g^2/[20000(M+g+8)]), with uniform loss at most tau/400.
No matrix, spectral gap, successful comparison, chosen family or supplied
subspace closeness occurs in these numerical hypotheses.

These are auxiliaries for the corrected buffered spectral comparison in
ALVV, arXiv:1602.08828v2, `t:aisefficient`, lines 1412–1420. They do not
assert a physical soft truncation or an improving-family construction.
The general half-error estimate does not need a separate beta-positive
hypothesis: its assumed positive precision budget already forces that
sign. The explicit minimum theorem assumes beta > 0 to prove positivity
of the constructed precision.

## Verification

The new Mathlib-only leaf passes actual-name strict checking at default
limits in 9.084 seconds, using the immutable TNLean provider
88ab31ce57bdbc4bcb65be00055d1db50df4f259 and its own QICLean package
e817ea0a8a46440eddc361d41cc46b9e61ba10f4. It imports no QICLean or TNLean
declaration. Its source-only branch starts at QICLean
45d42c80d5cd20632225a74607e97dae5b9af89c; the toolchain and dependency/build
inputs match the verified package. This checks the new leaf, rather than
claiming an ordinary full build of that source branch.

All five public declarations pass an imported foundation inspection in
18.037 seconds with only propext, Classical.choice and Quot.sound. The
inspection selects the new checked object explicitly; its temporary
command source is deleted. The initial check's deprecated import,
missing order lemma and tactic-layout linter were repaired and are not
counted as successful verification.

Generated imports, complete source/blueprint synchronization, reverse
coverage of all five public declarations, reader prose, proof integrity,
whitespace and the tactic-pattern scan pass. The mathematical lemma and
corollary were rendered together and their one-page layout was inspected.
Ordinary combined compilation and complete compiled blueprint declarations
remain integration checks. No provider, cache, dependency pin or Mathlib
source was changed or built.
