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
