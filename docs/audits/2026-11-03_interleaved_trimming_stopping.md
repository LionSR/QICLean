# Stopping of the interleaved trimming recurrence

The scalar recurrence is

    u(0)=1-a,
    u(j+1)=Delta*u(j)/(1-u(j)+Delta*u(j))+a/16.

The additive collective-trimming loss is retained at every round. For a
success b=1-u and denominator d=b+Delta*u, the next success is b/d-a/16.
If b<=sqrt(Delta), the hypotheses give 2Rd<=1 and
(Rb+a/16)d<=2Rbd<=b, so success grows by at least R. Once success is at
least sqrt(Delta), the next error is at most sqrt(Delta)+a/16. Small error
then persists. The induction records either small error or success at least
R^j a; it does not require already converged success to keep growing.

For integers D>=2 and s>=1, choose R=D^6, a=3/(32D^12 s^5),
Delta=1/(200000D^12), and k=clog_D(D^2 s). The actual count bound yields
R^k a>=3s/32, hence R^(k-1)a>=3s/(32R)>sqrt(Delta). The penultimate round
therefore reaches the crossing, reserving the final round for error<=1/200.
Every error remains in [0,1). This is the larger integer-round auxiliary
supporting ALVV, arXiv:1602.08828v2, lines 1797–1805, rather than the possibly
nonintegral printed half-logarithmic count. There is no probability or
running-time assertion.

The stopping theorem concerns the scalar recurrence;
physical family iteration, successful sampling and the recursive tree are
separate applications.
