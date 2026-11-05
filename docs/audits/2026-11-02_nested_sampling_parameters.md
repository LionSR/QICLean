# Numerical conditions for sampling between nested targets

This note concerns five scalar lemmas supporting the low-density argument of
Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2,
Proposition `prop:albootstrap-ld`, source lines 1112–1128.

## Mathematical statement

Suppose the real parameters satisfy
\[
 D\ge8,\quad \log D\ge100,\quad D'>0,\quad r\ge1,\quad Q,s>0,
 \quad t\in\mathbb N,\quad t\le r,
\]
\[
 \log D'\le\tfrac{13}{6}\log D,\qquad
 rD^3<p\le4D^2s,\qquad Q\le r(D')^3,
 \qquad D^{12}\Delta\le10^{-5}.
\]
For \(\alpha=3s/(25Q)\), the conclusion is
\[
 \left(1+\frac2{\sqrt\alpha}\right)^{2t}Qe^{-s/16}<1,
 \qquad \Delta/\alpha^2\le1/400.
\]
The four supporting lemmas derive the squared dimension ratio, the lower
bounds on the sampling fraction, the strict failure bound, and the error
bound. Integer powers suffice throughout; no rounding estimate for a
fractional power is introduced. The covering expression retains twice the
complex target dimension, as required by the existing complex-sphere note.

The actual natural quotient used for the sample must still be shown to
satisfy the displayed lower bound. The physical count family, canonical
low-energy targets and the minimal-dimension induction are also separate.
Thus these lemmas discharge scalar conditions; they do not assert the
physical low-density area law or the existence of a sampled merge tree.
