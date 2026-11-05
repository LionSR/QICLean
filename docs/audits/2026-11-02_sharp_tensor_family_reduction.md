# Normalized error reduction for a finite tensor family

Let a finite tensor decomposition be given by
$K=\sum_i A_i\otimes B_i$ on $E\otimes F$. For a retained subspace
$S\subseteq E$, the actual retained-factor image is $V=\sum_i A_iS$.
The shared containment theorem proves
$K(S\otimes F)\subseteq V\otimes F$.

Suppose $T\subseteq T_+$, $KT\subseteq T$,
$K(T_+^\perp)\subseteq T^\perp$, and $K$ has minimum norm gain one on $T$
and squared norm contraction at most $\Delta\ge0$ on $T_+^\perp$.
If $S$ is $\delta$-viable for $T_+$, with $0\le\delta<1$, then
$V$ is $\Delta\delta/(1-\delta+\Delta\delta)$-viable for $T$ and
$\dim V\le |I|\dim S$. The single-target statement is an active corollary.
The operator need not be the identity or have a constant eigenvalue on $T$.
For a spectral filter whose minimum low-band gain is $\alpha>0$, the
corresponding normalization uses squared contraction $\Delta/\alpha^2$;
that rescaling is not silently identified with the unnormalized contraction.

This refines the projection argument in ALVV, arXiv:1602.08828v2,
Lemma `l:er`, lines 597–622, and the nested targets of Theorem
`t:aisgapless`, lines 1037–1041. It is a bounded generic estimate, not the
construction of a physical filter or of the interleaved merge tree.
In particular, the first random sample can have very small target overlap.
The reference and clipped-target accuracy needed to control an actual trim
at that stage must be calibrated to that overlap; a fixed constant reference
error cannot be assumed sufficient merely because it suffices after a
complete powered-image improvement.
