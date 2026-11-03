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

## Reuse and ownership

The elementary-tensor membership and containment criteria move unchanged
from `ViableSubspaceSpectralProjector` to `TensorFamilyImage`, keeping their
names, signatures and proof text. The existing coarse nested reduction and
the new normalized nested reduction call the same tensor-image containment
lemma. No existing public statement changes, and no duplicate containment
proof is introduced. The new mathematical statements belong to QICLean.

## Verification

Private strict checks used immutable TN
`d316e8cbe52bd5f12bcfbeec687d1dbef7633586` and its own QIC
`d1317fdb229a1048cc65ec5ab1912403ab6bcbc0`. All changed dependencies were
explicit source/object overrides; the changed existing importer was freshly
elaborated. Selected sources, objects, root inputs and the warmed Mathlib
object were hashed before and after every check. No provider, dependency
cache or Mathlib artifact was changed.

| Module | Strict time | Guarded source/object pairs |
| --- | ---: | ---: |
| `TensorFamilyImage` | 4.903 s | 2 |
| `ViableSubspaceSpectralProjector` | 5.372 s | 4 |
| `ViableSubspaceSharpTensorReduction` | 4.280 s | 6 |

An imported inspection of the three new declarations, two moved declarations
and four existing error-reduction/spectral declarations passed in 4.070 s
with seven guarded pairs. Every inspected declaration depends only on
`propext`, `Classical.choice` and `Quot.sound`. The temporary inspection
source was deleted. Source-level blueprint synchronization, reader-facing
prose and whitespace checks passed. The scoped tactic-pattern scan found
no repeated pattern at its configured thresholds.

The ordinary combined build, affected-importer checks and compiled blueprint
verification remain required after integration. In particular, unchanged
importer objects compiled against the old tensor-projector source must not
be reused above the changed dependency.
