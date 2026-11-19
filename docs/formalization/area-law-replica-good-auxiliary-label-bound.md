# The good auxiliary label on an excitation component

Let $B$ be the actual excited subset of the $k$ copies, let $r=|B|$, and
construct the coordinate split by enumerating $B^{\mathsf c}$ first and $B$
second. Its good-copy group has $k-r$ coordinates, by the finite complement
cardinality formula. Write $F_g$ for the good-copy label observable on an
auxiliary system with one-copy coordinate set $C$, and $P_\lambda$ for its
whole-copy central label projection. Set
\[
 \tau=\log d_\lambda-r\log|C|-\log\binom{k}{r}.
\]
For an original vector $v$ satisfying the literal auxiliary label equation
$(I\otimes P_\lambda\otimes I_D)v=v$, the actual component
$w=(R_B\otimes I)v$ satisfies
\[
 \tau\operatorname{Re}\langle w,w\rangle
 \le\operatorname{Re}\langle w,(I\otimes F_g\otimes I_D)w\rangle.
\]
The arbitrary register $D$ retains every other auxiliary factor. The label
equation for $w$ is proved from disjoint action; it is not assumed. The
compressed label inequality is lifted by the identity on both spectator
registers and evaluated on $w$. Hermiticity of the actual whole-label
projection and its derived fixed-vector equation remove the two compressed
projection factors.

The construction is algebraic for arbitrary $\Omega\in\mathbb C^A$:
$R_B$ has factor $I-|\Omega\rangle\langle\Omega|$ on $B$ and
$|\Omega\rangle\langle\Omega|$ on its complement. When $\Omega$ is a unit
ground vector, the existing sector theorem identifies this literal operator
as the orthogonal excitation projection. No normalization, nonempty register,
independence or iid hypothesis is needed for the present inequality. Zero
components and zero copies are included. The real logarithm is total, with
$\log0=0$.

The source is *A two-dimensional area law from a global spectral gap*,
pinned `openai/math` revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`07-comparators.tex`, lines 441–456 and 481–493, equation
`comparator:good-auxiliary`. The only support premise is the source
whole-label equation on the original vector. The numerical high-label
threshold and subsequent metric estimate remain separate; no physical
excitation operator is commuted through a band metric.
