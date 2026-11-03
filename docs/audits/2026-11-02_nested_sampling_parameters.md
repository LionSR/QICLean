# Numerical conditions for sampling between nested targets

This contribution is based on QICLean
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`, the companion revision selected
by TNLean `5fc343a57d70eefd2902780107851ab9b0753a82`.
It adds five scalar lemmas supporting the low-density argument of
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

## Verification and its scope

The final actual-name strict private check passes in 22.512 seconds with
Mathlib's standard linters, strict implicit arguments and warnings treated
as errors. An imported inspection of all five public declarations passes
in 25.882 seconds and uses only `propext`, `Classical.choice` and `Quot.sound`.
The temporary inspection commands were removed after the check. No test
fixture is added to either repository.

The private check reads the immutable warmed QICLean revision
`24a2ee589c5ff8da34a5cc6d8b7026dc7700e929`; this new source imports only
Mathlib. Its toolchain, package configuration and dependency manifest are
byte-identical to the target revision. Selected source, object, input and
Mathlib artifact hashes are recorded. The Mathlib artifact retains SHA256
`9a387323c3dc0909926e9b8e73e1a95905f6666e6a811a44a8fecd8c35f12230`.
This private verification does not constitute a full target-revision build.
Ordinary integration builds and compiled declaration checks remain pending.

Source-only blueprint synchronization, reader-prose and whitespace checks
pass. The tactic-pattern scan was inspected and a candidate comparison
pattern recorded. The two-page chapter excerpt was rendered and both pages
visually inspected; its final rendering has no layout warnings.

Evidence is retained under
`/tmp/qiclean-nested-sampling-numerics-main-20261102` and
`/tmp/qiclean-nested-sampling-document-20261102`.
The preparation worktree has no Lake build directory. No common build cache
was modified and no Mathlib source was rebuilt by this private work.
