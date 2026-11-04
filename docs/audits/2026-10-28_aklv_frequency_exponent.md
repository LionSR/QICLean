# The scalar exponent in the AKLV rank estimate

`Algebra/AKLVFrequencyBounds.lean` proves the numerical estimates needed after
partitioning the actual ordered-word family in AKLV, arXiv:1301.1162v1, Lemma 4.2
(`l:agsp`, source lines 651–663). No operator rank or coefficient decomposition is
assumed or defined in this module.

For \(q\ge1\), \(s\le\ell+1\), and every \(r\le\ell\), the corrected finite
frequency sum is bounded by
\((q(\ell+1))^{3s+6\lfloor\ell/s\rfloor+4}\). The bound is uniform in the degree
\(r\). The theorem also includes the empty sum at \(s=0\), with natural division by
zero equal to zero.

For \(\ell,s\ge1\), the effective width
\(w=\min\{s,2\lfloor\sqrt\ell\rfloor\}\) satisfies \(1\le w\le\ell+1\) and

\[
3w+6\lfloor\ell/w\rfloor+5
\le16(\lfloor\ell/s\rfloor+\lfloor\sqrt\ell\rfloor+1).
\]

These estimates retain the additional `+1` in the corrected commuting-gap binomial
coefficient, documented in
[the existing word-count note](https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf).
The source's optimized exponent is preserved; no exponential-in-degree replacement
is used.

The final source SHA-256 is
`5850198def762d887074db41d55de7479bd9dbd6a1d4eb0806966945757c50ae`.
Its actual separate-module strict check passed in 3.33 seconds, with
`autoImplicit=false`, `relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`,
Mathlib standard linters, and warnings as errors. A temporary imported inspection
of both public declarations passed in 1.78 seconds and used only `propext`,
`Classical.choice`, and `Quot.sound`. No permanent per-theorem fixture is added.

This contribution was checked in the existing canonically seeded environment based
on QICLean main `164c79df`; it imports only Mathlib. The six earlier changed QICLean
mathematical modules retain their recorded full-library and compiled-blueprint
verification. Current main subsequently advanced to `acda92aa`. Ordinary verification
of this new module against the combined current-main contribution remains pending;
no duplicate warming or full build was started here.

The physical shorter-window regrouping and arbitrary-polynomial rank theorem belong
to the separate TNLean contribution. No Mathlib source was compiled, no dependency pin
was changed, and no shared cache was modified by the scalar proof checks.
