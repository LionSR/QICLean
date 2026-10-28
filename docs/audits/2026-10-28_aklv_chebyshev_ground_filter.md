# The normalized Chebyshev filter from a global gap

`Analysis/ChebyshevGroundFilter.lean` proves the ground-state and shrinking assertions
for the actual polynomial constructed in AKLV, arXiv:1301.1162v1, Section 4,
Lemma 4.1 (source lines 530–583). No spatial rank estimate, approximate projector,
coefficient family or entropy theorem is supplied.

For a Hermitian \(H\), a unit eigenvector \(\Gamma\) of energy \(E_0\), and a global
gap bound \(H-E_0I\ge\gamma(I-|\Gamma\rangle\langle\Gamma|)\), assume
\(\gamma>0\), \(E_0+\gamma\le u\), and spectrum bounded above by \(u\).
For every degree \(\ell\), the theorem constructs a real polynomial \(p\) of that
exact degree, with \(p(E_0)=1\). Its actual matrix \(K=p(H)\) fixes \(\Gamma\) and
satisfies

\[
\|K-|\Gamma\rangle\langle\Gamma|\|
\le 2e^{-2\ell\sqrt{\gamma/(u-E_0)}}.
\]

It preserves the orthogonal complement of \(\Gamma\), and every unit vector there
has output squared norm at most the square of the displayed bound. The source
shrinking coefficient is therefore retained with the correct normalization.

The proof derives the spectral alternative \(E_0\) or \([E_0+\gamma,u]\) from the
global gap. The existing isolated-energy Chebyshev construction supplies the polynomial;
the canonical spectral projection is then identified with the actual rank-one ground
projection. Both multiplication identities \(KP_\Gamma=P_\Gamma K=P_\Gamma\) are
used to derive ground preservation and orthogonal-complement invariance.

The spectral ceiling and gap are the source Section 4 assumptions. This theorem does
not derive them from hard truncation, establish AKLV Theorem 6.1 robustness, choose
parameters satisfying the area-law tradeoff, or prove an entropy bound. The physical
supported-chain rank assertion belongs to the separate TNLean theorem.

The final source SHA-256 is
`5e617faa0a744f6cd4cf806a17c4f8eedee8a225c1e9129e444b4e274667bfa8`.
The actual separate-module strict check passed in 3.85 seconds with
`autoImplicit=false`, `relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`, Mathlib
standard linters and warnings as errors. A temporary imported inspection of the generic
and physical declarations passed in 2.81 seconds and used only `propext`,
`Classical.choice`, and `Quot.sound`. No permanent per-theorem fixture is added.

The check used the existing seeded environment and private temporary objects.
Ordinary verification and compiled blueprint validation of this new module remain
pending the combined companion integration. No Mathlib source was rebuilt, no shared
cache or dependency pin was changed, and no duplicate full build was started.


## Combined ordinary verification

The common revision `b66600027b2e60ccafea43d041d563cdd00cf05b`
passed the full library build, strict checks of the new module and its
canonical import, an actual-import foundations inspection, blueprint
synchronization and compiled declaration checking. The foundations are
exactly `propext`, `Classical.choice`, and `Quot.sound`. The ordinary build
used prebuilt Mathlib artifacts and reported no Mathlib source jobs.
These checks extend the separately verified common foundations at
`98ec7c9f4b75fea27b369b4edac8663b98568eea`; earlier unchanged proofs were
not rewritten.
