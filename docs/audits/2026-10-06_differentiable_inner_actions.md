# Differentiable inner matrix actions

The new generic theorem extracts one Hermitian H from a pointwise unitarily
inner action alpha_t that is differentiable at zero on every fixed matrix and
equals the identity there. It asserts alpha'_0(M)=i[H,M]. No regularity of the
pointwise unitary witnesses is assumed.

The proof uses X(t)_ij=alpha_t(E_ja)_ia. Differentiating alpha_t(M)X(t)=X(t)M
at X(0)=I gives delta(M)=[Z,M], where Z=X'(0). Adjoint preservation implies
[Z+Z†,M]=0. Thus H=−i(Z−Z†)/2 is Hermitian and i[H,M]=delta(M).

The three matrix-unit declarations move byte-for-byte from the downstream
TNLean.MPS.Symmetry.LocalVirtualGauge module into
QICLean.Algebra.MatrixUnitConjugator, with their names and signatures retained:
- Matrix.matrixUnitConjugator
- Matrix.matrixUnitConjugator_eq_smul
- Matrix.matrixUnitConjugator_intertwines

The paired TN change removes the originals and imports this owner, preserving
its existing continuous local-gauge theorem. No duplication or compatibility
wrapper remains. This QIC branch is based on accepted c61daa23; the paired TN
branch preserves the previously published continuous and periodic batches.

A search of pinned Mathlib calculus APIs found no equivalent extraction theorem.
The implementation reuses the existing matrix-unit identities and the product,
entrywise, adjoint and uniqueness rules for derivatives. No polar decomposition,
inverse of the differentiable intertwiner or general Lie-group theory is needed.

Focused strict direct elaboration and audits of permitted axioms are documented in
the validation JSON. They are not claims of a full Lake/root build. Publication
of QIC must precede a downstream immutable pin update in TNLean.
