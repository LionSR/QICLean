# Physical label moments of an excitation component

The contribution proves the exact iid physical evaluation used in OpenAI,
*A two-dimensional area law from a global spectral gap*, September 24, 2026,
`07-comparators.tex`, lines 556–560, following the regional product argument
at lines 520–549. The pinned manuscript is openai/math
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

For a unit one-copy ground vector on Q×T, an arbitrary original vector with
an arbitrary finite exterior register, and an actual excitation component w,
the literal full rank-one pairing with the good-Q label exponential equals
‖w‖² times its iid regional-density pairing. The regrouping retains the
exterior register, all good complementary T coordinates, and every bad
physical copy. It uses the same chosen enumeration of the good set on Q and T.
The exponent is arbitrary real, so the formula handles both signs. No original
copy symmetry, supplied marginal equation, independence, normalization of w,
or nonzero component is required. Zero-copy and zero-component cases are included.

The proof consumes the previously proved actual regional product marginal,
the standard partial-trace pairing, tensor-factor exponential identity,
tensor-product trace and the usual rank-one norm identity. It introduces
neither a new density definition nor a coordinate-covariance helper.

In the source's three-region physical partition Q×(Y×V), apply the theorem to
Q with complement Y×V, V with complement Y×Q, and Y with complement Q×V using
the corresponding literal coordinate regrouping. This does not replace Y by
a paired outer region or discard a physical factor from the left pairing.

The analytic signed centred label-moment estimate at source lines 227–237
(`comparator:signed-label-moments`) remains separate. The checked development
provides the support-correct Schur remainder moment for L−F and finite iid
surprisal concentration, but no equivalent theorem establishing both signed
centred F exponential rates was found. In particular this identity does not
assume a moment bound, prove that rate, or establish the sharp comparator.
