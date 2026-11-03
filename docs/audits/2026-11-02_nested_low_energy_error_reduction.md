# Error reduction between two low-energy cutoffs

The operator, tensor-containment and spectral arguments now allow distinct
lower and upper targets. For $T\subseteq T_+$, the operator need only expand
on $T$ and contract $T_+^\perp$ into $T^\perp$. It is not required to
contract the intervening spectral band. The resulting error is
$\Delta/(1-\delta)^2$ for $\delta<1$.

This is an auxiliary step for ALVV, arXiv:1602.08828v2, Theorem
`t:aisgapless`, lines 1027–1041. It is not the physical construction of the
filter or a completion of the low-density area law. The new matrix
Chebyshev composition explicitly assumes a common finite polynomial
decomposition. The physical chain argument must derive that decomposition
from its supported interactions. Closed spectral cutoffs and the absence
of a positivity claim for an oscillating Chebyshev polynomial follow the
existing spectral-boundary and Chebyshev-positivity notes.

The existing operator and tensor proofs were generalized, rather than
copied. Their single-target public statements remain unchanged and are
specializations. The old spectral contraction statement also retains its
explicit spectral-gap assumption; the new two-cutoff statement needs none.
The canonical-coordinate argument uses coincident endpoints solely to
identify the actual conjugated eigenspaces, not to assert a gap between
the new cutoffs.

The selective operator and spectral changes were compared with preserved
commit `315f1d9e2d112717b4beb952a5c4aac59f8a40ea`; no old module was
restored wholesale. The matrix composition extracts the generic argument
from the preserved physical-family development at
`ac5bf5c8eab7780f7d11c52b0fdacfd83e3dc091`.

Private strict actual-name checks use fully verified TNLean
`5fc343a57d70eefd2902780107851ab9b0753a82` and its own QICLean
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57` package. The changed-importer
graph includes a fresh check of the unchanged Chebyshev spectral-projector
module and the separately checked public spectral-coordinate exposure.
Selected sources, objects, package inputs and the prebuilt Mathlib sentinel
are guarded before and after checking. Outputs are private; no provider or
build cache is changed. All nine inspected new or refactored declarations
depend only on propositional extensionality, classical choice and quotient
soundness. Diagnostic commands are removed after inspection. Ordinary
full-library and compiled blueprint checks remain for integration.

Final actual-source strict checks:

| Module | Seconds |
| --- | ---: |
| `ViableSubspaceErrorReduction` | 14.121 |
| `ViableSubspaceSpectralProjector` | 5.735 |
| `ChebyshevSpectralProjector` | 4.697 |
| `NestedChebyshevViability` | 11.293 |

The unchanged Chebyshev module is a regression check, not an additional
source change. The public coordinate exposure belongs to the separate
canonical-window contribution `ecfed6e2dd5c3a9a9d84af43686b7f3c978167be`.
The three retained single-target signatures were compared mechanically
with exact `ba01733099b5a18bed5c9bfb62f95f175b4c9b57`.

The final nine-declaration imported inspection passed in 4.641 seconds.
The temporary diagnostic source was deleted afterwards.
