# Paper-gap registry verification for the regional contribution

Merge `5181e09d` incorporates published parent `7b153216`. The parent adds the
OpenAI source key to the paper-gap registry and records its verification.
`texra-blueprint paper-gaps check` exited zero on the regional branch: all
60 referenced slugs resolve and all note names carry registered source keys.
The exact raw output and its SHA-256 hash are recorded here.

The production, test and blueprint source trees are byte-for-byte unchanged
from published regional revision `4b49e011`. `checks.json` records their Git
tree objects and the SHA-256 hashes of the regional module, uniform-region
test, generated entropy import, chapter inclusion, unique fragment and source
comparison. The six immutable regional bindings remain at `9366e598`.
The earlier Lean and PDF/web verification, including the complete compressed
PDF command output, is retained. A new proof or book build is unnecessary for
this registry and evidence change.
