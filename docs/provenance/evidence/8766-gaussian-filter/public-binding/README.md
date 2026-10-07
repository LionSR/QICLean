# Public Gaussian evidence binding

The 15 kernel, 21 matrix-integral, and 2 spectral ledger entries now identify
[public QICLean checkpoint `16b8135`](https://github.com/LionSR/QICLean/commit/16b81356549158a8393aaea5085defd4c5022e71).
Its complete tree is `41d46a48626973c9056f36ca6163fe3b5e23665d`, exactly the tree of
local source checkpoint `90bcaa0d425ad9f7916ce322edfcb229ecec8b9d`.

This binds existing successful evidence to identical public source bytes. It
does **not** claim any command ran at `16b8135`, nor any new Lean, Lake, full-root,
or public CI success. The actual retained checkpoints remain:

- Kernel: production/raw audit at `b45bc4a`; final native target and all 15
  consumer/axiom guards at `e3a17bc`.
- Matrix: final production/native target at `4df73de`; consumers and all 21
  raw/guarded axiom reports at `c5cd255`.
- Spectral: native target, production, consumers, and both raw/guarded axiom
  reports at `03c84b6`.

`manifest.json` records public Git blob identities, source SHA-256 hashes, exact
retained log hashes, actual selected-run revisions and command arrays, and every
unchanged file in the three historical packets. All historical failures and
normalization receipts remain intact. `original-ledgers/` and
`original-checkers/` contain exact pre-binding bytes; the checker compares them
with their blobs in the public checkpoint. `local-source-commit.txt` contains the
raw local commit payload, so its commit ID and tree equality remain verifiable
without fetching or retaining any local-only Git commit objects.

The three existing packet checkers first validate this binding and then run
their original historical assertions against the archived ledger. Current
ledger contents must equal the archived contents except for the public revision
and its explicit explanation. Run each existing packet checker normally, and
run this additional checker with the pinned TNLean schema when available:

```
python3 docs/provenance/evidence/8766-gaussian-filter/public-binding/check_binding.py PATH_TO_PINNED_SCHEMA
```

Validation uses only local reads and read-only Git object queries. The public
commit must be present in the repository. No historical local-only commit is
needed. The ground-estimate ledger and rendering packet are separate artifacts.

`clean-public-validation.json` records successful replay in a fresh depth-1
GitHub checkout at the public checkpoint, with only this metadata overlaid.
All 12 historical local-only commit objects were confirmed absent, and no Git
object alternates were configured. All three packet checkers passed, as did
schema validation of the three current and three archived ledgers against the
pinned TNLean schema. Exact checker outputs are in `validation-logs/`.
