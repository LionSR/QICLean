# Rank-one expansion of transported source matrices

Source revision: `b298f3fb6439c3e149d6788249fae868e3f9ed50`.
Parent revision: `95411dd3d2f08ec2f65c7613ab0b81c330d28f5c`.

`QICLean.ComplexGaussian.sourceTransport_eq_sum_rankOne` expands
`(E ⊗ F) M (Et ⊗ Ft)†` as the sum of the entries of `M` times the
corresponding rank-one endpoint matrices. The two summed coordinate sets are
finite. The four ambient index types may be arbitrary, and the endpoint matrices
need not be isometries or span their ambient spaces. The ket and bra indices
are independent; complex conjugation occurs on the bra endpoint product.

This is a supporting algebraic identity for the sampled-source construction in
the polynomial-PEPS manuscript. It does not assert the compression theorem or
any probability or norm estimate. The proof expands the two finite matrix
products. It was extracted from a checked TNLean draft; its noncomment tokens
are unchanged by its provenance notice and whitespace cleanup. No upstream
OpenAI Lean proof text was reused.

## Verification

The new module and its three enclosing import aggregators compiled directly
with the package options and warnings as errors. All four checks passed without
diagnostics, in 33.494, 12.614, 11.971, 29.693 seconds. The recorded commands and source and artifact
hashes are in `build-commands.json`. This is a direct Lean check against pinned
artifacts, not a Lake build or a CI measurement. The worktree has no `.lake`
directory; existing artifacts were accessed through read-only file links.

The imported theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
All 5,300 imported artifact hashes were checked again at the source pin.
The canonical provenance checker validates the one new exact-source entry,
including its manuscript label. The collision check covers 489 QIC entries;
it does not revalidate the other 488 entries. The unchanged checker and schema
are included under `canonical/`.

From the repository root:

```bash
python3 docs/provenance/evidence/sourceTransportExpansion8769/validate-evidence.py --root .
uv run --no-project --with jsonschema==4.26.0 python docs/provenance/evidence/sourceTransportExpansion8769/check-provenance.py --root . --upstream-root /path/to/openai-math
```

Neither command compiles Lean. The second requires the pinned manuscript
revision in the supplied checkout. Recompilation uses the recorded toolchain,
options and matching dependency artifacts.

## Mathematical documentation

Full source synchronization covers 3,661 blueprint reference entries. A direct
check in the compiled QICLean root finds all 3,629 names in the full declaration
list. This is a compiled declaration-presence check, not Lake's `checkdecls`.
The chapter formatter is idempotent. The focused five-page PDF contains the two
supporting definitions and the new theorem and proof, copied exactly from the
source. Its theorem page was inspected visually; the final TeX log has no
warnings. The focused web check passes on six pages with 95 typeset elements.
This does not claim a full-book render.

The first focused render omitted a supporting definition and therefore had
undefined dependency references. Its logs are retained. The final focused
render includes both supporting definitions and resolves those references.
The web tool writes a focused declaration list; the full source list was
restored before the compiled declaration check.

## Downstream application

The checked TNLean draft `Word.sourceContraction_preparedDensityCoefficient_selected_frames`
uses this identity to expand actual prepared ket and bra words through proper
Schmidt frames. Its source is retained under `consumers/` with a hash. This
reference is not a second QIC theorem or a claim that the TN dependency update
has already been published. The norm-helper predecessor and QIC PR #634 were
not changed by this contribution.

The exact focused excerpt is gzip-compressed under `blueprint/render-inputs/`
to preserve its final blank line without changing the rendered source.
