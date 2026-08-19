<p align="center">
  <b>Finite-dimensional quantum-channel theory, formalized in Lean 4.</b>
</p>

[![PR CI](https://github.com/LionSR/QICLean/actions/workflows/pr-ci.yml/badge.svg)](https://github.com/LionSR/QICLean/actions/workflows/pr-ci.yml)
[![Compile blueprint](https://github.com/LionSR/QICLean/actions/workflows/blueprint.yml/badge.svg)](https://github.com/LionSR/QICLean/actions/workflows/blueprint.yml)

QICLean is a [Lean 4](https://lean-lang.org/) library, built on
[Mathlib](https://github.com/leanprover-community/mathlib4), that formalizes
finite-dimensional quantum-channel theory: Kraus, Choi, and Stinespring
representations, Kadison-Schwarz inequalities, quantum Perron-Frobenius
theory (irreducibility, primitivity, peripheral spectrum), GKSL semigroups,
the quantum Wielandt inequality, and entropy. The organizing source is
M. Wolf's lecture notes, *Quantum Channels & Operations: A Guided Tour*.

## Relation to TNLean

QICLean was extracted from [TNLean](https://github.com/LionSR/TNLean), which
formalizes the fundamental theorem of matrix product states and remains the
home for matrix-product-state and tensor-network content. TNLean depends on
QICLean as an ordinary Lake package, pinned to a released tag, and re-exposes
the channel-level results it needs (`Kraus.mapLM`, `IsIrreducibleMap`, ...)
through a single sanctioned bridge module,
`MPS/Core/TransferChannel.lean`, on its own side. QICLean never imports
TNLean or any matrix-product-state vocabulary; the dependency runs one way.

Both libraries track the same Lean and Mathlib toolchain in lockstep. See
[`docs/UPGRADE_RUNBOOK.md`](docs/UPGRADE_RUNBOOK.md) for how a Mathlib bump
propagates from this repository to TNLean.

## Building

```bash
# Fetch pre-built Mathlib artifacts first; never build Mathlib from source
# in a fresh clone.
lake exe cache get
lake build
```

See [`CLAUDE.md`](CLAUDE.md) and [`docs/lake_build_cache.md`](docs/lake_build_cache.md)
for the full cache policy and local development workflow.

## License

QICLean is released under the Apache License 2.0, matching TNLean's license
(see [`LICENSE`](LICENSE)). The lecture notes under `Notes/` that motivate
much of this library's organization are a separate source; see the notice
alongside them for their terms.
