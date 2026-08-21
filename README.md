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
positive-but-not-completely-positive maps, and entropy. The organizing
source is M. Wolf's lecture notes, *Quantum Channels & Operations: A Guided
Tour*.

## Relation to TNLean

QICLean was extracted from [TNLean](https://github.com/LionSR/TNLean), which
formalizes the fundamental theorem of matrix product states and remains the
home for matrix-product-state and tensor-network content. TNLean depends on
QICLean as an ordinary Lake package, pinned to a released tag, and re-exposes
the channel-level results it needs through a sanctioned bridge module on its
own side. QICLean never imports TNLean or any matrix-product-state
vocabulary; the dependency runs one way.

Both libraries track the same Lean and Mathlib toolchain in lockstep. See
[`docs/UPGRADE_RUNBOOK.md`](docs/UPGRADE_RUNBOOK.md) for how a Mathlib bump
propagates from this repository to TNLean.

## Getting started

```bash
# Fetch pre-built Mathlib artifacts first; never build Mathlib from source
# in a fresh clone.
lake exe cache get
lake build
```

See [`CLAUDE.md`](CLAUDE.md) for the full cache policy and local development
workflow, and [`docs/getting_started.md`](docs/getting_started.md) for a
fuller guide: what to install, a table of entry-point modules, a first
reading path through the source, how the blueprint is built locally, and
the contributing conventions carried over from TNLean.

## License

QICLean is released under the Apache License 2.0 (see
[`LICENSE`](LICENSE)), matching TNLean's license.
