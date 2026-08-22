# Getting started with QICLean

This page is for a newcomer who wants to build the library, find a
particular result, or make a first contribution. It assumes familiarity
with Lean 4 and Mathlib, but not with this repository.

## What QICLean is

QICLean formalizes finite-dimensional **quantum-channel theory** in Lean 4
on top of Mathlib. It covers the Choi, Kraus, and Stinespring
representations of completely positive maps, the Kadison-Schwarz
inequality and the multiplicative domain, quantum Perron-Frobenius theory
(irreducibility, primitivity, peripheral spectra), continuous one-parameter
(GKSL) semigroups, entropy, and the quantum Wielandt inequality. The
material is organized to follow M. Wolf's lecture notes, *Quantum Channels
& Operations: A Guided Tour*, as closely as the underlying Lean development
allows.

QICLean was extracted from [TNLean](https://github.com/LionSR/TNLean),
which formalizes the fundamental theorem of matrix product states and
remains the home for matrix-product-state and tensor-network content.
TNLean consumes QICLean as an ordinary Lake dependency pinned to a released
tag; QICLean never imports TNLean, and its channel and Wielandt theory
never depends on matrix-product-state vocabulary, so the dependency runs
one way. See the "Relation to TNLean" section of the top-level
[`README.md`](../README.md) and
[`docs/UPGRADE_RUNBOOK.md`](UPGRADE_RUNBOOK.md) for how the two
repositories stay on the same Lean/Mathlib toolchain.

One extraction-era exception remains mid-dissolution:
`QICLean/Kraus/TensorCompat.lean` still declares a handful of genuinely
matrix-product-*state* definitions (`GaugeEquiv`, `SameMPV`, `mpv`) under
`namespace MPSTensor`, kept only so the rest of the `QICLean.MPS`
compatibility layer could dissolve. A paired TNLean pull request re-homes
this content in TNLean's own tensor-network layer, after which a QICLean
tag removes the file. New contributions should not add to it.

## What you need

- [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager.
  It reads [`lean-toolchain`](../lean-toolchain) and installs the pinned
  version (`leanprover/lean4:v4.34.0-rc1`) automatically.
- [Visual Studio Code](https://code.visualstudio.com/) with the
  [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4),
  or another editor with Lean 4 language-server support.
- `git`.
- Several gigabytes of free disk space: the prebuilt Mathlib cache and the
  local build artifacts (`.lake/`) are both large.

## Build

Fetch the prebuilt Mathlib cache **before** the first build. Skipping this
step makes `lake build` compile Mathlib itself, which takes hours instead
of minutes on ordinary hardware.

```bash
git clone https://github.com/LionSR/QICLean.git
cd QICLean

# Do this FIRST. Skipping it rebuilds Mathlib from source.
lake exe cache get

# Only after the cache fetch succeeds:
lake build
```

Then open the folder in VS Code; the Lean 4 extension picks up the
toolchain and starts the language server automatically.

To check a single file during development:

```bash
lake env lean QICLean/Path/To/File.lean
```

## Find your way

The library loads as a single import:

```lean
import QICLean
```

The table below lists one file per area as a starting point. All paths are
relative to the repository root and were checked against the source tree on
this branch.

| Area | Module | What is there |
|---|---|---|
| Channel definitions | `QICLean/Channel/Basic.lean` | `IsPositiveMap`, `IsCPMap`, `IsChannel`, and the basic theory of density matrices (Wolf Ch. 3 and 6) |
| Choi representation | `QICLean/Channel/ChoiJamiolkowski.lean` | The Choi matrix and the Choi-Jamiolkowski correspondence (Wolf Prop. 2.1) |
| Kraus representation | `QICLean/Channel/KrausRepresentation.lean` | The Kraus representation theorem (Wolf Thm. 2.1) |
| Stinespring dilation | `QICLean/Channel/Stinespring.lean` | The Stinespring dilation theorem (Wolf Thm. 2.2) |
| Kadison-Schwarz | `QICLean/Channel/Schwarz/KadisonSchwarz.lean` | The Kadison-Schwarz inequality (Wolf Ch. 5, Eq. 5.2) |
| Fixed points / irreducibility | `QICLean/Channel/Irreducible/Basic.lean` | `IsIrreducibleMap`, unique-fixed-point results; the entry point to the quantum Perron-Frobenius layer (Wolf Ch. 6) |
| GKSL semigroups | `QICLean/Channel/Semigroup/Basic.lean` | Dynamical semigroups and their generators (Wolf Ch. 7, Prop. 7.1) |
| Entropy | `QICLean/Entropy/VonNeumann.lean` | Von Neumann entropy |
| Quantum Wielandt theory | `QICLean/Kraus/Wielandt/` | Span growth, rank-one extraction, rectangular span, and the quantum Wielandt inequality, over finite Kraus families (Wolf Ch. 6; Sanz-Pérez-García-Wolf-Cirac, arXiv:0909.5347) |

The [blueprint](../blueprint/) is the mathematical map of the library: it
states every definition and theorem in ordinary mathematical language and
links each one to its Lean declaration. There is no published blueprint or
API-documentation site yet, so build it locally:

```bash
lake build
cd blueprint
leanblueprint checkdecls
leanblueprint web   # or: leanblueprint pdf
```

`blueprint/src/content.tex` orders chapters to follow Wolf's lecture notes;
the `chNN_` prefix on each chapter file is a stable identifier inherited
from TNLean and does not track that order (see
[`blueprint/README.md`](../blueprint/README.md) and
[`docs/blueprint_style_guide.md`](blueprint_style_guide.md)).

**A namespace note.** QICLean was cut out of TNLean's Lean tree, and a few
declarations still carry TNLean's `MPSTensor` namespace rather than a
channel-generic one, pending a rename. `QICLean/Kraus/Injectivity.lean`
says so directly in its module docstring: the exact word-span API is
already stated under `namespace Kraus`, but the established injectivity
and normality declarations remain under `namespace MPSTensor`. The
top-level `QICLean/Wielandt/` directory is the clearest example of this —
most of its declarations still open `namespace MPSTensor`, unlike the
channel-generic `QICLean/Kraus/Wielandt/` directory referenced in the table
above, which covers overlapping ground without that legacy namespace.

## A first reading path

These five files build on each other in the order given, and are a
reasonable way to see how the library is put together:

1. `QICLean/Channel/Basic.lean` — the definitions everything else is
   stated over (`IsPositiveMap`, `IsCPMap`, `IsChannel`).
2. `QICLean/Channel/ChoiJamiolkowski.lean` — the Choi matrix, imports
   `Basic.lean`.
3. `QICLean/Channel/KrausRepresentation.lean` — the Kraus representation
   theorem, imports `Basic.lean` and uses the Choi-Jamiolkowski
   correspondence to relate `IsCPMap` to Choi positivity.
4. `QICLean/Channel/Stinespring.lean` — the Stinespring dilation theorem,
   imports both of the above.
5. `QICLean/Channel/Irreducible/Basic.lean` — irreducible CP maps, the
   starting point for the quantum Perron-Frobenius layer used throughout
   the Wielandt directory.

## Contributing

Shared conventions (Mathlib style, naming, documentation, PR review, proof
integrity, prose style) live in the `lean-conventions` skill of
texra-ai/texra-lean-skills, auto-installed via `.claude/settings.json`;
QICLean-local addenda are in `docs/project_conventions.md`. Repo-specific
convention documents:

| File | Covers |
|---|---|
| [`docs/project_conventions.md`](project_conventions.md) | QICLean-local addenda to the shared conventions |
| [`docs/blueprint_style_guide.md`](blueprint_style_guide.md) | LaTeX conventions, `\lean{}`/`\leanok` tags, `\uses` rules |
| [`docs/UPGRADE_RUNBOOK.md`](UPGRADE_RUNBOOK.md) | The two-repository Mathlib upgrade procedure with TNLean |

The remaining TNLean convention documents (`CONTRIBUTING.md`,
`glossary.md`, `pr_review_management.md`, `ci-automation.md`,
`lake_build_cache.md`, `tactic_development.md`, `tactic_patterns.md`)
were not carried into this extraction; see [`../CLAUDE.md`](../CLAUDE.md)
if one of them turns out to be needed.

**PR titles** follow `type(scope): description`, with `type` one of
`feat`, `fix`, `refactor`, `doc`, `style`, `ci`, `chore`, and `scope` a
shortened module path with the `QICLean/` prefix dropped — for example
`refactor(Channel/Irreducible): tighten the growth lemma hypotheses`.

**What CI runs**, under `.github/workflows/`:

- `pr-ci.yml` — the main pipeline on pushes and pull requests: builds the
  library and runs the text-based style linter, checks that Lean
  compilation times for changed modules stay under their limit, enforces
  module-length and numbered-sequel-file policies, and compiles the
  blueprint (including its reader-facing prose checks).
- `blueprint.yml` — compiles and deploys the blueprint (web and PDF) on
  pushes to `main` that touch Lean or blueprint files.
- `docgen.yml` — a weekly (and manually triggerable) full API-documentation
  build.
- `import-completeness.yml` — checks that the generated `QICLean.lean`
  aggregator is complete after a change to it.
- `update.yml` — a manually triggered dependency-update check.
- `create-release.yml` — creates a release when the version changes.

## Troubleshooting

**`lake build` seems to be building Mathlib from source.** This means the
cache fetch was skipped or failed. Stop the build, run `lake exe cache get`,
confirm it reports a successful fetch, and only then run `lake build`
again. A fresh clone with no cache can otherwise take hours instead of
minutes.

**Toolchain or Mathlib version errors.** `lean-toolchain` pins the Lean
version and `lakefile.toml` / `lake-manifest.json` pin the Mathlib
revision; both must match what `elan` and `lake exe cache get` fetched. If
you are also working in a TNLean checkout, see
[`docs/UPGRADE_RUNBOOK.md`](UPGRADE_RUNBOOK.md): the two repositories are
required to sit on the identical toolchain and Mathlib revision outside a
short, deliberate transition window, and a mismatch tends to surface as a
confusing kernel or elaboration error rather than an obvious version
conflict.
