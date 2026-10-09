# Fixed-time Poisson counts and uniform order: focused render

The final render was actually rebuilt from the public commit
[`487c65996fa26916d1d1e4b23e277607075035ba`](https://github.com/LionSR/QICLean/commit/487c65996fa26916d1d1e4b23e277607075035ba).
It is not a relabeling of an earlier render. The four count/order leaves plus
one unchanged prerequisite word-law leaf produce seven PDF pages and six static
HTML pages. All seven PDF pages and the generated dependency graph were
inspected as pixels.

All 33 public declarations in the five new production modules are linked exactly
once in the chapter and PDF: 16 multiplicity/count-fiber declarations, six
independent-count declarations, three generic conditioning declarations, and
eight conditional-order/reconstruction declarations. The prerequisite leaf adds
20 distinct links, so the full fixture has 53 public links in the PDF and chapter,
and 159 across the chapter and two dependency-graph pages. All 31 source labels,
including 11 equation anchors, resolve in PDF and static HTML. Both dependency
graphs have 15 nodes and 18 edges, with the same reachability as the 30 explicit
source dependencies; dashed statement and solid proof edges match the source.

There are no overfull/underfull boxes, missing glyphs, unresolved references,
duplicate HTML IDs, or missing local anchors. The initial render identified one
missing static equation anchor in the existing multiplicity leaf. Replacing its
nested cases display with an equivalent single formula and a separate zero-case
sentence fixed the anchor. The original findings and raw artifacts remain
separate from the final public-source render.

The new leaves explain equal atomic masses on a finite event, the non-null
conditional law of the actual word measure, positivity of every count fiber at
positive time, zero conditional measure on impossible nonzero counts at time
zero, and reconstruction from independent counts plus uniform compatible order.
The zero count vector and empty alphabet are explicit. This is a fixed-time
characterization. It constructs no event times, independent increments,
pathwise clock coupling, or locality estimate. The manuscript source is
`09-amplification.tex`, lines 49–54 and 237–253, from the section “Amplifying the
collar estimate,” pinned at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The longer `arealaw-09-amplification-adc7f124.tex` name in the manifest is only the
retained download filename. No tensor diagrams were introduced.

## Verification limits

The HTML checks inspect the actual generated static pages, TeX math payloads,
links, declaration modals, and graph source. A live Chromium launch was attempted
but the executor refused its process socket with `Operation not permitted`,
including the escalated retry. No live-browser, interactive graph, or MathJax
runtime pass is claimed. Remote Lean-document URL availability, a full-book
build, and hosted documentation publication were not checked. This render worker
ran no Lean compiler or CI. Nonfatal inherited font-map/title-page warnings and
unavailable vector-imager warnings are retained in raw logs; they do not prevent
the PDF/static-HTML checks from passing.

## Replay

From the repository root, activate the existing pinned rendering environment:

```sh
export WORKSPACE=/path/to/workspace
source "${WORKSPACE}/glm23-blueprint-env.sh"
export SOURCE_REVISION=487c65996fa26916d1d1e4b23e277607075035ba
export RENDER_DIR=/tmp/poisson-count-order-replay
export XDG_CACHE_HOME="${WORKSPACE}/8766-unitary-evolution-focused/font-cache"
python docs/audits/evidence/poisson-count-order-render/run_render.py
```

Use a fresh `RENDER_DIR`; previous evidence is never overwritten by the replay
runner. The existing render tools, font cache, and pinned manuscript download are
reused. `prepare_fixture.py` copies exact committed leaves and repository render
context, replacing only the chapter router with the documented focused wrapper.
`verify_render.py` checks all source hashes, local anchors, PDF destinations,
public declaration URLs, and graph dependencies. `commands.json` preserves the
actual executed argument vectors, return codes, UTC start times, and raw-log
hashes. Generated binaries and raw logs remain outside the repository.
PDF metadata dates and graph layout ordering can vary between replays; structural
checks and source hashes are the reproducibility contract, not identical bytes.

Run `python3 docs/audits/evidence/poisson-count-order-render/check.py` to validate
the source and text packet without rendering or Lean. A historical checkout can
be checked with `--source-revision 487c65996fa26916d1d1e4b23e277607075035ba`.
The evidence retains 17 final artifact hashes and hashes for the replay scripts.
No downloads, external writes, binary commits, or dependency-pin changes were
performed by this render worker.
