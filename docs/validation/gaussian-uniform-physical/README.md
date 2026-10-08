# Combined uniform physical-buffer Gaussian render

This focused render binds to source revision
`d44122632c6d7d1b2d17a5d889fc8fe10bbb846e`. It combines the unchanged
physical-buffer-overlap and doubled-gap prerequisites, Gaussian filtering
including its physical-buffer subsection, parameter choice, generic uniform
approximation, and the final physical-buffer uniform theorem. All six leaves
are copied byte for byte. Only the external fixture's router and PDF title
change. Earlier frozen render evidence is untouched.

The [public correspondence](public-correspondence.json) records that draft
[PR #620](https://github.com/LionSR/QICLean/pull/620) published source commit
`003cd1fe3999756bd3bd01d0170793b5273ae739` with the same exact tree,
`8eb40f1385380b29d19e409510219cbceba15843`. This does not relabel the
local render commands or claim a build or CI result at the public commit.

The [verification](verification.json) passes for 15 PDF pages and six static
HTML pages. All 111 declaration links occur in both outputs, including all 52
public declarations parsed from the eight Gaussian modules. All 107 source
labels resolve in HTML and PDF; 441 HTML fragment links and 110 PDF internal
links resolve. The 63 labelled equations each have their own environment,
HTML display-block anchor, and distinct PDF destination. There are no missing
anchors, duplicate HTML IDs, unresolved references, or TeX layout errors.
Parsing source declarations checks identity and coverage, not Lean proofs.

The [visual review](visual-review.json) covers PDF page 3 (the reused Tenkz
compression diagram), page 13 (parameter bounds and the generic uniform
statement), page 14 (the final physical-buffer theorem and proof), and page 15
(bibliography only, with no theorem or proof continuation). All are readable without clipping or overlap. In particular, the final forward and
adjoint estimates have separate numbers 1.62 and 1.63; the error sum is 1.64.
Other pages were checked automatically, not visually.

The Tenkz sweep passes with one picture, zero hard findings, and zero
advisories. It performs no hard equation-group comparison because the inherited
picture lacks equation scope. The environment lacks `dvisvgm`; its existing
PDF-to-SVG fallback succeeded. Inherited font-map and title-page-destination
warnings are disclosed in [commands.json](commands.json). No render or
verification attempt failed. The [manifest](focus-manifest.json) records exact
source, support, and fixture hashes; the results also bind the PDF, HTML, SVG,
and inspected page images.

To reproduce, activate an existing blueprint Python environment, configure the
TeX search tree and writable cached formats, and set `TENKZ_ROOT` to the
repository's pinned Tenkz revision. Then run:

```sh
bash docs/validation/gaussian-uniform-physical/run.sh "$SOURCE_ROOT" "$NEW_EXTERNAL_FIXTURE"
```

`prepare.py` refuses to overwrite an existing fixture. `run.sh` contains the
same render commands executed for this record; it was syntax checked, while
those commands were run individually. `verify.py` checks current source hashes
against the fixture before inspecting outputs. For the recorded visual review,
rasterize PDF pages 3, 13, 14, and 15 at 1500 pixels along the long edge. Generated
PDF, HTML, SVG, images, and raw logs remain in the persistent external fixture;
only small text scripts and results are committed.

This is focused PDF and static HTML verification. It does not establish
full-book rendering, live browser or MathJax behavior, responsive layout,
remote declaration-URL availability, or any new Lean/Lake/checkdecls result.
It does not repair or reassess the separately held #604 prose/provenance work
or its known base-CI failures.
