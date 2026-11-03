# A natural sample with strict dimension decrease

This contribution follows the scalar estimates at QICLean
`7c6e7a5173819c2a623f6f97b65841a5fd3c5e05`, based on the exact TNLean
companion revision `ba01733099b5a18bed5c9bfb62f95f175b4c9b57`.
The source is ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`,
lines 1112–1128. The corrected proof uses a natural half-size sample.

## Mathematical conclusion

Let the original targets be Gplus and Gminus, and the improving targets
Thi and Tlo. Assume the original upper space approximates Thi with error
1/200 and Tlo approximates the original lower space with error 1/200.
A fixed family of D squared operators improves every viable input for Thi
toward Tlo. Let W be 3/200-viable for Gplus and Q its actual dimension.

The new calibrated theorem assumes natural count parameters satisfying

    log D >= 100, 1 <= r, dim Thi <= r,
    log Dnext <= (13/6) log D,
    r D^3 < p <= Q <= r Dnext^3,
    D^12 Delta <= 1/100000,  Delta >= 0.

It derives both numerical conditions for the actual sample size
`s = p / (2 * D^2)` in natural division. The conclusion retains the actual
Haar unitary, its s-dimensional sample in W, and the image under the chosen
operators. That image has dimension at most p/2 and strictly less than p.
It is 3/200-viable for the original lower target. Its sharper error is
`2 * (Delta / alpha^2 + 1/200)`, with `alpha = 3s/(25Q)`.

The direction of closeness is explicit in the mathematical chapter and the
new local-correction note. The original upper-target dimension bound also
bounds Thi, by the existing dimension theorem for approximation error below
one. Physical window comparisons and the same-family count/suppression
calibration must still be proved by a physical application. The complete
minimal-dimension induction and low-density entropy theorem remain separate.

The existing integer-quotient helper is exposed with its proof unchanged.
Its two existing consumers and the new natural-sample theorem share that
proof; no second natural-division argument is added. The conditional
nested-target theorem is selectively restored from the preserved source,
then checked against the current companion definitions.

## Verification

The final strict actual-name source checks pass:

| Module | Seconds |
|---|---:|
| ViableSubspaceBootstrap, unchanged proof with one public helper | 48.985 |
| NestedSamplingNaturalParameters | 39.745 |
| ViableSubspaceNestedSampling | 31.148 |
| ViableSubspaceNestedCountSampling | 17.134 |

The first module is close to the unchanged 50-second limit. Ordinary
quiet integration timing remains required; no threshold is increased.
An imported inspection of all four public declarations passes in 30.231
seconds, using only `propext`, `Classical.choice` and `Quot.sound`.
The first temporary inspection had only a missing module-documentation
header; its attempt is retained and the corrected inspection passes.
The diagnostic commands and temporary inspection source were deleted.
No test fixture is added.

Private checks read the immutable warmed QICLean revision 24a2ee58. Every
selected unchanged dependency and all three package inputs are checked
byte-identical to ba017330. Current changed dependencies and every selected
importer above them are separately re-elaborated and supplied explicitly.
The source, object, input and Mathlib hashes are recorded before and after.
This verification leaves the ordinary combined build and compiled
mathematical declaration checks pending.

Source-only mathematical declaration synchronization, reader prose,
whitespace, paper-gap references and the tactic-pattern scan pass.
The focused two-page chapter excerpt and two-page correction note were
rendered and all four pages visually inspected, with no final layout
warnings. Evidence is under `/tmp/qiclean-natural-sampling-20261102` and
`/tmp/qiclean-natural-sampling-docs-20261102`.

The source-only worktree has no Lake build directory. No common cache was
modified and no Mathlib source was rebuilt by these checks.
