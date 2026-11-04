# A natural sample with strict dimension decrease

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

The original upper-target dimension bound also bounds Thi, by the existing
dimension theorem for approximation error below one. Physical window
comparisons and the same-family count/suppression calibration must still be
proved by a physical application. The complete minimal-dimension induction
and low-density entropy theorem remain separate.
