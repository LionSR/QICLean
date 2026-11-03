# A simultaneous soft-family parameter choice

For each local dimension q >= 2, positive real gap g, and natural exponents
a,b,c, the theorem Real.exists_soft_family_calibration chooses one natural
u >= 2. Its window, Taylor order, scale, filter degree and cutoff are exactly
ell=u^8, m=u^10, t=3m, k=u^16 and T=u^9. The count is the natural number

    D=(mk+1)(qk)^(36ell+4(k/ell)).

The norm ceiling and precisions are evaluated at those same choices:

    M=3t(1+log m)+4ell+34,
    tau=1/(D^a M^b),
    xi=min(1,tau*g^2/(20000(M+g+8))).

The conclusion derives all positivity and cutoff requirements, both coarse
five-region residual bounds with right side tau*g/1000000, and the exact
squared Chebyshev shrinking bound

    [2 exp(-2k sqrt((g/2)/(M+xi+4+g)))]^2 <= 1/(D^12 M^c).

No count, residual, spectral comparison or parameter-feasibility premise is
present. No chain length or target dimension enters the selection of u.
The exponents may be zero; there is no upper bound assumed on g.

## Proof and scope

The actual natural quotient is k/ell=u^8. The count and norm satisfy

    log D <= u^8(log 2+40log q+666log u),
    M+R <= u^10(47+R+90log u), for every R >= 0.

Mathlib's logarithm versus positive real-power asymptotic, composed with
natural coercion, supplies both M+5+g <= u^12 and one aggregate logarithmic
budget. Their finite intersection with the explicit threshold conditions
chooses a single u. A squared comparison then bounds the square-root
Chebyshev exponent; both residual estimates and the filter estimate use
that same count and scale. There is no successive choice of a tolerance
and a count which would change that tolerance.

This is a new sufficient numerical auxiliary, not the printed fourth-order
choice of ALVV or a quantitative gap or running-time estimate. The separate
scope note docs/paper-gaps/alvv16_soft_family_calibration.tex distinguishes
a prospective half-dimension resampling and original-target trimming
procedure from the paper's sample-once iteration. Neither procedure's
probability analysis follows from this scalar theorem alone. The blueprint
states exactly this numerical theorem under its own label.

## Verification

The final production source passes actual-name strict checking at the
standard default limits in 4.930 seconds. The held provider is TNLean
6dcb693b498041f9f0e2efb8df37a5474aac2b17 with its own QICLean package
79fb1403dd2ec8ca448204f89ccef73c1a77f509. This source-only worktree begins
at that exact QICLean revision, with all three toolchain/build inputs
byte-identical. The new module imports only Mathlib. Its selected closure
therefore contains no QICLean or TNLean declaration or artifact override.

An imported inspection of the public theorem passes in 3.468 seconds and
reports only propext, Classical.choice and Quot.sound. An earlier temporary
inspection printed the same foundations but was rejected for a missing
module docstring; it is not counted as a successful strict audit. Temporary
command sources are deleted after the inspection. All incomplete-proof
diagnostics are retained under /tmp; no elaboration limit was increased.

Generated imports, source/blueprint synchronization and reverse declaration
coverage, reader prose, proof integrity, whitespace and the repeated-pattern
scan pass. The theorem and its proof, and the complete separate scope note,
were rendered for reader inspection. Ordinary combined compilation and
complete compiled blueprint declarations remain parent integration checks.
No provider, build cache, pin or Mathlib source was modified or built.
