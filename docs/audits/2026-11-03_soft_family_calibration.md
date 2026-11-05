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
scope note docs/paper-gaps/alvv16_bootstrap_constants.tex distinguishes
a prospective half-dimension resampling and original-target trimming
procedure from the paper's sample-once iteration. Neither procedure's
probability analysis follows from this scalar theorem alone.
