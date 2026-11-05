# A common polynomial for the explicit refinement expression

The new numerical theorem fixes gamma,g,u,Ktree,Kref and the integer filter count D
before choosing its positive coefficient and natural exponent. Length L, multiplicity r,
spectral width A, precision eta, actual reference budgets and sample size come afterward.
It assumes exactly the scalar reference profiles and sample inequality and derives the
bound on the entire recorded product. No physical approximation or running time is assumed
or concluded by this numerical auxiliary.

The common variable is Z=(L+1)(r+1)(1+1/eta). The existing cubic/quartic inverse-accuracy
bounds and r(L+1)≤Z place both reference profiles below b0+log(Z^5). The existing
integer-power reference estimate gives Btree,Bref≤Cb Z^(5p0). The proof then derives
common≤Cb Z^(5p0+2), N≤CN Z^3 and count≤Ccount Z^6. The final exponent is
10p0+23, equivalently the natural expression ((5p0+2+3)*2)+(1+6*2) used in the proof.
The coefficient is selected before every variable in Z. The exact algebraic definitions
of Cb,CN,Ccount and p0 are recorded in the blueprint.

This is an auxiliary to ALVV, arXiv:1602.08828v2, `t:alg1`, lines 1777–1817.
The physical same-output application is owned by TNLean. This scalar theorem does not
identify the modified tree with the printed algorithm or supply a success probability,
source energy-estimation invariant, gap-sharp bound or computational running time.
