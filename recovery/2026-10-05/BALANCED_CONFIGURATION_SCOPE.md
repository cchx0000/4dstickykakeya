# Actual balanced configurations: verified scope

`NativeBalancedConfiguration.exists_balanced_configuration` is a proved
conditional construction under positivity of the fixed-compact extremal
exponent kappa. It does not conclude kappa=0 or the final Kakeya theorem.

Fix tau>0, window>0, and finite menu sizes d,g with d+g>0. The theorem first
chooses positive e,zeta and an integer L, with zeta=window*e/32 and
zeta<=tau/256. For every positive requested eta and thickness cutoff it then
constructs an actual normalized native source D in the fixed compact class,
with smaller positive input eta and thickness delta. The source has its
proved original near-extremal volume and multiplicity bounds.

It next constructs one original line-label backbone R, common height, exact
original cells, dyadic depth, half-cardinality and half-shading retention,
original density/CW, and all-dyadic ancestor populations. R is fixed before
the requested finite schedule and symmetric/reflexive relation menu. For each
such chosen schedule/menu, one actual original incidence subset E is selected
and used at every scheduled scale. No single E for all possible different
menus is asserted.

At N=2^m, set rho=64/N and eps=N*delta/64, so rho*eps=delta exactly. The
three separately defined quantities have the following checked bounds:

- The physical full coarse shadow on R/E has multiplicity between
  delta^tau*rho^(-kappa) and delta^(-tau)*rho^(-kappa).
- Every active actual normalized local source has multiplicity between
  delta^tau*eps^(-kappa) and delta^(-tau)*eps^(-kappa).
- Every active OLD parent incidence family has its original incidence/support
  ratio between the same two eps powers.

The two local quantities are not silently identified. Their comparison and
the physical coarse readbacks were proved on the same E. Actual native local
and coarse admission, exact local source traces, original relation uniformity,
the explicit source-derived radix budget, and coarse upper bounds at every
window scale are retained in the output.

Verification: official Lean 4.33.1, explicit -j1, autoImplicit=false and
warningAsError=true. Source and separate imported-axiom checks both exited0.
All three public declarations use only propext, Classical.choice, Quot.sound.
Source SHA256: 71d9045dd41e976cb930e6133237dc1550a5895b590fef770e55f84aea90bbdb.
The exact commands, source, readback and results are in
`verified/native_balanced_configuration/`.

Remaining work includes the all-middle-scale consumer, the original-to-relative
double-projection comparison for (113), subsequent geometric configuration
arguments, and the contradiction excluding positive kappa. The existing final
published-volume axiom has not been removed.
