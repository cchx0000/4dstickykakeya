# Direct heavy-root charge from an actual good/bad decomposition

Date: 2026-10-03. The elementary lemma, original-source application, derived triangular
power bound, and dyadic summability are now Lean-checked. The proof below
also received an independent mathematical audit. The older frozen triangular note contains
a valid low-moment argument; this is a stronger, simpler alternative.

## Symmetric-ball lemma

Let mu=nu+eta be finite Borel measures on a separable metric space. Suppose
nu(B(x,r))<=c for every x, and B>=2c>0. Define the measurable set

  E={x: mu(B(x,r))>B}.

On E one has eta(B(x,r))>B-c. Symmetry of distance and Tonelli give

  (B-c)nu(E)
     <= integral_E eta(B(x,r))dnu(x)
     <= integral eta(B(x,r))dnu(x)
      = integral nu(B(y,r))deta(y)
     <= c eta(univ).

Therefore

  mu(E)<=eta(univ)+nu(E)
       <=[1+c/(B-c)]eta(univ)<=2eta(univ).              (1)

All balls can be open. The set {(x,y):dist(x,y)<r} is symmetric Borel, so its
parameter integral and E are measurable. Closed balls work by the same proof
if the assumed good-ball bound is closed; otherwise use closed(r) contained
in open(2r), changing only the fixed radius constant.

## Actual source/time application

Let mu_t be the unchanged slice pushforward of the original source sigma.
Let a measurable source/time cutoff G_N split it into the actual submeasures
nu_(t,N) and eta_(t,N). Suppose for every t and x,

  nu_(t,N)(B(x,r))<=C N^3 r^(3s),
  integral_J eta_(t,N)(univ)dt<=H/N.

Apply (1) with c=C N^3 r^(3s), B=r^beta whenever 2c<=B. The ORIGINAL heavy-root
source/time mass is exactly

  integral_J mu_t{x:mu_t(B(x,r))>r^beta}dt,

by the defining pushforward; it is at most 2H/N. Joint measurability follows
by integrating the Borel function 1_{dist(P_t(a),x)<r} against the fixed source,
with the measurable cutoff for the good/bad kernels.

If beta<3s choose 0<epsilon<(3s-beta)/3 and N=ceil(r^(-epsilon)). For r<=1,
N<=2r^(-epsilon), and 2C N^3 r^(3s)<=r^beta for all sufficiently small r.
Consequently the original heavy-root charge is <=2H r^epsilon, summable over
dyadic radii. No grid, Holder estimate, independent-marginal replacement, or
conditional success normalization is required.

The triangular reference-potential construction supplies these hypotheses
with constants uniform over its Borel triangular functions. The lemma does
not manufacture such a good/bad decomposition for a general sticky selector.

## Derived Borel triangular endpoint

The final theorem does not assume H, a potential-finiteness statement, or
the displayed threshold condition. `UniformScalarProjectionEnergy` derives
one finite scalar energy bound independent of the Borel intercept.
`TriangularUniformPotentialBound` integrates it over the unused coordinates
and transfers it to the actual dominated source, proving a finite H from
the input densities.

For `0<beta<3`, take `s=(beta+3)/6` and `epsilon=(3-beta)/12`. The actual
proof uses the real cutoff `N=r^(-epsilon)`. Since
`3s-3epsilon-beta=3epsilon>0`, the threshold is valid at all sufficiently
small r. It follows that the literal ORIGINAL source/time heavy event has
mass at most `C r^epsilon`. The finite initial dyadic terms and a geometric
tail then give a finite sum over `r_n=(1/2)^n`.

The four new modules contribute 44 strict theorem readbacks. All use only
`propext`, `Classical.choice`, and `Quot.sound`. Exact commands and hashes
are in `verification/triangular-heavy-charge-checkpoint.json`; the targeted
build passed 8,718 jobs. No energy, potential, or heavy-charge certificate
appears in the final Borel triangular power and summability endpoints.

This closes the original-weight charge for that special class. Nothing here
extracts a triangular representation or an equally effective good/bad
decomposition from the general original sticky hypotheses.

The independently audited cyclic continuation is recorded separately in
[the chart-cover obstruction](CYCLIC_CHART_COVER_OBSTRUCTION.md),
[the Fourier parameter audit](CYCLIC_FOURIER_PARAMETER_AUDIT.md), and
[the genuine product-convolution calculation](CYCLIC_PRODUCT_LQ_INVERSE_AUDIT.md).
These handwritten tests do not have the full front-deficit premise and do
not refute the main theorem; they prevent importing an unproved cheap-chart
or near-no-growth step into the general argument.
