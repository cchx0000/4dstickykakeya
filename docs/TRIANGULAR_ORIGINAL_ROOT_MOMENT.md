# Original low moments for arbitrary Borel triangular sources

The source and trajectory hypotheses are those of the checked
[triangular escape](TRIANGULAR_BOREL_FROSTMAN_ESCAPE.md). The actual finite
source sigma may be coupled; only its domination by a finite product
reference with bounded scalar Lebesgue densities is used. Write
mu_t=(a -> b(a)+t a)_#sigma and

    Z_r(t,a)=mu_t(B(b(a)+t a,r)).

The root and the neighbor use the SAME actual sigma. The time law is ordinary
Lebesgue measure on the supplied fixed positive interval J. No cutoff or
conditioning replaces this root/time law in the conclusions below.

## Saturating the original heavy-root bound

Fix 0<s<1. The uniform scalar estimate has already derived a finite constant
H bounding the sum of three native potentials on sigma x dt, independently
of the Borel intercepts. For any real cutoff N>0, the good part of each slice
has ball mass at most D N^3 2^(3s) r^(3s), while the integrated bad mass is
at most H/N. The symmetric-ball argument applies at threshold B when twice
that good-ball bound is at most B.

Choose the positive finite ENNReal cutoff that makes this constraint an
equality. This is allowed because the cut and Markov lemmas accept arbitrary
real/ENNReal heights, not just integers. The result, for EVERY r>0 and finite
B>0, is

    (dt x sigma){Z_r>B}
       <= min(M, C_tail r^s B^(-1/3)),

where M=|J| sigma(univ) and
C_tail=2H (2D)^(1/3) 2^s. All constants are finite and derived from the stated
source data. There is no assumed tail, energy, or charge input in the final
triangular caller.

## Layer-cake without a power loss

For 0<theta<1/3, normalize the tail using
A=(C_tail+1)r^s and split the layer-cake integral at B=A^3. Below that level
use the finite total mass M; above it use the cubic-root tail. Both integrals
converge, since theta>0 and theta<1/3. Thus one finite C_theta works at every
radius:

    integral_J integral Z_r(t,a)^theta d sigma(a) dt
       <= C_theta r^(3s theta).

This improves the earlier elementary cutoff optimization, whose exponent
was divided by 1+3theta. It is a genuine low moment of the unmodified
original law. Coincident points retain infinite potential in the auxiliary
argument, and the source-density/energy proof discharges the nullity issue.

For beta<3, select s with beta<3s. Markov then gives heavy-root mass at most
C_theta r^((3s-beta)theta), so dyadic summability follows with positive decay.
The earlier explicit power theorem is retained, rather than replaced.

A standard ball-smoothing comparison converts the checked root moment to
an averaged L^q estimate, 1<q<4/3, with arbitrarily small power loss as s
approaches one. That smoothing comparison is described here as a consequence;
it is not an additional Lean declaration in this checkpoint.

## Formal interface and scope

`root_tail_moment` proves the general layer-cake calculation, including the
ENNReal case. `triangular_root_moment` defines the literal root-ball mass,
proves its measurability, constructs the saturating cutoff, and discharges
the uniform potential bound from Borel triangular source data. The final
public theorem is
`StickyKakeya4.TriangularRootMoment.exists_triangular_original_root_moment_bound`.

These two modules contain ten proved declarations. This is the desired
continuum original-root estimate for the triangular special class. No
triangular representation, approximate chart decomposition, or equivalent
estimate has been derived for an arbitrary sticky selector. The original
main theorem's project-axiom dependency remains open.

Executed repository checks: strict source and proper import axiom readback
passed with only the standard logical axioms. See
`verification/rank-one-moment-checkpoint.json` for exact hashes and logs.
