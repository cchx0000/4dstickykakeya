# Time averaging gives a finite physical source-bush cover

Date: 2026-10-02.

## 1. Status and scope

The local time-average and finite half-edge source-cover results are now
Lean-verified in:

- `Thm_StickyKakeya4_time_averaged_bush.lean`: 12 declarations
- `Thm_StickyKakeya4_maximal_disjoint_cover.lean`: 4 declarations
- `Thm_StickyKakeya4_quantitative_bush_cover.lean`: 9 declarations

The arbitrary-tail `quantitative_bush_resolution` module adds four certified
declarations. For `0<theta<1`, it constructs floor `r theta M/(2L)`, count
`2L/(r theta M)`, exact kept-plus-tail original measure, tail at most theta M,
and retained mass at least (1-theta)M. The original-data
`actual_half_edge_bush_seed` composition adds two certified declarations and
removes the given-root premise using the original sticky datum and front deficit.

All 31 declarations passed strict compilation and public readback with only
`propext`, `Classical.choice`, and `Quot.sound`. The principal endpoint is
`exists_quantitative_source_bush_cover`. The elementary marked-label,
quarter-tail two-sided, and three-time observations below are explained at
source level; they are not claimed as additional certified declarations.

This is a finite geometric construction on the original graph. It does not
prove the global cross-cap payment, termination of the later bush routing,
or the final Sticky Kakeya theorem.

Write

    Pi_t(a) = b(a)+t a,
    Bush(t,p,R) = {a : |Pi_t(a)-Pi_t(p)| <= R}.

The map b is measurable, so these are measurable source sets. The probe p
used to specify a bush need not be the original target of every edge later
assigned to that bush.

## 2. Exact origin in the actual collision kernel

For a probability source nu, the manuscript's actual fixed-angle graph is

    h_r(a,a') = 1_angle(a,a') (C_tau r)^(-1)
                integral_J 1_{|Pi_t(a)-Pi_t(a')| <= r} dt.

If M is its edge mass, Tonelli gives the exact identity

    C_tau r M
      = integral nu(dp) integral_J
          nu{a : angle(a,p), |Pi_t(a)-Pi_t(p)| <= r} dt.

Thus some actual probe and time give an r-bush of source mass comparable to
rM, with constants depending only on the normalization and time window.
There is no additional time-buffer issue in this identity: the averaging
already uses the actual interval J. A threshold strictly below the average
avoids assuming that a supremum is attained.

If g<=h_r is an old subgraph, insert the factor g/h_r, defined as zero where
h_r=0, into the time integral. Its value lies in [0,1], its integrated mass is
exactly the old graph mass, and its physical support is unchanged. The same
lower bush-mass conclusion follows.

In particular, when M^2<=C r with a fixed C, the lower bound crM is at least
(c/C)M^3. The manuscript's M^3 bush-mass scale is therefore automatically
available below the square-root threshold, before four-cycles or determinant
routing. For M=r^(chi+o(1)), every fixed chi>1/2 lies in this range eventually.
This is availability of a source bush, not a claim that one bush carries a
fixed fraction of the original joint edge measure.

## 3. Product-dominated original graphs and buffered time averaging

The certified version needs no exact formula for the graph density. Assume

    sigma(univ) <= 1,       Gamma <= sigma x sigma,
    M = Gamma(univ) > 0,    0 < r <= 1.

For Gamma-almost every original pair, suppose its slope difference has norm
at most two, its closest collision time s_* lies in [u,v], and its transverse
residual has norm at most r. Set

    J = [u-1,v+1],       L = v-u+2.

For every t in [s_*-r/2,s_*+r/2],

    |(b(a)-b(a'))+t(a-a')|
      <= |residual| + |t-s_*| |a-a'| <= 2r.

This interval has length r and lies in J. Hence

    r M <= integral_J Gamma{(a,a') : |Pi_t(a)-Pi_t(a')| <= 2r} dt.

Product domination and Tonelli convert the right side into an upper bound by

    integral_J integral sigma(dp) sigma(Bush(t,p,2r)) dt.

The asymmetric version is decisive. If only the original sources are
restricted to a measurable remainder T, then

    Gamma_T = Gamma restricted to T x univ
             <= (sigma restricted to T) x sigma,

and therefore

    r Gamma(T x univ)
      <= integral_J integral sigma(dp)
           sigma(T intersect Bush(t,p,2r)) dt.                 (1)

All original targets remain available. There is no new normalization by the
mass of T or by a descendant edge mass.

For genuinely marked old collision times, the same elementary argument uses
the inherited label directly instead of replacing it by the closest time.
If |a-a'|<=A_0 and the marked time lies in a compact interval I with buffer
delta inside J, take h=r/(A_0+1)<=delta. The time interval of length 2h around
the mark has residual at most 2r. This gives (1) with r replaced by 2h.
Only the new bush radius is enlarged; the original edge errors, times, and
other marks are retained unchanged.

The enlarged averaging interval must be distinguished from the original
unit-segment height interval. The cover theorem produces affine trajectory
bushes at times in J. Using their centers as points of the original unit
front requires the relevant common-slab inclusion separately; the cover
itself does not assert that inclusion.

## 4. Certified finite source-only half-edge cover

As long as the remaining source set T satisfies

    Gamma(T x univ) > M/2,

(1) provides a measurable bush piece

    B = T intersect Bush(t,p,2r),
    sigma(B) >= a,       a = rM/(4L).

Indeed, if every such bush had mass at most a, the average in (1) would be
at most aL=rM/4, contradicting its lower bound greater than rM/2.

Remove B from the source remainder and repeat. The pieces are pairwise
disjoint. Since their masses are at least a and sigma(univ)<=1, no more than
1/a pieces can occur. Equivalently, select a maximum-cardinality admissible
finite family and apply the same argument to its complement. This avoids
an unproved measurable choice of an infinite greedy sequence.

The certified conclusion is a finite pairwise disjoint family F of measurable
sets, with U its union, such that

    every B in F lies in a physical 2r-bush,
    sigma(B) >= rM/(4L),
    #F <= 4L/(rM),
    Gamma(U-complement x univ) <= M/2,
    Gamma(U x univ) >= M/2.

This is a source-marginal cover. It neither freezes, deletes, nor reverses
any original target. It requires no lower bound on original vertex degrees.

For a source of arbitrary finite mass m>0 and original graph mass G>0,
normalize sigma by m and Gamma by m^2. The corresponding unnormalized bounds
are

    sigma(B) >= rG/(4Lm),       #F <= 4L m^2/(rG).

These are source-mass and counting bounds, not a small upper bound on the
mass of U.

## 5. Exact old-edge accounting and the optional induced variant

Enumerate the source pieces B_i and let T_i be the source set before removing
B_i. The actual assigned old measures are simply

    Gamma_i = Gamma restricted to B_i x univ.

Their supports are disjoint, and

    sum_i Gamma_i + Gamma restricted to U-complement x univ = Gamma.

All original pair coordinates and all inherited conditional marks remain
attached. The selected probe p_i is only a label for the physical bush; it
is not substituted for an edge's original target.

For comparison, the weaker induced-graph construction removes both endpoints
from the current remainder. Its exact loss at one step splits into

    Gamma restricted to B_i x T_i,
    Gamma restricted to (T_i minus B_i) x B_i.

These two pieces are disjoint and telescope against the induced remainder.
One may reverse the second piece to put its bush endpoint first, while
retaining its original-root and orientation tags. Forgetting those tags and
merging orientations can double the physical product density. The primary
source-only construction avoids this issue entirely.

### Two endpoint covers, at source level

The same greedy proof can stop when the source tail has mass at most M/4:
use piece threshold rM/(8L), giving at most 8L/(rM) bushes. Apply this proof
once to the original graph and separately to its transpose. If their source
and target unions are S and T, respectively, then

    Gamma(S-complement x univ) <= M/4,
    Gamma(univ x T-complement) <= M/4,
    Gamma(S x T) >= M/2.

The last inequality is just the union bound on the two discarded endpoint
events. It does not provide a single bush pair carrying comparable edge
mass, nor small total masses for S and T. The source quarter-tail bound now also specializes the certified arbitrary-tail
theorem at theta=1/4. The two-sided combination itself is recorded here at
source level, rather than as an additional named Lean declaration.

## 6. Separate three-time observation and the remaining charge problem

There is also a useful raw-cycle estimate, independently checked at source
level. If a physical four-cycle has three pairwise g-separated collision
labels, one of its two opposite-anchor orientations has incident-time gaps
at least g/2 at both free vertices. For a free vertex y contacting anchors
p,q at times s,t, subtraction gives

    (s-t)(a_y-a_p) + (b_q-b_p) + t(a_q-a_p) = e_1-e_2,
    |e_1|,|e_2| <= r.

Thus a_y lies within 4r/g of the anchor-only affine plane

    a_p + span(a_q-a_p,b_q-b_p).

Both free vertices lie in this same at-most-two-dimensional plane tube. If
the direction density is at most D on a bounded chart, and the physical raw
cycle law is dominated by nu^4 for a probability nu, integration gives

    raw three-separated-time cycle mass <= C D^2 (r/g)^2.

The two possible orientations change only C. Conditional probability time
marks add no multiplicity. This estimate does not transfer to an arbitrarily
normalized, stationary, or root-preserving cycle coupling without the corresponding
joint-product domination.

Its time dependence matters. In the sliced planar-radial model
b(a)=(-lambda |a_h|^2 a_h,0), shrinking lambda compresses genuine non-bush
contact-time gaps and phase rank. On fixed separated planar sectors, the selected physical edge family has
mass comparable to (r/lambda)^2, rather than r^2 with a uniform
lambda-independent constant.
For fixed lambda its inverse powers are fixed coarse constants; allowing
lambda to move with r does not establish a fixed-coarse/all-fine
counterexample. Moreover a small M^3 bush can coexist with the non-bush cycle
family, as the time-average argument already guarantees.

The finite source cover establishes real linear retention of original edge
mass in a controlled number of genuine bushes. What remains is to charge the
subsequent near/far, same-window, and cross-cap interactions with the original
joint weights, or to prove a Frostman exit from them. Neither the count
4L/(rM), nor the raw cycle estimate, supplies that global quadratic payment.
