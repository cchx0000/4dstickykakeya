# Transverse original queries and one fixed Cartesian source

The four new modules contain 17 public proofs, all checked strictly with
official Lean 4.33.1 and then through one fresh imported all-public
readback. Every axiom closure contains only propext, Classical.choice and
Quot.sound. The prior common-growth, vector-BSG, robust-Kaufman and
two-projection source hashes all match their frozen manifests.

Start with an actual finite planar P, an actual finite slope set C, and
original subsets Q_c of P satisfying `|Q_c| >= q |P|`. No pairwise overlap
of those subsets is assumed.

The exact identity is

    sum_(a,b,c in C) |Q_a intersect Q_b intersect Q_c|
      = sum_(p in P) degree(p)^3.

Mathlib's finite power-mean inequality gives the lower bound
`q^3 |C|^3 |P|`. If each original h-neighborhood contains at most
`q^3 |C|/2` slopes, the contribution from close first-two slopes is at
most half that quantity. Actual finite averaging therefore chooses
`a,b in C`, `|a-b| >= h`, with third-slope total at least
`q^3 |C| |P|/2`.

Thresholding at `q^3 |P|/4` gives an actual `C0 subset C` with
`|C0| >= q^3 |C|/4`. The fixed carrier is literally

    P0 = Q_a intersect Q_b,

and each retained third query is literally `P0 intersect Q_c`, with at
least `q^3 |P|/4` original points. These are original-source intersections,
not independent replacements for the input queries.

The native version starts from the original slope Frostman law at mesh
delta and the numerical scale condition

    delta <= h <= 1,
    Kc h^s <= q^3/16.

It constructs the required interval counts, then removes the original
h-neighborhoods of both a and b. At least `q^3 |C|/8` third slopes remain;
they stay at distance at least h from a and b. Every third query keeps
the same `q^3 |P|/4` lower count.

The main composed endpoint is
`OriginalCartesianQueryFamily.exists_original_cartesian_query_family`.
Assume also original planar delta-separation, unit point/slope boxes,
delta<=1, and actual projected covers

    |floor_delta pi_c(Q_c)| <= K sqrt(|P|), for every c in C.

It uses the previously proved two-projection construction at the actual
chosen a,b. The fixed real alphabets A,B lie in [-1,1] and are separated
at delta/4. With `D=(6/h+2)^2`, for every retained c it constructs an
actual `G_c subset A x B` satisfying

    (q^3/4) |P| <= D |G_c|,
    (q^3/4) |A| |B| <= D K^2 |G_c|,
    |floor_(delta/4) {u a0+v b0 : (a0,b0) in G_c}|
      <= (8/h+4) K sqrt(|P|),

where `u=(b-c)/(b-a)` and `v=(c-a)/(b-a)`. Both coefficient magnitudes
are at least h/2. Every edge retains an actual point in
`Q_a intersect Q_b intersect Q_c` as its witness. Thus the construction
has one fixed Cartesian source and a positive original third-direction
set, with all density and covering losses derived before any BSG call.

This does not yet prove an approximately closed scalar ring. A subsequent
BSG caller must handle the separation of uA and vB at the chosen mesh,
and preserve the original weights needed for any later nonconcentration
argument. In particular, two-scale regularity of P does not by itself
give the half-dimensional interval profile of each scalar marginal.
That deduction must use the actual restricted graph family or further
source-preserving scale selection. The positive small-s A.3 gain remains
open.
