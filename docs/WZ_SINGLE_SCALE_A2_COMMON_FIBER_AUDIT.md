# What the completed common-fiber count gives beyond A.2

Audit date: 2026-10-04. The frozen thirteen-module common-growth batch is
unchanged. This audit adds one independent, verified geometric adapter,
`OriginalRobustKaufmanImage.lean`, and tests two proposed shortcuts against
explicit original finite configurations.

## Result

The current A.2 graph can yield a weak positive ABC expansion when all its
other losses are smaller than its fixed cap exponent. It does not yet give
an A.3 union gain. The missing deduction is geometric, not a missing
Cauchy count or a missing selection of common scalar fibers.

The completed count, with the notation in `OriginalCommonGrowth.notes.md`,
is

    r tau^6 |C| <= 32 Q Mpack cap |A|,
    Mpack = 1/d + 2.

Here `d` is the lower separation of a retained B secant. The original
radial tube must be bounded at physical width `4 delta/s`, where `s` is
the lower separation of the retained A pair and `delta` is the ABC mesh.
If A.2 supplies `cap = delta0^chi` at width `w0`, it applies to that count
when `4 delta/s <= w0`. Substitution then gives exactly

    |A| >= [r tau^6/(32 Q Mpack)] delta0^(-chi) |C|.

In particular, if the bracket is at least `delta0^(chi/2)`, the result
is a genuine `delta0^(-chi/2)` expansion relative to C. This observation
does not assume A.1. The original mesh `delta0`, ABC mesh `delta`, and
their scale relation must remain distinct if the application uses coarse
representatives.

There is no factor proportional to the reciprocal query width in this
substitution. Decreasing the query width preserves the A.2 cap, but does
not improve it. Nor has a reduction of an arbitrary actual shaded tube
family to this particular vector ABC source been proved. A.3 asks for
growth relative to the number of shading points times the square root of
the number of tubes. Those are different original populations, and
cannot be substituted for A or C just from their cardinalities.

There is a sharper numerical check in the actual rich-class family.
A.2 already bounds its original tube mass by
`m <= delta0^chi |P|`. Thus `|P|/m >= delta0^(-chi)` before any common-fiber
argument. The rich-class construction makes the tube count comparable
to `(|P|/m)^2` up to its recorded losses. Even the optimistic identification
of A with the original union and C with a shading would therefore make
the single-scale substitution reproduce an existing lower bound on
`|P|/m`, with further losses. It provides no extra power above the
shading-population times square-root-tube-count baseline. This test does
not assert that such an ABC encoding has been constructed.

## Exact OS premise and where it is used

OS Definition 4.2 requires both normalized point Frostman counts and
`|Q intersect P_R|_r <= K(R/r)^t` for every dyadic `delta <= r <= R`.
Corollaries 4.9 and 5.32 then provide many directions that work for every
dense subset of the same regular carrier. The allowed projection exponent
is any `v < min((s+t)/2,1)`. The subsets may depend on the direction.
See [Definition 4.2](https://arxiv.org/pdf/2301.10199v4#page=25),
[Corollary 4.9](https://arxiv.org/pdf/2301.10199v4#page=26), and
[Corollary 5.32](https://arxiv.org/pdf/2301.10199v4#page=51).

In the actual application, (5.30) controls consecutive angular
populations, (5.31) supplies dense direction-dependent fibers, and
Corollary 5.21 supplies regularity of the rescaled carrier. Equation
(5.34) is the resulting projection lower bound. Corollary 5.37 separately
preserves the original incidence data through a product of local
configurations. These are distinct prerequisites, not consequences of
having rich common fibers at a single scale.
[OS, pages 49–52](https://arxiv.org/pdf/2301.10199v4#page=49).

For our current vector argument, the literal common fibers are subsets
`C_(b,b')` of the original scalar C, with mass at least `tau^2 |C|/2`.
If C has normalized kappa-Frostman constant K, these fibers inherit that
law with constant at most `2K/tau^2`. This only controls scalar
translation parameters. It does not control the distribution of the
original directions `b-b'`. It also does not make the planar BSG-selected
A' two-scale regular. A' is an actual retained subset of A, so its
normalized point counts inherit a retention loss; occupied-cell counts
at a larger resolution require a separate argument.

Consequently, two proposed direct applications fail at explicit inputs:

1. Using the rich B-pair set as the direction source requires a profile
   for its weighted secants at the relevant widths. A.2 gives only one
   width, and the example below shows that no width-linear profile
   follows from it, even when every common scalar fiber is full.
2. Using the original dual tube-parameter carrier in OS 5.32 requires
   two-scale regularity. The next example satisfies normalized
   Frostman and the critical-scale cap but violates that regularity by
   a power. A genuine source-preserving scale decomposition is needed.

These statements identify failures of particular substitutions. They
are not counterexamples to A.3 or OS's actual theorem.

## Exact original-grid obstruction to improving the A.2 cap

Let `S >= R >= 2` be integers and take the actual points

    B = {(i/S,j/R): 0 <= i < S, 0 <= j < R},
    delta = 1/(RS).

For any native sup-norm ball of radius `r in [delta,1]`, its cardinality
is at most `(2Sr+1)(2Rr+1)`. Dividing by `|B|=RS` gives

    4r^2 + 2r/R + 2r/S + delta <= 9r.

Thus B has a uniform normalized 1-Frostman law at the original mesh.
Every Euclidean strip of width w has normalized mass at most

    2 sqrt(2) w + 1/R <= 3w + 1/R.

To see this, write the unit strip normal as `(a,b)`. At least one
coordinate has magnitude at least `1/sqrt(2)`. Fixing the other grid
coordinate then leaves an interval containing at most its length times
the corresponding grid density plus one. Summing those literal fibers
gives the bound. In particular, any `w0 <= 1/R` has cap at most `4/R`.

For every smaller `w < 1/R`, the tube around any horizontal original
secant contains exactly S original points, hence fraction `1/R`.
There are exactly `R S(S-1)` nondegenerate horizontal ordered pairs,
which is fraction `(1-1/S)/R` of `B x B`. Thus the directional count can
retain a fixed fraction of the one-scale cap at arbitrarily smaller
query widths.

Take `H = (B x B) minus diagonal` and `F = B x C` for any original
scalar C. H omits only fraction `delta`; every common fiber is exactly
C. Neither graph retention nor common-fiber richness eliminates this
example. Choosing `R=N`, `S=N^k` makes the cap exponent
`1/(k+1)` arbitrarily small. Fixed factors can be absorbed by slightly
lowering that exponent. This matches the relevant qualitative small-cap
regime without identifying the A.2 cap with a finer width.

The adjacent exact-integer script checks all original pair lines for
`(R,S)=(4,16),(8,32)` at three progressively smaller physical widths.
It uses squared Euclidean distances, not floating-point angle tests.

## Normalized Frostman and the critical cap do not imply regularity

Let N be a power of two, `delta=N^(-2)`, and use the N by N original
grid `(i/N,j/N)` inside the unit square. Regard its points as occupied
delta-cells. Its cardinality is `N^2=delta^(-1)`.

For every dyadic R between delta and one, the maximal number of original
points in an R-cell is at most `R N^2`. Below scale `1/N` it is one;
at or above that scale it is `(RN)^2 <= R N^2`. Hence the normalized
dyadic 1-Frostman constant is one; arbitrary metric balls have a fixed
constant by the preceding count.

The critical width is `delta sqrt(|B|)=1/N`. Each such dyadic cell has
one original point, so the critical-scale cap is exactly fraction delta,
even with exponent u=1. Nevertheless, at `R=1` and `r=1/N`, the number
of occupied r-cells is N squared. A two-scale 1-regularity constant must
therefore satisfy

    N^2 <= K N, so K >= N = delta^(-1/2).

It cannot be bounded by `delta^(-epsilon)` for any fixed epsilon below
one half. Taking full common fibers does not change these occupied cells.
The exact dyadic check covers N=4,8,16,32. This is an obstruction to a
direct OS 5.32 call, not to regularizing genuine configurations across
several scales with their correct incidence weights.

## Why the robust quantifier order matters

There need not be one large scalar subset shared by all rich pairs.
For a finite example take `C=F_2^m`, take B to be the nonzero binary
characters, and retain `(b,c)` when `b dot c=0`. Then F has density one
half. Every two distinct B fibers have intersection exactly `|C|/4`,
but the intersection of all fibers is just `{0}`. The script verifies
this for m=3,4,5,6. Labels can be placed on a uniform original scalar
grid; no assertion about a common fixed C follows from pair richness.

Thus a theorem that first fixes Q and then chooses a favorable direction
does not suffice for arbitrary original Q_theta. The direction must be
chosen with a conclusion valid for all dense subsets simultaneously.

## Completed smaller geometric lemma

`OriginalRobustKaufmanImage.original_robust_kaufman_image` now proves,
using the canonical finite Kaufman engine, the following exact finite
statement. Assume the original planar P and original slope Lambda have
the same normalized exponent t in [0,1], with constants KP and KL, at
mesh `delta=2^(-n)`. For `0<q<1`, there is an actual slope subset of mass
at least `(1-q)|Lambda|` such that, for every one of its slopes and every
original `Q subset P` with `|Q| >= 2q|P|`,

    1 <= [48 KP KL (n+3)^2/(q^3(1-q))] delta^t
           * |floor_delta(projection(Q))|.

The proof intersects Q with the engine's slope-dependent retained set.
At least `q|P|` original points survive. Their interval profile bounds
every actual floor fiber, and summing those fibers bounds the literal
projected image of Q. It assumes no projection image lower bound, energy
certificate, two-scale regularity, or radial cap.

This closes the robust-quantifier adapter for direction-dependent dense
queries. It does not supply the missing direction profile when the
directions are B secants, and it does not convert scalar common C fibers
into planar query sets by changing their type.

For carrier exponent sigma and slope exponent s, one may weaken both
profiles to `min(s,sigma,1)`. When `s<=1` and `sigma<=2`, the resulting
exponent exceeds `sigma/2` precisely in the useful regime
`min(s,sigma)>sigma/2`. In particular it gives a positive local gain for
`s>sigma/2`, with enough margin for the displayed density and logarithmic
losses. When `s<=sigma/2`, it gives no positive gain above the square-root
baseline. The native A.1 family allows this latter regime: its shading
exponent may be only gamma while the tube-parameter exponent can approach
`2-gamma`.

The next genuinely unproved local implication is therefore a robust
sparse-direction gain above `sigma/2` in that small-s regime, from the
actual original regular carrier and original direction profile. To use
it under A.3's one-scale hypothesis also requires the incidence-preserving
multiscale factorization. Replacing either implication by a desired
projection or union lower bound would merely assume the missing result.

## Verification

The new module has three public theorem/lemma declarations. Strict source
compilation and a fresh proper imported all-public readback passed with
official Lean 4.33.1, `-j1 -DautoImplicit=false -DwarningAsError=true`.
The three imported axiom closures are only `propext`, `Classical.choice`,
and `Quot.sound`. Exact hashes and logs are recorded in
`OriginalRobustKaufmanImage.manifest.json`. The independent script reports
all rational/integer diagnostics passed. No audit or diagnostic claim is
included in the Lean proof count.
