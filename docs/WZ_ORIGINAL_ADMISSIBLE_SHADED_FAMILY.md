# Weighted physical tube family from the actual original graph

This checkpoint continues the frozen thirty-proof unit-line family.
It uses the same original graph G, original point set P, original angular
classes, original unit normals and offsets, and literal fine line cells.
No repository source is edited by this staging work.

## Fixed-length physical geometry

Write n(z)=(unitX z,unitY z), b(z)=unitOffset z, and d(z)=(-n₂,n₁).
For an original pair z define the actual clipped rectangle

    T(z,w) = {x : |n(z) dot x - b(z)/2| ≤ w,
                  |d(z) dot x| ≤ 1}.

The two directions form an orthonormal basis. A proved representation
identifies this set exactly with

    (b(z)/2)n(z) + t d(z) + s n(z), |t|≤1, |s|≤w.

Thus its longitudinal length is two and its normal half-width is w.
The factor-two spatial normalization is explicit: halfPoint(p)=p/2.
It is injective and preserves the exact number of original shaded points.
For every original representative, its constructed shading maps inside
T(z,3rho). These are actual points, not grid-cell centers. The already
available coarse-shading selection chooses subsets of original labels,
so this physical containment survives that selection.

## Weighted chart and residue selection

Each actual unit normal is assigned one of four charts by a signed
coordinate at least 1/2. Two normals in the same chart have squared norm
of their sum at least one, quantitatively excluding near-antipodal
identification when their lines are close.

Color the original three integer line-cell coordinates modulo a positive
integer M, together with the chart. There are exactly 4M³ colors. Select
a color by the sum of its ORIGINAL graph cell-fiber cardinalities, using
the exact original cell partition. All original pairs in each selected
cell are retained. The selected graph H and representatives S satisfy

    |G| ≤ 4M³ |H|,    H ⊆ G,    S consists of original representatives.

This is a source-pair weight retention statement, not merely a lower
bound on the number of selected tube labels.

The full centerline endpoints of T(z,w) test any proposed containment in
another line's strip of width 2w. Under a common chart this forces actual
normal-coordinate differences at most 8w and original-offset difference
at most 36w. Consequently, if

    36w < (M-1)rho,

distinct selected cells yield a point of T(z,w) outside the other line's
2w-strip. In particular the actual clipped rectangle sets are distinct,
and neither is contained in the other's doubled-width strip. This is a
concrete physical essential-separation property, derived without using
finite P-support containment to infer line proximity.

The residue modulus is explicit:

    M = ceil(36w/rho) + 2.

For w≥3rho it is positive, satisfies the strict separation inequality,
and M≤37w/rho. Hence coarse thickening has an explicit polynomial source
weight loss at most 4(37w/rho)³. The ambient three-coordinate grid is only
used for this finite coloring; no false three-dimensional parameter
population estimate is substituted for the pair count.

## Original shadings and population

Each selected representative retains its original shading constructed
from the FULL rich original graph G. The shading has at least 2k original
points. Its halved image lies in T(z,w) for w≥3rho, with exactly the same
cardinality. Richness is not incorrectly transferred to the color-thinned
graph H: all neighbor and shading counts continue to use the certified G.

The actual fine-grid multiplicity still gives

    4k² |S| ≤ 539 |G|.

The exact selected cell fibers, and the earlier bound of each fiber by
the square of its original 6rho physical tube population, remain available
for the complementary lower population estimate.

## Literal critical-width cap

Full clipped centerlines in one arbitrary external W-strip yield
original determinant and offset moment bounds against that strip.
For W≤1/4, any two selected representatives in the same strip have
normal-coordinate differences at most 8W and original-offset difference
at most 72W. The common chart controls the orientation ambiguity.

Using the already proved local original-pair charge gives, for any actual
contained reference a,

    4k² |S[A]| ≤ 539 |P intersect physicalTube(a,432W+16rho)|²,

where S[A]={z in S : T(z,w) is contained in A}, and A can be ANY set lying
inside any unit-normal W-strip. In particular arbitrary translated and
rotated W×2 rectangles are allowed. Every unit-normal affine line has a
proved representation in the pair-parameter convention; the external
line does not need to be an original source pair. The reference a on the
right IS an original selected pair, as required for the native radial
occupancy input.

The finite construction and all physical comparisons are proved without
an assumed tube multiplicity, assumed weighted retention, or assumed
critical-width population estimate. Later small-scale substitutions must
still put 432W+16rho below the original radial query width and account for
the explicit color loss. The parent composition handles the original and
coarse shading Frostman profiles. The genuine small-s A.3 gain itself
remains unproved and is neither a premise nor a conclusion here.
