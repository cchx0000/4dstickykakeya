# Terminal universal baseline: source audit and reconstruction

Audited source: `cchx0000/4dstickykakeya`, commit
`912dc065d2be0bded29e47a817afd4ab89becdf1` (999-module snapshot).
This is a read-only mathematical audit. No canonical Lean file was edited and no
compilation was run. Proposed mathematical interfaces below are not claims of
existing Lean declarations.

## Result

The snapshot contains no real-incidence `State` declaration and no universal
baseline theorem with the requested conclusion. A caller of that missing theorem
cannot yet be named or checked. The mathematical endpoint

    M sqrt(|P|) <= 1024 (2 K_s)^(1/s) |T|

does follow by a short transverse-pair count from existing geometric and packing
lemmas. The constant 1024 checks exactly: their constants yield
`2 * 100 * 64^2 = 819200 < 1024^2`.

No Kaufman projection theorem is needed for this endpoint. In the notation
`C(s) K_s^(1/s)`, the resulting coefficient is
`C(s) = 1024 * 2^(1/s)`; it is not an absolute coefficient independent of `s`.

## Existing canonical declarations

1. `PlanarStripIntersection.transverse_intersection_ball`, in
   `Theorems/Thm_StickyKakeya4_planar_strip_intersection.lean:73`:

       (a b c d e f w theta : R) (p q : R x R)
       (hw : 0 <= w) (htheta : 0 < theta)
       (ha : |a| <= 1) (hb : |b| <= 1)
       (hc : |c| <= 1) (hd : |d| <= 1)
       (hp  : |residual a b e p| <= w)
       (hq  : |residual a b e q| <= w)
       (hp' : |residual c d f p| <= w)
       (hq' : |residual c d f q| <= w)
       (hdet : theta <= |determinant a b c d|) :
       boxDistance p q <= 4*w/theta

   Here `residual a b e p = a*p.1 + b*p.2 - e`,
   `determinant a b c d = a*d-b*c`, and `boxDistance` is the sup distance.
   For graph tubes `(a0,b0)` and `(a1,b1)`, instantiate the normal coefficients
   with `(-a0,1,-a1,1)` and offsets `(b0,b1)`. The residual is precisely
   `y-a*x-b`, and the absolute determinant is `|a1-a0|`. No coordinate swap.

2. `OriginalSeparatedPointPacking.original_separated_square_packing`, in
   `Theorems/Thm_StickyKakeya4_original_separated_point_packing.lean:31`:

       (Pts : Finset (R x R)) (delta : R)
       (hd : 0 < delta) (hd1 : delta <= 1)
       (hbox : forall p in Pts, |p.1| <= 1 and |p.2| <= 1)
       (hsep : forall p in Pts, forall q in Pts, p != q ->
         delta <= PlanarFrostmanBallConversion.euclideanDistance p q) :
       (Pts.card : R)*delta^2 <= 100

3. `PlanarRoundedSumsetCover.synthesis`, in
   `Theorems/Thm_StickyKakeya4_planar_rounded_sumset_cover.lean:13`, is the additive
   map `z -> (eta*(z.1:R), eta*(z.2:R))`.
   `VectorIntegerBinRealBSG.synthesis_injective` (line 17), `real_grid_card`
   (line 26), and `real_grid_separated` (line 44), in
   `Theorems/Thm_StickyKakeya4_vector_integer_bin_real_bsg.lean`, prove injectivity,
   exact image cardinality, and separation at `eta` when `0 < eta`.
   The last theorem uses the product sup norm, which is at most the explicit
   Euclidean distance used by the packing theorem. That elementary comparison
   still needs to be supplied when joining these existing lemmas.

4. `OriginalPlanarTubePairCount.InCellTube h z x`, in
   `Theorems/Thm_StickyKakeya4_original_planar_tube_pair_count.lean:13`, is

       |x.2 - (h*(z.1:R)*x.1 + h*(z.2:R))| <= 16*h.

   `original_planar_two_point_cell_count` (line 56) assumes `0<h<=1`, point
   sup distance at most 6, grid slopes bounded by 2, and that every tube cell
   in `S` contains both points. Its conclusion is
   `|S| * max(boxDistance x y,h) <= 30000`.
   This is a bound on tubes through two points. It is not itself the desired
   bound on points shared by two transverse tubes; declaration 1 supplies that
   geometry instead.

5. `OriginalThreeDimensionalCapCount.integer_interval_mass`, in
   `Theorems/Thm_StickyKakeya4_original_three_dimensional_cap_count.lean:13`, says
   that `0<rho`, `0<=R`, and `|rho*k-a|<=R` for `k` in a finite integer set `S`
   imply `|S|*rho <= 2*R+2*rho`. This is an alternative for direct integer-grid
   rectangle packing. It can improve the numerical constants but is unnecessary.

## Minimal mathematical endpoint and proof

Original real input consists of finite sets `P` of points and `T` of actual tube
parameters `(a,b)`, and an edge set `E subset P x T`. Assume:

- `0 < delta <= 1`, `s > 0`, and `K_s >= 1`
- Every point is in `[0,1]^2` and distinct points are Euclidean delta-separated
- Every tube slope satisfies `|a| <= 1`
- Every edge satisfies `|y-a*x-b| <= 16*delta`
- Each actual row `R_p = {t in T : (p,t) in E}` has exactly `M` members
- For each `p in P`, each real center `c`, and each `delta <= r <= 1`,
  `|{t in R_p : |a(t)-c| <= r}| <= K_s*r^s*M`

The Frostman count is a count of tubes in each row, including distinct intercepts
with the same slope. Replacing it by the cardinality of the slope image loses
multiplicity and is insufficient without an additional argument.

Set `theta = (2*K_s)^(-1/s)`, so `0<theta<=1` and `K_s*theta^s=1/2`.
Empty `P` or `M=0` is immediate.

If `delta > theta`, global square packing gives `sqrt(|P|)<=10/delta`, while
`M<=|T|` follows from one nonempty row. Therefore the target follows with 10
in place of 1024.

If `delta<=theta`, query each row at radius `theta` and at the slope of each of
its tubes. At most `M/2` row tubes are within that slope radius, hence at least
`M^2/2` ordered pairs have slope difference strictly greater than `theta`.
Let `W` be the actual triples `(p,t,u)` where both edges lie in `E` and
`|a(t)-a(u)|>theta`. Then `|P|*M^2/2 <= |W|`.

For a fixed such ordered tube pair with at least one common point `p0`,
declaration 1 puts all its common points in a sup ball about `p0` of radius
`R=64*delta/theta`. The map `p -> (p-p0)/R` is injective, has image in
`[-1,1]^2`, and preserves separation with new separation `delta/R=theta/64`.
Declaration 2 gives common-point count at most `409600/theta^2`.
The empty common-point case is automatic. Summing over at most `|T|^2` ordered
pairs gives `|W| <= 409600*theta^(-2)*|T|^2`.

Thus `M^2*|P| <= 819200*theta^(-2)*|T|^2`, and nonnegative square roots give
the stated endpoint with 1024. This proves the bound from the displayed input;
it does not assume a baseline or a conclusion-shaped certificate.

## Literal terminal realization of an integer graph

There is no matching canonical terminal `G`/`State` package in this snapshot.
The following specifies the exact transport needed when its source is restored.
Let `k : Nat`, `1<=k`, `epsilon=1/(k:R)`, and
`G : Finset ((Z x Z) x (Z x Z))`. Put

    Pz = G.image Prod.fst
    Tz = G.image Prod.snd
    rowz(p) = Tz.filter (fun t => (p,t) in G)
    i(z) = synthesis epsilon z
    P = Pz.image i
    T = Tz.image i
    E = G.image (fun e => (i(e.1), i(e.2)))

The two coordinates of `i(t)` are `(slope,intercept)`. Injectivity of `i`
implies all of the following, with no loss:

- `|P|=|Pz|`, `|T|=|Tz|`, and `|E|=|G|`
- `row_E(i(p)) = (rowz(p)).image i`; consequently exact row mass is preserved
- Original point separation is at least `epsilon` in the sup norm, and hence
  in Euclidean distance
- Integer bounds `0<=p.1,p.2<=k` imply the real point box `[0,1]^2`
- Integer bound `|t.1|<=k` implies the real slope bound `|a|<=1`
- The literal integer residual condition
  `|k*p.2-t.1*p.1-k*t.2|<=16*k` implies width `16*epsilon`, because

      y-a*x-b = (k*p.2-t.1*p.1-k*t.2)/k^2.

The graph edges must remain exactly the image of `G`. Replacing them by every
geometrically incident point/tube pair can enlarge rows, change `M`, and destroy
the provided local profile. Geometric incidence is only an upper-bound tool
for the common-point count.

For every row, real center `c`, and radius `r>=0`, the exact local count identity is

    |{t' in row_E(i(p)) : |t'.1-c|<=r}|
      = |{t in rowz(p) : |(t.1:R)-(k:R)*c|<=(k:R)*r}|.

Consequently the original grid's local interval count, at radius `k*r` and center
`k*c`, gives the required row Frostman profile directly. If the restored source
only provides integer centers or integer radii, a rounding lemma and its actual
constant loss must be proved; it must not be silently assumed to be exact.
No row Frostman upper bound follows from injectivity or equal row masses alone.

## Why canonical Kaufman is not the caller

`ProjectionAnnulusEnergy.projection` and `ProjectionHeavyCells.projection` use
`p.1-lam*p.2`, rather than `y-a*x`. Theorems
`FiniteKaufmanProjection.finite_kaufman_projection` and
`OriginalRobustKaufmanImage.original_robust_kaufman_image` also require a global
point Frostman profile, a global distinct-slope Frostman profile at dyadic mesh
`(1/2)^n`, and produce slope-dependent retained subsets with a logarithmic-scale
factor `48*KP*KL*(n+3)^2/(q^3*(1-q))`. They do not directly consume the actual
row-wise tube profile above or conclude the universal baseline.

## Remaining formal work, if the later package is unavailable

1. Define or restore the actual incidence state and graph realization, preserving
   original edges, and prove the exact image/row/profile identities above
2. Formalize the local translate/scale application of square packing, including
   its Euclidean distance scaling and injectivity
3. Double-count the literal ordered transverse triples and perform the real
   power/square-root algebra, including `epsilon>theta` and empty cases
4. Only then instantiate the proved baseline with the restored graph's original
   box, incidence, exact row, and local interval-count hypotheses

The elementary proof validates the intended endpoint and its constant, but it
does not establish that the missing later Lean file had been kernel-checked.
