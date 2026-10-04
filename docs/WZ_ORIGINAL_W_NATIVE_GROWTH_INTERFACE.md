# Original W witnesses to native transverse growth: verified interface

2026-10-03. This is a conditional finite-geometric endpoint for the two native dimensions `a=1,2` in d=4. It does **not** construct the global Definition 17.2/17.4 configuration, prove the final sigma-ancestor concentration count, or prove the original compact packing theorem.

## Verified endpoint

`NativeOriginalWEndToEnd.scalar_original_w_growth` and `planar_original_w_growth` start with original point–tube incidences, actual graph coordinates, the original fine direction sets and their pointwise Frostman laws, and the original collision mass lower bound. They construct the real rich core and conclude growth of the actual depth-one/depth-two neighborhoods.

No successor, point-representative, displacement, coarse-union Frostman, selected-W Frostman, determinant, path-count, or endpoint-fiber certificate is an input to these two theorems. Those objects and bounds are constructed from the stated data and previously verified finite lemmas.

Strict compilation succeeded. `/tmp/NativeOriginalWEndToEndReadback.log` checks all 53 declarations in the seven composition modules, using only `propext`, `Classical.choice`, and `Quot.sound`. The three earlier original-W/fine-slab modules have a separate 34-declaration imported readback at `/tmp/OriginalWCoarseEscapeMenusReadback.log`.

## Literal native objects

* `I : Finset (P × T)` is the original incidence set. Point and tube labels are retained.
* `height : P → ℝ` gives the original actual height. `Z : Finset ℝ` contains those original heights. It is not a new coarse label set.
* `theta : T → Fin 3 → ℝ` is the full actual three-coordinate tube slope.
* The terminal collision label is the literal floor vector `j ↦ floor(theta(T,j)/q)`.
* A branch is the existing `TwoTubePathCollisionCount.Path P T` record, containing its three original points and two original tubes.
* A W witness is an ordered pair of original branches, collided by `(common start point, intermediate height, terminal height, terminal full-slope cell)`.
* A terminal vertex is `(terminal height, original terminal tube)`.
* Initial angular labels are `floor(theta(T,0)/q)` in a=1 and the pair of the first two such labels in a=2. Their displayed coarse coordinates are exactly `q` times those integer labels.
* A menu is `((original start height, original intermediate height), (left initial angular label, right initial angular label))`.
* The angular alphabet is the actual image of all original incident tube labels under that initial angular-label map.

To embed these collisions in the source's literal Euclidean terminal-gap condition at radius rho, take the intended fixed small dimensional grid factor, for example `q=rho/4`. Equality of the full terminal grid labels gives coordinate gaps at most q, hence Euclidean gap at most `sqrt(3) q < rho`. The proved tangential growth itself only requires `0<q<=rho` and uses maximum norms. No arbitrary untracked refinement of q is free: the actual alphabet size and fiber caps still occur in the parameter budgets.

## Actual incidence counts

The count interface has primitive original-reference bounds:

* `C`: maximum original points in one original tube at one fixed original height
* `D`: actual incident-tube degree cap at an original point
* `U`: cap for incident tubes in one initial projected q-cell and in one terminal full-slope q-cell
* `N=|Z|`

`OriginalWWitnessCounts` enumerates branches through actual incidence fibers. A backward first branch has at most `C^3 K` choices. A forward second branch from that branch's same original start point has at most `C^2 K U` choices. It derives:

    B = C^5 D^2 U N^2

as the ambient witness degree cap, and

    C^5 D K U N^2

for a tested second initial tube population K. Fixing both original times and both projected angular labels gives the actual menu fiber bound

    L_W = C^5 U^3.

These are proved upper bounds on original path-pair records, rather than assumed W-fiber certificates.

## Fine-label normalization and the approximation width

Two actual maps are used at each original point:

1. Every incident original tube selects an original fine direction label; a fixed fine label has at most mu original tube labels above it.
2. Every original fine direction has a realizing original incident tube; a fixed realizing tube has at most nu fine labels above it.

The proof derives the correct comparison

    |Phi_p| <= nu |T(p)| <= nu D.

It never reverses `|T(p)| <= mu |Phi_p|`, and it does not assume `mu |Phi_p| <= D` for the unchanged degree cap D. The final bad-witness estimate retains both multiplicities:

    bad W <= mu nu F_* R^gamma B,

where `F_*=F` in a=1 and `F_*=2^gamma F` in a=2.

The original fine direction is within `DirErr*delta` of the actual projected slope. Literal floor quantization is within q of that actual slope in maximum norm. Thus the proof uses exactly

    R >= h + 2(DirErr*delta + q),
    delta <= R <= 1,
    mu nu F_* R^gamma <= alpha/8.

For every proper subspace, a unit continuous annihilating functional is constructed. A coarse difference at distance less than h from that subspace is charged to an affine slab on the ORIGINAL fine direction set at the SAME original start point. The pointwise upper bound is applied to the full reference incidence choices, before restriction to the W core.

`NativePlanarSlabNormConversion.slab_law_conversion` derives the max-norm unit-functional law directly from the original Euclidean unit-normal slab law, preserving Phi exactly and charging `2^gamma`. It uses the original law at width `2r` when `r<=1/2`, and the trivial whole-Phi bound otherwise. Its assumptions `F>=1` and `gamma>=0` are explicit. Scalar unit-functional conversion has no extra loss.

## Constructed core and menus

The collision lower bound supplied by the earlier actual-incidence count is

    |W| >= alpha B |V|.

`RichWitnessRealCore` constructs a nonempty core S, retains at least half the original W witnesses, and gives outgoing original-witness degree at least `alpha B/4` at every retained vertex. The original branch swap is the symmetry used by the core construction.

Subtracting the full-reference bad-W upper bound and dividing by the derived original menu-fiber bound yields, for every core vertex and every proper subspace,

    (alpha/8) D^2 N^2 <= U^2 * #escaping menus.

If m is the actual angular alphabet size, the explicit numerical condition

    8 beta U^2 m^2 <= alpha D^2

gives the uniform menu population `beta N^2 m^2` required by the growth lemma. This is the exact point at which the source's actual D/U and common angular-alphabet estimates pay their K factors.

One original witness is chosen for each occupied menu independently of the subspace. The resulting successor stays in the core and preserves the actual terminal height. Off-menu values fix the state. Representatives are chosen once per `(height,tube)` vertex and are genuine original incident points at that exact original height.

## Derived physical displacement

The graph assumption is only the original per-incidence residual

    ||position(p) - base(T) - height(p) slope(T)|| <= Err delta.

Two incidences on the same tube give a chord error at most `2 Err delta`. A two-leg branch has error at most `4 Err delta`. Subtracting the two genuine branches yields error at most `8 Err delta`.

The terminal full-slope grid equality gives projected terminal slope gap at most q. Both original time gaps are at most rho because the ORIGINAL height set lies in the chosen rho interval. Initial floor quantization contributes at most `2 rho^2`, and the terminal term contributes at most `rho^2`.

Changing the two actual terminal points to the fixed original incident representatives costs at most another `4 Err delta`, proved from their common original tube and exact common original height. Hence

    ||x(next)-x(current) - (zmid-zstart)(phi_right-phi_left)||
      <= 3 rho^2 + 12 Err delta
      <= (3+12 Err) rho^2,

using the explicit input `delta<=rho^2`. Equal or reversed time levels and loops remain allowed. An error parameter growing with the mesh remains visible in the conclusion.

## Original time cap and final neighborhood counts

`OriginalHeightIntervalCap` starts with literal mesh membership

    z in Z ==> exists k in Z, z=delta*k.

It proves injectivity of the original floor index on these unchanged heights and counts its integer interval image. At `r=rho^2>=delta`, every interval contains at most

    H = 3 rho^2/delta

original heights. No time-AD law is transported through an arbitrary cut. This mesh condition is a literal native caller hypothesis; the module does not assert that arbitrary real delta-separated sets are already exactly on that mesh.

Put `E0=3+12 Err`, `C1=4+4E0`, and `C2=16(1+4E0)+2`. The planar value uses V=4, derived from the actual original slope bound `|theta_j|<=1` and `q<=rho<=1`.

For every root in the constructed core, the endpoint theorems give

    beta h N <= C1 H Q1,
    beta^2 h^4 N^2 <= C2^2 H^2 Q2,

where Q1 and Q2 count the actual rho-squared grid cells reached by the constructed original dynamics in at most one and two steps, respectively. Each step has an actual original W witness and preserves the terminal height.

The original retained-height density `delta N >= lambda rho` gives `N/H >= lambda/(3rho)`. Thus the usual source growth scales are

    Q1 >= beta h lambda / (3 C1 rho),
    Q2 >= beta^2 h^4 lambda^2 / (9 C2^2 rho^2).

The density must come from the actual retained-height preparation. It is not a consequence of the upper mesh cap alone.

## What the native caller still supplies

The caller supplies the prepared original incidence configuration, literal graph residuals and fine direction realization data, primitive point/tube/angular caps from its separation and AD properties, the actual original-height density, and the collision lower bound from the earlier finite walk/collision theorem. It must keep all scale-rounding factors and the fixed small angular grid factor explicit.

The full native configuration constructor remains separate. To finish Lemma 19.2 one must combine these actual depth-bounded W paths with the verified adapted-box comparison, extract sigma-separated terminal points, count original sigma ancestors using full fine direction populations, and use the full-reference carrier ancestor lower bounds and global tube cardinality bound. None of those later concentration conclusions is an input here.
