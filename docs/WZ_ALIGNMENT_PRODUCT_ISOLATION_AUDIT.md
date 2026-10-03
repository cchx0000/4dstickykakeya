# Independent audit of the remaining alignment/product and isolation steps

2026-10-03. Companion to
[the disjoint-fiber preparation](WZ_ALIGNMENT_DISJOINT_FIBER_REPAIR.md). This is a handwritten mathematical
audit, not a Lean proof. It checks the completion proposed by the main
extremal-geometry researcher.

Write a=r_i, b=r_{i+1}, N=b/a, and Delta comparable to 1/N. Let H collect
all the small-power losses from the repaired preparation. The first final
set B is t-AD; it has one assigned source-fiber direction at every point;
the source fibers are s-AD at the working radii; and one common E_0 supplies
the tube profile. Throughout 0<=s<=min(t,1).

## 1. The angular menu uses actual retained directions

Include in the FIRST same-set uniform call both spatial r_i-cell partitions
and (spatial r_i-cell, angular Delta-cell) partitions, for every candidate i.
Then the numbers of occupied angular cells in any two occupied r_i-cells
are comparable. If D_i is their maximum, nested spatial cells give
D_i<=D_{i+1}, and D_m/D_0<=C Delta^{-(d-1)}. Some common i therefore has

  D_{i+1}/D_i <= C Delta^{-(d-1)/m}.

In EVERY b-parent Q, angular averaging selects a Delta-cell present in at
least f times its occupied a-children, where
f>=H^{-C} N^{-(d-1)/m}. Keep all B points in those children. Their total
original-point population is at least f H^{-C}(b/delta)^t.

Choose alpha to be an ACTUAL witness slope in the selected angular cell.
For every selected child q choose its actual witness p_q in B intersect q.
Its assigned source direction theta_j satisfies |theta_j-alpha|<=C Delta.

The source direction is exactly constant on each B intersect F_j. Hence
all child cells met by that fiber inside Q have the same chosen angular
label and are selected too. No direction label is reconstructed after a
point-only refinement.

## 2. Parent boundary and fractional-s spine counts

The cleanest boundary convention is to use original-grid dyadic parents.
For a retained p in F_j intersect Q and any smaller dyadic working radius r,
its r-cell is contained in Q. The first-call partition (fiber j,r-cell)
therefore gives the SAME-SET lower bound within F_j intersect Q. In
particular the b-level partition gives a rich spine entirely inside Q.

Alternatively, taking the spine (B intersect F_j) intersect B(p_q,b) in a
fixed dilation 3Q suffices for the following counting argument. One uses
only its total lower richness at p_q and the inherited local upper bounds.
One does NOT assert that truncating an AD set by that ball preserves AD at
all points of the truncated set.

For every u in [a,b], the spine has at least

  H^{-C}(b/u)^s

distinct u-cells: divide its total rho-cover lower count by its local
u-ball rho-cover upper count. This remains valid for fractional s, including
s=0. Since |theta_j-alpha| b=O(a) and rho<=a, the entire spine stays within
O(a) of the alpha-parallel a-column of its witness.

Any occupied output normal a-column comes from a point of a selected child
and is O(a) from that child's witness. At a coarser normal radius u>=a,
the corresponding spine consequently lies in a fixed dilation of that
u-column. Such enlarged parallel u-columns have bounded overlap. Since
ambient t-AD gives O(H(b/u)^t) reference spatial u-cells in 3Q, summation
gives the GLOBAL reference quotient cover bound

  #D_u(Y_ref) <= H^C (b/u)^{t-s}.

The spines are reference witnesses. They need not survive the SECOND
uniform refinement. This is a counting bound on its fixed original menus.

## 3. Use original point mass as weights during the second refinement

Shear coordinates by (x,t)->(x-alpha t,t), and quantize on a fine mesh a/c,
with c a sufficiently large dimensional constant. Each bin has a fixed
integer weight equal to the number of original selected B points in it.
Every bin weight is at most

  U = C H (a/delta)^t.

Choose one coordinate residue class of this grid, of fixed period large
enough that its shear-image grid centers are at least a separated. A
heaviest residue class retains a fixed fraction of original point mass;
it can be chosen separately in each parent. Every retained original point
is still within a/10 of its assigned center. Keep whole original point
fibers of retained bins, not one original point per bin.

For P parents, reference total weight is at least

  H^{-C} f P U N^t.

All reference class-count estimates below have a factor P, which cancels
this factor. Apply ONE weighted same-set refinement with these partitions:

* (parent, exact normal column, longitudinal r-cell), r in [a,b];
* (parent, transverse r-cell), r in [a,b].

Use fixed-depth working radii and interpolate. Parent and column partitions
may be included explicitly as well. All counts below concern the SAME
final set of bins with their unchanged original point weights.

## 4. Fiber lower and upper AD

The fixed tube profile bounds the number of occupied longitudinal r-cells
in a reference column by H^C(b/r)^s. The number of reference columns per
parent is at most H^C N^{t-s}. Thus the total number of first-kind partition
classes is at most

  P H^C N^{t-s}(b/r)^s.

The same-set partition lower bound gives final weight at least

  f H^{-C} U (r/a)^s

in every occupied class. Divide by the per-bin upper U to obtain the
required lower number of distinct longitudinal bins. At r=b this also
gives final weight at least f H^{-C} U N^s in every final column.

The inherited a by r source tube profile gives at most H^C(r/a)^s bins
locally in a column, and at most H^C U N^s total weight in a column. Hence
each final one-dimensional fiber is s-AD, with loss f^{-1}H^C.

## 5. Quotient lower and upper AD

For the second-kind partitions, Section 2 gives at most

  P H^C(b/r)^{t-s}

reference classes. Their final class weights are therefore at least

  f H^{-C} U N^s(r/a)^{t-s}.

Divide by the final per-column upper weight H^C U N^s to get quotient
LOWER AD counts.

For the UPPER count in a transverse r-ball, the inherited r by b source
tube profile gives ONE common longitudinal cover with at most
H^C(b/r)^s spatial r-cells. Each has original point mass at most
C H(r/delta)^t. Thus the total final weight in the corresponding thick
column is at most

  H^C U (b/r)^s(r/a)^t
    = H^C U N^s(r/a)^{t-s}.

Divide by the final per-column LOWER weight f H^{-C} U N^s. This gives
quotient upper AD counts f^{-1}H^C(r/a)^{t-s}.

The common longitudinal cover is crucial. Bounding each column separately
and adding would not establish the t-s exponent.

## 6. Exact near-alignment and local-ball isolation

The selected quantized centers have the exact form

  {(x,y+alpha x): y in Y, x in X_y},

are a-separated, and are at Hausdorff distance at most a/10 from the
retained original points. Each selected bin is nonempty, giving the
converse Hausdorff inclusion. Sections 4--5 establish the aligned fiber
and quotient AD requirements. The tube Katz--Tao bound transfers from E_0
by the fixed quantization error and constant tube enlargements.

Choose C_b>=10d. RUN THE INITIAL COVER-PROFILE CONSTRUCTION with a fixed
dyadic top tube length tau_max<=1/C_b instead of 1. The extremal ratio
argument and epoch bounds are unchanged except for dimensional constants.

Color the original b-parent cubes by their index vector modulo an integer
L>=10C_b and keep a heaviest color, after all within-parent refinements.
This loses a fixed factor and removes only whole already-constructed
patches. Different retained parent cubes have gaps larger than C_b b;
each patch has diameter at most sqrt(d)b.

Set rho_out=a and tau_out=C_b b. Then delta<=rho_out<=tau_out<=1. For EVERY
retained original point p, B(p,tau_out) contains its entire patch and no
other patch. Thus the literal set in the theorem,

  A_out intersect B(p,tau_out),

is exactly the already-constructed complete patch, not an arbitrary
truncation of a product set. Translate by p and dilate by tau_out^{-1},
with the finite slope-chart coordinate map if needed. The resulting mesh
is a/(C_b b), and all sets lie well inside the unit coordinate box.

The source tube upper profile extends to the larger output range as
follows. For u<=v<=b it is the inherited estimate. For u<=b<v<=C_b b,
the patch intersects the tube inside O_d(1) pieces of length b, giving
O_d(H)(b/u)^s<=O_d(H)(v/u)^s. For b<=u<=v<=C_b b, the patch has only
O_d(1) u-cells. Quantization changes only constants.

## 7. Final parameter budget

Choose m>=C_d/zeta, then epsilon<<zeta/m. Let
chi_profile=epsilon^{ceil(2/epsilon)}/2, kappa=epsilon chi_profile, and
eta<<epsilon chi_profile. Make all fixed-depth interpolation errors
O(epsilon). The preparation and both uniform refinements contribute
R^{O_d(epsilon)} losses; angular menu selection contributes
N^{-(d-1)/m}, where N comparable R^{1/m}. Constants and logarithmic losses
are absorbed by sufficiently small delta.

Consequently final retention is at least (rho_out/tau_out)^zeta and all
AD/Katz--Tao constants are at most (rho_out/tau_out)^{-zeta}, after choosing
the hierarchy with enough margin. The final positive separation exponent
can be chi_safe=chi_profile/(2m), allowing all rounding constants.

This completes the handwritten repair route for the full Lemma 5.3
conclusion, with a smaller positive chi. It uses no additional geometric
certificate and makes no assertion that a Lean implementation is already
complete.
