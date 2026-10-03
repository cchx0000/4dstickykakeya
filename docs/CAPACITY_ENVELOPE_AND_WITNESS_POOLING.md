# Capacity envelopes and the witness-compatible partition problem

Date: 2026-10-03. This continues the filtration repair while retaining the
original marked family, hypotheses, and final dimension-four target. The
new finite-capacity argument replaces cumulative local duplication by a
strictly weaker hereditary envelope condition. It does not prove that
condition for the actual no-Frostman hairbrush route.

## 1. A constructed reference capacity

Consider a finite rooted tree with positive cap capacities `c_v`. Define
backwards from the leaves

    R_v=max(c_v, sum_(w child of v) R_w).                  (1)

Then `R_v>=c_v` and `sum_w R_w<=R_v`. Moreover this is the least such
majorant: if `S_v>=c_v` and `sum_w S_w<=S_v`, induction from the leaves
gives `R_v<=S_v`.

Equivalently,

    R_v=max {sum_(w in A) c_w : A a descendant antichain of v}.  (2)

An antichain contains no two nodes on the same branch. It either contains
`v` alone or decomposes into child-subtree antichains, proving (2) by
induction. This includes mixed-depth antichains, not only one level.

The Lean construction uses the finite-height recursion

    R_0(v)=c_v,
    R_(n+1)(v)=max(c_v,sum_w R_n(w)).

A rank strictly decreasing along every child edge proves stabilization
once the recursion depth exceeds the subtree height. The resulting
superadditive reference and its least-majorant property are constructed,
not assumed as a certificate.

## 2. Transferring actual density growth

Let the original node masses satisfy

    p_v>=0,   sum_w p_w<=p_v,   q_v=p_v/c_v<=L.

Suppose the constructed envelope obeys

    c_v<=R_v<=B c_v.                                     (3)

Use the same masses with the new reference densities

    qtilde_v=p_v/R_v.

Thus `q_v/B<=qtilde_v<=q_v<=L`. Any original `K`-gain edge, meaning
`q_w>=K q_v`, is a `(K/B)`-gain for the new reference densities:

    qtilde_w>=q_w/B>=K q_v/B>=(K/B) qtilde_v.

For `K>B`, let `a_(K/B)=log(K/B)-1+B/K>0`. The checked subcapacity
filtration theorem gives

    a_(K/B) sum_(original K-gain edges v->w) p_w
      <= p_root [1+log(L R_root/p_root)]
      <= p_root [1+log(L B c_root/p_root)].                (4)

Zero-mass nodes can be omitted. Arbitrary mass deletion is allowed.
No actual measure, retained mass, physical point, or mark is rescaled;
only its reference denominator changes. The comparison (3) is the
remaining geometric premise, explicitly separate from the construction.

This can be much better than summing
`p_v log(max(1,sum_w c_w/c_v))` over all generations. That local sum may
diverge even when one uniformly comparable majorant exists.

## 3. The tight-cap cycling test is now absorbed

Use the tight opposite-pair construction in
`FILTRATION_CAPACITY_REPAIR.md`. A full cube node has 32 pair children,
each of capacity `c_full/8`. A pair node has two quarter-cube children,
each of capacity `c_pair/8`.

For every finite truncation or pruning, induction gives

    R_full<=4 c_full,       R_pair=c_pair.

At a pair node, its child-envelope sum is at most
`2*4*c_pair/8=c_pair`. At a full node, its child-envelope sum is at most
`32*c_full/8=4c_full`. Equality holds at a full node with all pair children.
This verifies the bound for arbitrary mixed-depth antichains.

Thus `B=4` works for arbitrarily many rounds, although the cumulative
positive local duplication entropy grows linearly with the number of
rounds. The repeated fourfold cap-density gains become unit gains for
the envelope reference: both full and pair nodes have modified density
`1/4`, up to the common dimensional convention for ball capacities.
They correctly do not count in (4), which requires `K>B`.

This is a real improvement over the previous local-error ledger. It also
shows why a bound on one-level overlap is not the right stopping criterion.
The geometry needs a hereditary antichain bound.

## 4. Where the original packing information would apply

Suppose, additionally, that witnessed source pieces can be assigned to
distinct cells `C_v` of one nested reference phase partition, with child
cells disjoint and scales `T_v` comparable to their direction-cap scales.
The actual witnessed source need only lie inside `C_v`; it need not fill
the cell. This preserves its fine physical witness.

If the reference source has lower occupied-cell mass

    mu(C_v)>=c_zeta T_v^(3+zeta),

then for `T_v>=r` any descendant antichain obeys

    sum_v T_v^3
      <= c_zeta^(-1) r^(-zeta) sum_v mu(C_v)
      <= c_zeta^(-1) r^(-zeta) mu(C_parent).

An upper direction-density bound on the parent cell consequently gives
an envelope comparison of order `C_zeta r^(-zeta)`.

These lower bounds must be proved for the selected reference cells.
The repository's occupied **net-ball** bounds cannot silently be applied
to arbitrary disjoint dyadic atoms. A fixed countable cell system can be
pruned using the same threshold-budget method, but repeated geometric
witnesses assigned to the same cell remain a separate problem.

A direction-`T` bush with physical error `epsilon<=T` at a bounded time is
contained in a phase ball of radius `O(T)`. Splitting one witness among
the finitely many nearby ordinary phase cells therefore costs only a
dimensional constant. The missing property is injective, nested allocation
for **many** witness branches, not localization of one bush.

## 5. Exact geometry of pooling witnesses

Let all source slopes lie in a cap `|a-a_Q|<=T`, and suppose source piece
`H_i` has a genuine bush witness

    |b(a)+s_i a-y_i|<=epsilon_i.

Put `z_i=y_i-s_i a_Q`. For any proposed pooled center and time `(z_*,s_*)`,
the original line satisfies

    |b(a)+s_* a-(z_*+s_* a_Q)|
      <=epsilon_i+|z_i-z_*|+T|s_i-s_*|.                  (5)

This is a direct triangle inequality with the actual original slope and
intercept. To pool at error `rho`, the relevant label metric is therefore
`|Delta z|+T|Delta s|`, requiring center resolution `rho` and time
resolution `rho/T`. A count of unclustered labels in this metric is not
automatically physical-front entropy: the assigned times may depend on
the source and are not uniform actual times.

Ordinary phase cells of diameter `T` preserve only an `O(T)` bush error.
Retaining a thinner `epsilon` witness naturally uses anisotropic cells

    |Delta a|<=T,     |Delta b+s Delta a|<=epsilon.

Even an optimistic occupied-mass lower bound of order
`epsilon^(3+zeta)` yields a cap/reference distortion
`T^3 epsilon^(-3-zeta)`. This has the power cost `(T/epsilon)^3` on a
power-separated branch. Such a lower bound itself needs either a padded
supported ball or separate pruning of the chosen cells; arbitrary moving
half-open atoms do not inherit it merely by meeting the support.

Consequently, a canonical phase partition does not yet supply a cheap
witness-compatible reference for arbitrarily thin bushes. Replacing the
source by the whole cell can additionally destroy its witness. Keeping
the exact witnessed subset avoids that support error, but does not stop
different subsets from reusing the same reference cell.

## 6. What a whole-family restart does and does not give

The manuscript's `lem:v081-mass-conserving-vector-frostman-stopping` does
apply its failure threshold to the mass of the *whole bush family*.
Literally the threshold uses the current remaining mass `q_l`, which is
at least half the initial family mass before half-mass removal.
It can therefore pool repeated source pieces as a family while retaining
their individual physical labels. This is more flexible than requiring
one common bush witness at the start.

Its concentration output is a new physical bush. It does not by itself
place that output in a small single direction cap: the component secant
centers vary with the original labels. A density increment relative to
the whole parent still needs a quantitative comparison between the new
physical radius and the returned direction-cap radius. Likewise, the
intrinsic two-copy graph has constant normalized mass at its existing
physical error; this does not furnish arbitrarily finer collisions on a
fixed positive source.

The literal vector-stopping lemma assumes source-disjoint bushes. For
fractional overlapping pieces its tagged-space version must be stated
separately, retaining domination of the *sum* of source marginals. Ordinary
disjointification can destroy a quantitative heavy-mass threshold.

For the main dimension target, one may investigate a source-only restart
instead of preserving one old edge law forever. It must still use the
fixed original selector measure and preserve actual witness support.
Forgetting an old edge can remove its fixed residual constraint, but it
does not prove the new cap-radius comparison or pay the transverse branch.
No such cap-improving restart theorem is claimed here.

There is, however, a rigorous weaker restart directly from the actual
dimension deficit. Fix initial source mass `p>0`, a finite positive-length
marked slab `J`, `dim_H K<1+beta` with `beta<3`, and arbitrary `A,r_max>0`.
Every positive remaining source `lambda` contains an actual bush of radius
`0<R<r_max` at a time in `J`, of mass

    lambda(H)>A p R^beta.                                 (6)

The coefficient uses the fixed initial `p`, not the remaining mass. To
prove this, cover the actual compact front by finitely many open balls of
radii `r_i<r_max` with `sum r_i^(1+beta)` arbitrarily small. The original
`lambda x dt|J` has positive mass. Each ball can receive at most `2r_i`
units of time; if all its actual-time spatial bushes had mass at most
`A p r_i^beta`, summing the ball bounds would contradict the total mass.
Thus one ball and an actual time give (6). No old collision scale or graph
retention factor enters.

Choose a bush with at least half the supremal eligible mass in each
remaining source and remove it. If the limiting remainder had positive
mass, (6) there would give a fixed positive eligible mass in every earlier
remainder, contradicting the convergence of the extracted masses to zero.
This constructs source-disjoint bushes exhausting the original source;
every piece has the same coefficient in (6), and a finite truncation
retains arbitrarily close to all its mass. The subsequent
[whole-parent restart](WHOLE_PARENT_HEAVY_BUSH_RESTART.md) now has a strictly
checked original-data endpoint and a direct maximal-disjoint-family proof,
which preserves the quantitative threshold without arbitrary trimming.

This removes the initial `M` loss for a source-only whole-parent restart.
It does not put the resulting physical bushes in small single direction
caps. The earliest relevant manuscript outputs, at
`cor:v081-family-to-merged-bush-frostman` (TeX10103ff) and
`cor:v081-merged-bush-cap-debt` (10140ff), give lower bounds on the returned
angular radius, not the upper comparison needed for forced density growth.
The intrinsic version at `prop:v081-hairbrush-intrinsic-renormalization`
(10904ff) and `cor:v081-alternating-two-probe-lock` (10978ff) leaves the
same two-scale issue. Freezing one positive bush does not permit its fixed
physical error to tend to zero in a later Frostman limit.

## 7. Status

The capacity construction and budget transfer are new finite results.
The comparison between the constructed envelope and the actual geometric
caps is not derived from the full original hypotheses. Nor has excessive
envelope size been shown to produce a Frostman measure supported on the
original front.

The models used to test the ledger have full-dimensional fronts. They do
not refute a genuine dichotomy under a front dimension deficit. The exact
remaining task is to prove that geometric dichotomy, with witness support,
time scales, and the original source retained.

The new `capacity_envelope_budget` module has ten strictly compiled
declarations, including the finite-height construction, its least-majorant
property, and the end-to-end original-growth budget for that construction.
All ten import readbacks use only `propext`, `Classical.choice`, and
`Quot.sound`. The targeted Lake build passed 1,949 jobs; strict source and
readback commands used `-DautoImplicit=false -DwarningAsError=true`.
See `verification/capacity-envelope-checkpoint.json` and the corresponding
build, strict, and axiom logs. The antichain characterization and the
geometric discussion are handwritten and independently checked; their status
is not included in this formal declaration count. The later formalization
of (6) and its exact source-disjoint exhaustion is recorded separately in
`WHOLE_PARENT_HEAVY_BUSH_RESTART.md`.
