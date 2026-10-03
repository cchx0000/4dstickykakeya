# Heavy families at one fixed actual time

Date: 2026-10-03. The two modules described here are strictly Lean-checked.
They strengthen the whole-parent restart by fixing its witness time before
all later coefficient, scale, and retained-mass requests. They do not
complete the physical-to-angular cap step or the original main theorem.

## 1. Almost every slice has arbitrarily cheap finite covers

Let `K` be a compact subset of the actual four-dimensional front, and let
`beta>=0` satisfy

    dim_H K<1+beta.

For Lebesgue-almost every height `t`, the spatial slice

    K_t={x in R^3 : (x,t) in K}

has the following property: for every `rho,epsilon>0`, finitely many open
spatial balls cover K_t, all radii lie strictly between zero and rho, and
their beta-power radius sum is less than epsilon.

The good time is chosen before rho and epsilon. In particular a single good
time can be selected in any prescribed positive-length closed interval.
The formal development retains the almost-everywhere statement as well as
this existence corollary.

### Proof with the actual time coordinate

Choose finite open spacetime-ball covers at scales tending to zero with
summable total `(1+beta)`-power radius costs. For the nth cover define

    cost_n(t)=sum_i r_ni^beta 1_{|t-t_ni|<r_ni}.

Each vertical interval has length `2r_ni`, so

    integral cost_n(t) dt=2 sum_i r_ni^(1+beta).

Tonelli implies `sum_n cost_n(t)<infinity` for almost every t. Thus those
active slice costs tend to zero. A spatial point in K_t lies strictly
inside some spacetime cover ball, so that ball is active and its spatial
projection contains the point. Active projected balls therefore cover
the slice, with both maximal radius and total beta-cost tending to zero.
Open-ball boundaries do not leave uncovered slice points.

This argument uses the original continuum of heights. It is not an
assertion based on finitely many selected times or a new normalized label law.

## 2. The same time works for every positive source remainder

Fix a finite source sigma, a measurable intercept b, and a common marked
slab `J=[u,v]`. Assume the original trajectories `(b(a)+t a,t)` lie in K
for sigma-almost every a and every t in J.

Choose one of the good heights `t` from Section 1. For any positive
restriction `lambda=sigma|S`, any finite coefficient C, and any `rho>0`,
the slice-cover property forces an actual spatial ball of radius `R<rho`
whose preimage has lambda-mass greater than `C R^beta`. Otherwise a cover
with sufficiently small beta-cost would have total preimage mass strictly
less than `lambda(univ)`.

Intersect that bush with S. Its own original sigma mass still satisfies
the strict inequality, and all its lines carry the same actual time t.
The coefficient C is unchanged when passing to S.

The non-hereditary maximal-disjoint-family theorem then produces a
countable source-disjoint exhaustion at this fixed time. A finite
subfamily retains any target strictly below `sigma(univ)`, keeping every
selected set intact and retaining its quantitative lower bound.

## 3. Original-data endpoint and quantifier order

From `IsStickyDatum ambient` and
`dimH(unitFront ambient)<4`, the endpoint constructs

    beta, sigma, b, u, v, t

with `0<beta<3`, positive finite `sigma<=volume`, `v-u=3/8`, and
`t in [u,v]`. These are fixed before every finite A, every `rho>0`, and
every `target<sigma(univ)`. It then supplies a finite source-disjoint
family H_i with

    sigma(union H_i)>target,
    H_i subset {a : |b(a)+t a-y_i|<=R_i},
    0<R_i<rho,
    sigma(H_i)>A sigma(univ) R_i^beta.

Every bush has the SAME t. Its center, radius, and source piece may vary.
The original source and original marked-front support are retained; no
Frostman, slice, heavy-family, or routing certificate is a hypothesis of
this original-data endpoint.

There is also a generic theorem asserting these finite-family conclusions
for almost every t in the actual slab. This stronger time statement matters:
one exceptional low-dimensional projection by itself is compatible with a
full-dimensional front.

## 4. The remaining geometric obligation

This removes moving witness times from the source-only restart. It does
not bound the number of spatial centers, their repeated direction-cap
labels, or the hereditary capacity envelope from the filtration argument.
The radii R_i are physical radii, not angular cap radii.

The source-disjoint sets keep their fine physical witnesses. Replacing
them by entire phase cells can enlarge their physical error; retaining
arbitrary witnessed subsets can cause repeated use of a reference cell.
The common time makes this compatibility problem more concrete, but does
not solve it. No change is made to the main theorem or its assumptions.

The separate handwritten
`RELATIVE_PROJECTION_FILTRATION_AUDIT.md` examines a possible relative
projection/entropy continuation. Its polynomial transversality estimate
only applies to planes chosen before the queried time (or with an explicit
selection cost), and is not an assumed inverse theorem.

## 5. Executed checks

`common_time_slice_cover` contributes six checked declarations;
`fixed_time_heavy_families` contributes seven. All thirteen passed source
compilation and import axiom readback with
`-DautoImplicit=false -DwarningAsError=true`. The only axioms reported are
`propext`, `Classical.choice`, and `Quot.sound`.

The targeted Lake build passed 8,759 jobs. Exact hashes and verification
scope are recorded in `verification/fixed-time-heavy-checkpoint.json` and
the corresponding strict/build/axiom logs. The prior 189 source hashes are
unchanged. This checkpoint does not claim a fresh full default build of all
191 project modules, nor removal of the main theorem's existing WZ axiom.
