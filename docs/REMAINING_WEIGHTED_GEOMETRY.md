# Remaining weighted geometry after genuine contact-cycle rigidity

Date: 2026-10-02. This note records source-exact quantitative obligations.
It does not disprove the final theorem. The smooth test selectors below have
four-dimensional fronts, so they test individual proposed implications before
the no-Frostman hypothesis is used.

## 1. What the packing estimate actually supplies

Original `lem:v056-weighted-q-slice-retention` (TeX lines 5205ff) assumes

    N_r(G) <= C_zeta r^(-3-zeta),   Gamma endpoint marginals <= L mu.

For an occurrence submeasure of mass H, the subsequent
`lem:v057-collision-preserving-multiscale-pruning` (lines 5270ff) retains at
least H/2 and proves a vertical-branch bound

    v_r(A_r(a)) <= C (L/H) log(2/W) r^(-zeta),   W <= r <= 1.

The factor L/H is explicit. With H comparable to r0^(2-eta), it is a power
of the root scale, not a subpower factor at that scale. If r0 and H are
frozen and a genuinely new scale rho tends to zero, the same constant can
be absorbed into a rho-subpower bound. That fact does not improve the
physical residual of an inherited old edge from r0 to rho.

These statements bound covering multiplicity after occurrence-sensitive
pruning. They do not assert a quantitative upper bound on physical bush
mass, nor a root-weighted charge for all discarded rank-loss occurrences.

## 2. Packing alone cannot supply a polynomial bush modulus

On a fixed bounded direction ball, set

    b(a) = f(|a|) e_2,   f(t)=exp(-1/t^2) for t>0,   f(0)=0.

This is a smooth Lipschitz selector. Its graph satisfies the stronger
uniform covering estimate N_r(G) <= C r^(-3). At time zero and center zero,
for sufficiently small epsilon,

    sigma{a: |b(a)| <= epsilon}
      is comparable to (log(1/epsilon))^(-3/2).

Indeed the defining inequality is precisely
|a| <= (log(1/epsilon))^(-1/2). The bush mass tends to zero more slowly than
every positive power of epsilon. Scaling any fixed smooth selector by a
small constant also gives uniformly Lipschitz graphs whose entire direction
domain is a bush at a correspondingly small scale.

These examples have full-dimensional fronts: for a suitable nonzero time s,
Db+sI is invertible on an open patch, and the front map has an open image
there. Thus they do not survive the no-Frostman branch. They establish that
any useful rate must genuinely use that branch, not merely its packing
hypothesis. The existing qualitative no-Frostman result gives a uniform
small-bush modulus tending to zero; no polynomial rate has been derived.

## 3. Vector failure does not imply same-tolerance mass growth

In `cor:v081-bush-family-angular-concentration` (lines 9775ff), failure of
the full vector-family bound produces cap subsets

    A_j = H_j intersect B(a_j,R),
    S = sum_j sigma(A_j) > A q R^(3-delta).

The physical merger of `prop:v081-hairbrush-merges-to-one-bush` (9999ff)
merges these selected subsets, not the complete old bushes H_j. There is
no comparison S > max_j sigma(H_j), or even S > max_j sigma(A_j).
Consequently maximal old-bush mass is not a proved increasing potential.

A concrete smooth test makes the failure strict. Let h=1/L and tile the
unit direction cube into N=L^3 cubes with centers a_j. Choose a smooth
function psi equal to one on B(0,1/8), supported in B(0,1/4), and put

    b_h(a) = -a + sum_j psi((a-a_j)/h) (a-a_j),
    H_j = B(a_j,h/8).

The bump supports are disjoint and the derivatives of b_h are uniformly
bounded, so N_r(graph b_h) <= C r^(-3) uniformly in h. On H_j,
b_h=-a_j: each component is an exact time-zero bush. With ordinary
Lebesgue direction measure and v_3=volume(B(0,1)),

    p = sigma(H_j) = v_3 h^3/512,   q = Np = v_3/512.

At the common outer point (y,s)=(0,1), the vector cap centers are a_j.
Set R=h^(5/2) and delta=1. For small h the cap pieces are
A_j=B(a_j,R), with total merged mass S=v_3 h^(9/2). Hence

    S / (q R^2) = 512 h^(-1/2) -> infinity,
    S / p       = 512 h^(3/2)  -> zero.

Taking the excess constant A=256 h^(-1/2) gives a strict vector failure.
The merged set is an R-bush at (0,1), but the whole old H_j has radius h/8
there. Thus arbitrarily large vector excess can produce a merged mass
smaller than every old component. Replacing selected caps by whole old
bushes violates the tolerance.

Even the partition-square potential fails here. Put x=v_3 R^3. Replacing
the N blocks by their N remainders of mass p-x and the single merged block
of mass Nx changes the sum of squared block masses by

    N x [-2p+(N+1)x] < 0

for small h; the block count increases from N to N+1, and the largest block
mass decreases. These are smooth/full-dimensional models, not examples
satisfying the no-Frostman hypothesis.


There can even be a finite-cell regrouping cycle. Replace the spherical
cores by fixed smaller cube cores H_j=a_j+D, still in the constant region
of b_h, and partition the common offset cube D into R-microcubes Q_k.
Put P_jk=a_j+Q_k. Row unions H_j are exact time-zero bushes. Column unions
C_k=union_j P_jk are O(R)-bushes at time one, since b_h(a)+a=a-a_j is in
Q_k. Vector cap selection at (u_k,1), with u_k the center of Q_k, extracts
a column from the rows. Selection at (-a_j,0) extracts a row from the
columns. Both regroupings retain all points and the same finite carrier
microcells. The total source mass q is the same positive constant in both
partitions. At R=h^(5/2), delta=1, the row-to-column selected mass is of
order h^(9/2), and the column-to-row selected mass is of order h^3. The
vector denominator in both directions is q (C R)^2, of order h^5. The
excess ratios are therefore of order h^(-1/2) and h^(-2), respectively.
For each fixed h this is a finite-cell cycle in one fixed smooth selector;
letting h tend to zero is a varying-selector family, not an infinite-scale
claim for one fixed selector. Thus finite cell count alone gives no acyclic
partition order.

There is also an error-budget issue: the available merger estimate is
O(epsilon+R), whereas the vector test uses R>=epsilon. Repeating the
operation at a fixed tolerance does not preserve its numerical error bound
automatically. Re-covering by fixed-radius cells is possible but splits old
blocks and does not turn the partition into a coarsening. A finite packing
cell count therefore does not by itself imply finite mass-growing merges.

## 4. A sharper fixed-old-error near/far scale test

For an old collision residual r0 and a current physical bush error R,
the standard separated-time estimate gives source-fiber radius

    C (R+r0)/g

when the time gap is at least g. The same-window merger estimate carries
an error bounded by C(R+r0+L g), where L bounds the relevant direction
secants. To make both estimates uniformly smaller than a prescribed T,
the direct two-branch argument requires, up to fixed constants,

    (R+r0)/T <= g <= T/L,
    hence L(R+r0) <= T^2.

At the quadratic source-cap target T comparable to r0^(2/3), this
compatibility fails for fixed nonzero L: T^2 is smaller than r0.
This is a limitation of these uniform bounds; additional geometric time
alignment could improve them. It identifies a concrete intermediate-gap
obligation, rather than showing that all physical routing is impossible.

The relevant source statements are
`lem:v081-separated-old-time-fiber-cap` (13010ff),
`lem:v081-same-window-edge-flow-amplification` (13200ff), and
`cor:v081-same-window-carrier-reduction` (14170ff). The proof of the last
one explicitly relabels each local collision thickness as the later fine
scale rho. That substitution needs a new physical justification when the
occurrence still records the original residual r0.

## 5. The density product needs a loss budget

`lem:v081-bush-return-density-cocycle` (12275ff) proves the genuine bound

    D(H_next) >= g_l D(H),
    g_l = c A_l M_l R_l^(3-delta) Rhat_l^(-3),
    product_{l<L} g_l <= C/D(H_0).

This excludes g_l >= 1+c at every sufficiently late generation. It does
not bound the product over just the increasing generations. The sequence

    g_0,g_1,g_2,g_3,... = 2, 1/2, 2, 1/2, ...

has bounded prefix products and infinitely many gains, whose subproduct
diverges. Accordingly, the sentence beginning “Apart from density-increasing
generations whose multiplicative gains have bounded total product” and the
following `cor:v081-stopping-tail-compensation` (12347ff) require an
additional no-replenishment or summable-loss argument. The exact density
cocycle remains valid; the stronger tail interpretation is not a consequence
of that product inequality alone.

## 6. Direct old-time packets improve the proved cycle scale

The formally checked module `contact_cycle_rigidity` proves, for a genuine
old contact four-cycle with bounded frame entries M and determinant at least
Delta,

    |t_i-t_j| <= 48 M^2 r0/Delta.

Thus if the actual rooted edge time t0 lies in a cell of radius theta
centered at c, all four old times lie within

    theta + 48 M^2 r0/Delta

of c. The actual edges then collide at c with error at most

    r0 + L(theta + 48 M^2 r0/Delta).

The displayed packet corollary is an elementary consequence of the checked
pairwise-time theorem. It avoids the second inverse-frame factor required
to infer the packet from a scalar entry of the graph-slope matrix.
For Delta=r0^d, d<1/3 suffices to make this error o(r0^(2/3)), with an
appropriately smaller theta. The separate scalar-plane coherence estimate
uses r0/Delta^2 and hence the stricter d<1/6.

Actual origin-plane labels can still be necessary on the noncoherent
common-target branch: a time cell alone does not provide a genuine
rank-two old/new polarization packet or its weighted anchor law.
Moreover, if both source vertices of a bipartite rooted cycle already lie
in a T-cap, its bounded-chart determinant is at most C T. If both target
vertices also share a T-cap, the bound is C T^2. Thus a large absolute
threshold cannot remain available after arbitrary cap refinement.

## 7. Exact remaining positive target

A completion needs actual weighted geometry which does at least one of:

- pays determinant-small transverse/horizontal root occurrences at the
  quadratic root scale with the original ordered pairs and their weights;
- gives a valid Frostman escape for a positive aggregate remainder;
- supplies a genuine monotone or summably charged physical growth mechanism
  that survives partial-bush selection and the fixed old collision error.

The results above identify why the existing packing bound, qualitative
individual-bush modulus, and density-product identity do not yet supply
that step. No new hypothesis is being inserted into the final theorem.

## 8. Exact no-Frostman consequences and the remaining root-fiber charge

The exact-collision-null and fixed-angle vanishing consequences below now
have dedicated strict Lean builds and axiom readbacks. The packet-free local
bound is also checked with numerical constant 81. The finite Hausdorff-cover
routing construction is still being formalized; its status is separate.

First, failure of the front Frostman conclusion makes every positive-source
exact bush impossible. In fact the exact-collision pair set has zero product
mass. Otherwise C4 positivity, together with Lebesgue-nullity of degenerate
horizontal frames, gives a positive set of nondegenerate exact cycles.
Exact contact rigidity synchronizes their times. Fixing one positive-root
fiber leaves a positive set of source vertices through the same exact point
at the root collision time, contradicting the already proved exact-bush
Frostman escape.

Hence fine exact-residual neighborhoods decrease to a product-null set. A
fine witness coupling with fixed positive inherited mass cannot retain a
uniformly integrable density relative to the fixed raw product law. If the
old edge itself is required to be a fine edge, the allowed old marginal also
shrinks to zero. If the old target is retained only as a mark, a fine source
cycle can still be appended, but its normalized fresh density can diverge.
These are different constructions and must not be interchanged.

For a raw rooted completion kernel Q_rho(omega,dv), write

    w_rho(omega) = Q_rho(omega,V),
    p_rho(omega) = Q_rho(omega,transverse outputs).

After normalization preserving the old law Gamma_0, the relevant paid mass
is

    integral p_rho(omega)/w_rho(omega) dGamma_0(omega),

on the positive-success set. A bound on the unnormalized product integral
of p_rho does not imply this bound. In a regular graph of edge density M,
the rooted completion density is of order M^3, while total C4 mass is of
order M^4. Preserving old mass therefore already incurs an M^(-3) density
cost; normalization to a whole-cycle probability incurs M^(-4). At
M approximately rho^(2-eta), a single displayed gain rho^nu with nu<1 does
not overcome either cost. Independent old flags exclude the fully coherent
rank-loss class by a high power, but do not automatically amplify a single
transverse direction-union gain in this normalized root integral.

Compactness and dimH(K)<q provide a genuine additional uniform input: one
finite open-ball cover with arbitrarily small sum of R_i^q. Append a fresh
front time from the left or right quarter of the marked slab, choosing the
quarter separated from the inherited old time. First-hit assignment then
preserves the whole old law exactly and gives fractional branch weights at
most 8 R_i/(v-u). For sufficiently small cover radii, every branch is a
physical bush of error 2 R_i separated from its original collision time.
Combining this route with the packet-free one-bush estimate gives only the
available aggregate cost

    C m sum_i R_i (R_i+r_0)^2.

This is a source-faithful finite route, but its cubic cover cost does not
supply the requested quadratic root-scale payment from dimH(K)<4.

The cap-recentered local identity is also valid. If source directions lie
in a T_source-cap about a_0, old times lie in t_0+[-delta,delta], and the
source bush is centered at (c,s), then the old target at time t_0 is within

    R+r_0+delta L+|t_0-s| T_source

of c+(t_0-s)a_0. The smaller coefficient is useful, but after reversal that
known cap belongs to the opposite endpoint. A recurrence for the next
distinguished source cap has not been established. Partitioning both
endpoints into small caps can duplicate selector supports across labels;
small separate caps also leave fixed-angle edges cross-cap.

Finally, positive submeasure exhaustion does not turn arbitrarily small
absolute costs into a summable root budget. For example, available output
mass might be bounded by cost^p for p>1. Requiring a summable sequence of
shrinking costs can then prevent exhaustion. One needs a relative charge
bound for actual extracted old mass, or a global reference-measure budget
that sums independently of the number and scales of attempts.

The minimal unresolved theorem is therefore a genuine root-weighted
transverse/horizontal charge bound (or a valid Frostman alternative) for
these actual conditional completion laws. It cannot be replaced by success
positivity, an assumed capacity field, or a bound before normalization.
