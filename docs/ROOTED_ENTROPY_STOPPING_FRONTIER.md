# Root-preserving entropy stopping: a stronger deficit input, not a closure

Date: 2026-10-02. Status: independently audited handwritten probability and
dimension argument.
This note does not change the main theorem, add a hypothesis to it, or claim
that the missing geometric charge is proved. It strengthens the actual
no-Frostman input in a way suitable for a scale-coherent entropy argument.
The normalization and predictive-information countertests explain which
potential arguments still do not close the proof.

## 1. Fixed source and actual physical measure

Use the fixed supported source and common marked slab already constructed in
`ROOTED_TIME_RECURRENCE_FRONTIER.md`. Normalize once and write

    F(a,t) = (b(a)+t a,t),
    nu = F_#(sigma x uniform(J)),
    dim_H K < q < 4,       nu(K)=1,
    delta = 4-q > 0.

The physical compact front K, original source sigma, and actual times do not
change with scale. All logarithms below have base two. Fix the standard
half-open dyadic partition of R^4, with a harmless bounded initial partition
if the support meets several unit cubes. For nu-almost every z let Q_n(z)
be its level-n cube and put

    I_n(z) = -log nu(Q_n(z)).

For a cube Q of positive mass let p_1,...,p_16 be the relative masses of its
sixteen children. Define

    h_n(z) = -sum_i p_i log p_i,       z in Q,
    d_n(z) = 4-h_n(z).

Terms with p_i=0 are zero. Thus 0<=h_n<=4 and 0<=d_n<=4. Importantly,
h_n is the entropy of the actual front measure inside the actual physical
cube containing z. It is not the entropy of a newly normalized cycle law.

## 2. Local entropy averages, with the exceptional set controlled

There is an elementary almost-everywhere identity

    [I_N(z) - sum_{n=0}^{N-1} h_n(z)] / N -> 0.           (1)

A bounded initial information I_0, or an integrable finite initial
partition, makes no difference.

Proof. On a realized child, the information increment is

    j_n = I_{n+1}-I_n = -log p_child.

Its conditional expectation given the level-n cube is h_n. The centered
increments j_n-h_n are martingale differences. Their second moments have
one universal bound: conditionally,

    E(j_n^2 | Q_n) = sum_{i=1}^{16} p_i (log p_i)^2
                  <= 16 sup_{0<p<=1} p(log p)^2 < infinity.

Consequently the martingale series sum_n (j_n-h_n)/(n+1) converges almost
everywhere, since the sum of its second moments is finite. Kronecker's
lemma gives the Cesaro convergence in (1). This argument does not assume
uniformly positive child probabilities or bounded realized information
increments.

The dimension deficit gives, for nu-almost every z,

    I_N(z) < q N for arbitrarily large N.               (2)

Indeed, if for some N_0 a positive-mass set A obeyed the opposite inequality
for every N>=N_0, then every small dyadic cube meeting A would have
(nu restricted to A)-mass at most its side length to the q power. A ball
meets only a bounded number of dyadic cubes of comparable side length, so
this restriction would be a nonzero q-Frostman measure supported on K.
This contradicts dim_H K<q. Taking a countable union over N_0 proves (2).
Half-open dyadic boundaries cause no problem for this restriction argument.

Combining (1) and (2), almost every z has arbitrarily large N such that

    sum_{n<N} d_n(z) >= (delta/2) N.                    (3)

At every such N, at least (delta/16)N of its levels satisfy

    h_n(z) <= 4-delta/4.                                (4)

To check the constant, outside (4) each deficit is less than delta/4, and
inside it the deficit is at most 4. Thus (3) implies

    4 #{n<N satisfying (4)} + (delta/4)N >= (delta/2)N.

This is positive **upper** density along each root's own prefixes. It is
not a common positive-density set of scales, and it supplies neither lower
density nor a positive uniform density in the averaged root law.

### Any fixed block length is permitted

Fix k>=1 and use the nested partitions at levels 0,k,2k,... instead. There
are 16^k children per parent and the entropy bound is 4k. The same finite-
alphabet second-moment argument applies for this fixed k. Equation (2)
also holds along these levels: a positive restriction with all sufficiently
fine k-block cube masses bounded by 2^(-q k n) is still q-Frostman, with a
constant depending on k. Thus almost every root has a proportion at least
delta/16 of entropy-deficient blocks along arbitrarily long block prefixes,
where deficient means conditional block entropy at most (4-delta/4)k.
A countable intersection permits all integer k simultaneously. The same
argument permits every fixed initial scale and residue class modulo k.

## 3. A full-original-root stopping construction without p/w

For an initial cutoff N_0 define

    tau_N0(z) = first N>=N_0 with
                sum_{n<N} d_n(z) >= (delta/2)N.

This is a stopping time for the physical dyadic filtration (up to the
irrelevant one-level convention), and (3) makes it finite almost everywhere.
There is no assertion of a uniform bound or finite expectation for tau_N0.
If only new levels after N_0 may count, replace the displayed test by

    sum_{n=N_0}^{N-1} d_n(z) >= (delta/2)(N-N_0),
    N>N_0.

Its stopping time is also finite almost everywhere: removing a fixed finite
prefix does not change the limsup average deficit.
Nevertheless, for every epsilon>0 a finite T can be chosen so that

    nu{tau_N0>T} < epsilon.                              (5)

There is a source-faithful version with all old marks retained. Let Gamma
be one finite old occurrence law and let a(omega) be its original source,
with a_#Gamma dominated by C sigma. Append an actual time according to a
probability kernel kappa_omega satisfying

    kappa_omega(dt) <= C_J uniform(J)(dt).               (6)

The separated-quarter time choice already used by the finite Hausdorff-
cover route satisfies such a bound, with a fixed constant. It can depend
on the inherited old collision time; every other inherited mark remains
part of omega.

The joint law of (a(omega),t) is dominated by C C_J sigma x uniform(J).
Thus tau_N0(F(a(omega),t)) is finite almost everywhere for Gamma d kappa.
The fractional branch densities

    f_N(omega) = kappa_omega{t: tau_N0(F(a(omega),t))=N}

are measurable, lie in [0,1], and satisfy

    sum_{N>=N_0} f_N(omega) = 1      for Gamma-a.e. omega. (7)

For a sufficiently large finite T, their restrictions retain at least
(1-epsilon)Gamma(univ), and the tail plus the retained restrictions equals
Gamma exactly. This follows by dominated convergence on the original
occurrence law, even when C and Gamma(univ) are not normalized to one.
Retention is aggregate; no uniform retained fraction at every individual
root is asserted. The pulled-back time need not be a stopping time for an
unrelated preexisting old-occurrence filtration.

To keep the time label, use the unnormalized marked restrictions

    1_{tau_N0(F(a(omega),t))=N} Gamma(d omega) kappa_omega(dt).

Their time kernels are subprobability kernels still bounded as in (6).
Normalizing a single branch would introduce 1/f_N and is unnecessary here.

No old root is divided by f_N, no completion probability is inverted, and
no fresh endpoint replaces an old one. This is an actual full-root entropy
stopping route. Its outputs record entropy-deficient physical scale blocks;
**they have not yet been shown to be paid geometric outputs**. In particular,
the construction does not improve an inherited collision residual r_0 to
the stopping cube radius.

## 4. Why two natural bounded-potential repairs still fail

### Nested completion probabilities

Even suppose a raw successful-completion sequence is genuinely nested, with

    1>=w_0>=w_1>=...>0,
    0<=p_n<=w_n-w_{n+1}.

This stronger-than-known disjointness hypothesis yields, for 0<theta<1,

    sum_n w_n^theta (p_n/w_n) <= w_0^theta/theta.         (8)

Indeed concavity gives

    theta w_n^(theta-1)(w_n-w_{n+1})
        <= w_n^theta-w_{n+1}^theta,

which telescopes. The same estimate can be integrated against the unchanged
old-root law Gamma.

But (8) controls roots weighted by w_n^theta. It does not control the
required sum of p_n/w_n with the original root weights. Already
w_n=2^(-n), p_n=w_n/2 gives p_n/w_n=1/2 at every n. Thus even genuine nesting
and a finite capacity after positive-power reweighting do not remove the
normalization debt. The no-Frostman branch permits success probabilities
tending to zero, so that reweighting cannot be silently discarded.

### Vertical entropy can be replenished by predictive information

Let A_n and B_n denote dyadic horizontal and vertical labels of the fixed
phase law. Since both label sequences refine, the exact identity is

    H(B_{n+1}|A_{n+1}) - H(B_n|A_n)
      = H(B_{n+1}|A_{n+1},B_n)
        - I(A_{n+1};B_n|A_n).                           (9)

The innovation and release terms on the right are both nonnegative.
Small conditional vertical entropy therefore does not bound cumulative
innovations.

For uniform x in [0,1), take b(x)=fractional_part(2x). Then A_n consists of
binary digits 1,...,n and B_n of digits 2,...,n+1. For every n>=1,

    H(B_n|A_n)=1,
    innovation=1,       release=1.

Embedding this in one coordinate of a three-dimensional direction cube
gives a fixed, piecewise affine packing-three selector. It has a genuine
four-dimensional front. Thus charging each vertical innovation while
forgetting the equal predictive release repeats the density-cocycle error;
it is not a geometrically meaningful transverse charge.

## 5. Stress tests and the exact remaining estimate

- Radial selector b(a)=-t_0 a: away from the single time t_0 the front map
  is locally nonsingular. Its natural front measure is absolutely continuous,
  so h_n tends to 4 almost everywhere. The entropy-deficient stopping route
  is correctly not forced; the model has a Frostman exit.
- Smooth row/column cycling selectors: for each a, det(Db(a)+t I) is a
  monic cubic in t. It is nonzero for almost every t. The front map is
  locally nonsingular almost everywhere, and its natural front law is
  absolutely continuous. The same test succeeds despite bush regrouping
  cycles. Finite interfaces of piecewise smooth models are null.
- The fixed coordinatewise digit-resonance selector: the summable
  root/time heavy-event bound already proved in the recurrence note gives
  natural front lower local dimension four almost everywhere. Equation
  (1) then gives zero average entropy deficit. Entropy loss at the countable
  resonant times carries no time mass. Finite-time synchronization still
  does not substitute for the actual time variable.
- Rare, extremely long exceptional digit blocks: the abstract example in
  `SCALAR_PENCIL_PROJECTION_AUDIT.md` can have full limiting averaged
  Shannon entropy and lower local dimension zero almost everywhere. It
  does satisfy the pointwise upper-density defect conclusion above, while
  its deterministic averaged deficits tend to zero. Thus (3) cannot be
  converted by an incorrect Fatou argument into a common deterministic
  positive-density scale set.

A root-preserving way to complete this entropy route would be a **maximal**
or **stopped-scale** geometric estimate excluding a full-mass set of paths
with (3), using the actual packing-three phase source and horizontal volume
bound. For example, it would suffice to prove, for the delta supplied by
the contrary dimension assumption, that some N_0 satisfies

    (sigma x uniform(J)){
      sup_{N>=N_0} N^(-1) sum_{n<N} d_n(F(a,t)) >= delta/2
    } < 1.                                              (10)

The strict front deficit makes the left side exactly one for every N_0.
Unlike a polynomial moment estimate, (10) does not require a decay rate or
summability at deterministic scales. Unlike an averaged Shannon entropy
estimate, it controls the actual exceptional roots and their stopping scales.
The entropy identity and stopping construction prove neither (10) nor a
geometric inequality implying it.

In particular no estimate currently turns the actual transverse/cross-cap
outputs into increments of a bounded root potential. A successful increment
must both survive arbitrary later stopping and distinguish true geometric
mixing from the predictive releases in (9). The original packing bounds,
raw C4 payments, and probability-kernel bookkeeping have not supplied that
increment. This note gives a stronger original-data input and a precise
weaker-than-power endpoint for further research, not a repair of the final
geometric gap or its Lean axiom dependency.
