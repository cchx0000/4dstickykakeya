# Fixed finite alphabet: an extremal-family extension of the projection argument

Status: independently audited handwritten proof adaptation, using the finite Lq inverse theorem as an external input; not a Lean endpoint. The selected-tree issue in the initial draft is resolved by UNIFORM_FAMILY_FLATTENING_LEMMA.md, which keeps original doubled-cell masses. The new steps here are the compact-family extremizer, the simultaneous finite-alphabet time estimate, and their combination. This is not a direct invocation of a published pleasant-model theorem on a non-uniquely-ergodic base.

## 1. Claimed scope

Fix B>=2 and a FINITE alphabet G={g_1,...,g_M} of maps {0,...,B-1}^3 -> R^3. Let x=(x_1,x_2,...) be ANY sequence in {1,...,M}^N; no recurrence, genericity, or unique ergodicity is assumed. With independent uniform full-cube digits D_j, set

    A = sum_j B^(-j) D_j,
    F_x = sum_j B^(-j) g_(x_j)(D_j),
    mu_(x,t) = law(t A + F_x).

For almost every t, simultaneously for every x, every rank-k orthogonal projection pi, and every q>1, the Lq dimension of pi_*mu_(x,t) equals k. The decay of natural grid q-moments is uniform over x and pi when t,q,k are fixed.

Every nonzero actual source sigma<=D Leb on the slope cube has front dimension 4 for each prescribed x, even after an arbitrary positive source restriction. This is a property of the actual independent-digit graph law; it does not assert that general sticky graphs admit this form.

## 2. Uniform fine-prefix occupancy for all sequences

The polynomial-minor proof in STATIONARY_GRID_GRAPH_PROJECTION_ESCAPE.md remains valid when taking the union over all M^n choices of the digit-map prefix. Only one common map prefix is chosen per tuple of slope words; the count is M^n, not M^(n(j+1)).

Choose an integer C>39+3 log_B M. For a j-tuple of independent slope differences, j=1,2,3, its selected output minor is a degree-j polynomial in t with leading coefficient at least B^(-jn). The total exceptional-time measure at depth n is bounded by

    sum_(j=1)^3 2j B^[n(3(j+1)+1+log_B M-C/j)],

which is summable. Thus for one full-measure set of t, all sufficiently deep minors are >=B^(-Cn), simultaneously for every map prefix.

At such a t choose an integer L>C+1. Every projected prefix cube of side 2^(-L m(n)), m(n)=ceil(n log_2 B), contains at most B^((3-k)n) original slope words. This follows from the same exterior-product/kernel argument and affine grid count as in the stationary note. All words have weight B^(-3n), so

    Z_q(pi_*mu_(x,t,n),2^(-L m(n))) <= B^(-kn(q-1))       (F)

for every sequence x, projection pi, and q>1. The eventual depth is common to x and pi.

## 3. Compact-family spectra and an actual extremizer

Fix one good t and q>1. Let O_k be the compact space of k-by-3 matrices with orthonormal rows. Use the compact state space

    Y_k = {1,...,M}^N x O_k,
    S(x,pi)=(shift(x),pi).

Write nu_y=pi_*mu_(x,t). This family is weakly continuous in y: a finite map prefix controls the projected law up to a uniformly bounded O(B^(-n)) tail. It has the exact prefix/tail convolution identity.

Use smooth grid moments equivalent, within constants independent of y and n, to the ordinary dyadic q-moments. Write Psi_n(y) for their logarithm at scale 2^(-m(n)). The elementary conditional convolution estimate behind Corso–Shmerkin Proposition 2.11 gives

    Psi_(n+n')(y) <= Psi_n(y)+Psi_n'(S^n y)+C_0.

It requires the exact convolution identity and uniform support bounds, not an invariant measure or unique ergodicity. The smooth moments make Psi_n continuous. Thus F_n=Psi_n+C_0 is a continuous subadditive cocycle.

Put a_n=max_y F_n(y). By Fekete,

    beta_k = lim_n a_n/n,
    alpha_k = -beta_k/log_2 B.

The ambient bound gives 0<=alpha_k<=k(q-1). For every epsilon>0, eventually

    Z_q(nu_y,2^(-m)) <= 2^[-(alpha_k-epsilon)m]            (U)

uniformly in y; bounded gaps between m(n) transfer this to every integer scale m.

There is an invariant ergodic measure attaining beta_k. Here is the compactness argument, included to avoid treating unique ergodicity as implicit. Choose y_n nearly attaining a_n and take a weak limit P of the empirical measures n^(-1)sum_(i<n)delta_(S^i y_n). It is invariant. The standard finite-block inequality for a subadditive cocycle gives, for every fixed N,

    beta_k <= (1/N) integral F_N dP.

Taking the infimum in N yields equality, since F_N<=a_N. Kingman's theorem and ergodic decomposition give an ergodic component with exponent beta_k. At a typical point y_* of that component,

    lim_m -log_2 Z_q(nu_(y_*),2^(-m))/m = alpha_k.         (E)

The projection coordinate is constant under S; ergodicity in particular fixes one projection for this extremizer. We have not made any assumption that an originally prescribed sequence is typical. It remains covered by the uniform bound (U).

## 4. Exact flattening inputs and why the published proof transfers

The proof adaptation uses the following three properties of this family:

1. Uniform natural q-moment upper bounds (U) at exponent alpha.
2. A uniform hyperplane margin: for some gamma>0, all hyperplane projections of every member have q-moments at most 2^[-(alpha-(q-1)+gamma)m] at sufficiently fine scales.
3. The exact prefix/tail convolution identity with uniformly bounded supports and tails remaining in the family.

The uniform-family lemma proves the following flattening conclusion: for every sigma>0 there is epsilon>0 such that, whenever a discretized probability eta has uniformly bounded support and Z_q(eta,2^(-m))<=2^(-sigma m),

    Z_q(eta*nu_y,2^(-m)) <= 2^[-(alpha+epsilon)m]          (S)

for every y and sufficiently large m (with harmless support/discretization constants).

The separate uniform-family lemma derives global and conditional pruning from the hyperplane margin and local tail decomposition, then uses an original-mass recursion K_s=sum_Q mu(2Q)^q on selected cells. Centering permits enlarged child covers inside the parent. This avoids comparing original parent mass to restricted parent mass. The lower q-moment bound needed for the inverse theorem is supplied by the failure of (S), not by a typical-point hypothesis. Support normalizations and bounded translations preserve the required estimates. The dependency on the published theory is isolated to its finite inverse Theorem 2.1.

Primary source for this dependency audit:

https://arxiv.org/html/2409.04608v1#S3

The zero case alpha=0 causes no issue: Young's inequality already gives a positive gain from the assumed q-moment decay of eta. In our application to rank k, the hyperplane margin follows from lower-rank induction as explained below.

## 5. Fine-prefix stabilization at the extremizer

For completeness, the required consequence of (S) can be proved without assuming any measure on the base other than the existence of the point (E).

Fix R>=1 and write m=m(n). Partition the prefix measure nu_(y_*,n) into coarse cells I at scale 2^(-m), with masses c_I. Let rho_I be the normalized restriction, rescaled by B^n and translated into a uniformly bounded box. Bounded-overlap grid comparisons and the convolution identity give

    Z_q(nu_(y_*),2^(-(R+1)m))
      <= C sum_I c_I^q Z_q(rho_I * nu_(S^n y_*),2^(-Rm)),

and

    Z_q(nu_(y_*,n),2^(-(R+1)m))
      >= c sum_I c_I^q Z_q(rho_I,2^(-Rm)).

Also sum_I c_I^q is comparable to Z_q(nu_(y_*),2^(-m)), since the omitted tail has diameter O(B^(-n)).

Separate cells according to whether Z_q(rho_I,2^(-Rm))<=2^(-sigma m). On these diffuse cells apply (S) at scale Rm with spread parameter sigma/R, obtaining a gain in the tail exponent. Their total contribution is exponentially smaller than the left side, using (E) at m and (R+1)m. On the remaining cells, use (U) for the tail. It follows that their sum of c_I^q is at least 2^[-(alpha_k+o(1))m]. The second displayed inequality then gives

    Z_q(nu_(y_*,n),2^(-(R+1)m))
      >= 2^[-(alpha_k+sigma+o(1))m].                     (P)

Because sigma>0 is arbitrary, this is the needed stabilization inequality. The opposite exponent inequality follows from the coarse-prefix comparison, but is not needed for the contradiction.

This is the same finite-prefix mechanism as Shmerkin's Proposition 5.2, with its actual inputs (E), (U), (S), and the convolution identity now supplied for the compact family:

https://annals.math.princeton.edu/wp-content/uploads/annals-v189-n2-p01-s.pdf

## 6. Induction and original source consequence

Rank zero has alpha_0=0. Assume alpha_(k-1)=(k-1)(q-1). If alpha_k<k(q-1), choose gamma smaller than this positive gap. The uniform rank-(k-1) bound from Section 3 applies to every hyperplane projection of every rank-k family member, giving the margin in Section 4. Thus (S) and (P) hold.

Take R=L-1 in (P). Inequality (F) gives the opposite bound with exponent k(q-1). Letting sigma tend to zero forces alpha_k>=k(q-1), a contradiction. Hence alpha_k=k(q-1). This yields uniform full q-moment dimension for every member, including every prescribed, arbitrarily nonstationary sequence.

The argument works for every q>1 at the same geometrically selected good t. Taking q=2 gives finite s-energy for all s<3 and all actual bounded-density source restrictions. Alternatively, choosing large finite q gives uniform spatial Frostman exponents arbitrarily close to 3 across the sequence family at a fixed good t. A positive actual time subset with bounded constants gives an original spacetime Frostman measure of exponent arbitrarily close to 4. No global time-integrability rate is asserted.

## 7. Boundaries of the extension

The finite alphabet is used to choose a good-time set simultaneously for EVERY sequence. For a continuous compact alphabet, the full shift contains the constant focus map g(d)=-t d at every t. Thus all-sequence full dimension at almost every t is false in that enlarged scope. A particular continuous-alphabet sequence might still obey an almost-every-time theorem, but it cannot be obtained by asserting good behavior of every invariant measure in its full hull.

Branch-dependent digit maps also fall outside the exact convolution identity here. A finite-state transducer gives a finite SUM of convolution identities after grouping by terminal state. This suggests a further extension, but it requires checking the matrix/subprobability version rather than silently identifying it with the family above.
