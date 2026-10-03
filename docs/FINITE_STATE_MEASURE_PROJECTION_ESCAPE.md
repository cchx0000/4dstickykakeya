# Finite-state digit graphs: a source-retaining projection argument

Status: handwritten consequence of the separately proved UNIFORM_FAMILY_FLATTENING_LEMMA.md, whose deep input is the published finite Lq inverse theorem. This is not a Lean endpoint. Unlike the earlier loop-subset proof, this argument retains the actual uniform source law and all its bounded-density restrictions.

## 1. Exact finite-state model

Let S be a nonempty finite state set, B>=2, and D={0,...,B-1}^3. Fix maps

    T : S x D -> S,
    g : S x D -> R^3.

Starting at s, take independent uniform digits D_j, set s_0=s and s_j=T(s_(j-1),D_j), and define

    A=sum_j B^(-j)D_j,
    F_s=sum_j B^(-j)g(s_(j-1),D_j),
    mu_(s,t)=law(t A+F_s).

There is a single full-measure set of t such that, for every initial state s, every orthogonal projection pi of rank k=1,2,3, and every q>1,

    dim_Lq(pi_*mu_(s,t))=k.

The natural q-moment upper bounds are uniform over s and pi at each fixed good t and q. The source A is literal slope Lebesgue on the cube, and F_s=b_s(A) is a Borel function off the null ambiguous-expansion set. Thus every nonzero actual sigma<=D_0 Leb and every positive restriction of sigma has front dimension 4.

## 2. Fine-prefix occupancy

For each initial state and length n, the words still have distinct horizontal prefixes forming the complete B^(-n) grid, each of weight B^(-3n). Their intercept prefixes are bounded and are independent of t. The polynomial-minor argument is unchanged; taking a union over finitely many initial states multiplies the exceptional-time estimate by |S|.

Consequently, for almost every t and all sufficiently large n, simultaneously for all initial states and all rank-k projections,

    max_Q (pi_*mu_(s,t,n))(Q) <= B^(-kn)

at cube side 2^(-44m(n)), m(n)=ceil(n log_2 B). The same bound holds for the AVERAGE prefix measure over all initial states. Its q-moment is at most B^(-kn(q-1)). This includes all prefix collisions with their original symbol weights.

## 3. Worst spectra without assuming equality between states

Fix a good t and q>1. For each rank-k projection pi, let

    M_n(pi)=max_s Z_q(pi_*mu_(s,t),2^(-m(n))).

Use smooth grid moments, equivalent up to fixed constants, when continuity in pi is needed. The actual graph-directed prefix decomposition and convexity imply

    M_(n+n')(pi) <= C M_n(pi) M_n'(pi),

with C independent of pi,n,n'. The reason is that at a coarse parent cube all contributing scaled tails are original state laws; their total prefix weight is bounded by the mass of a fixed enlarged parent cube. Their fine q-moments are bounded by M_n'(pi), and summing enlarged-parent q-masses costs only a dimensional constant.

Thus F_n(pi)=log_2 M_n(pi)+C_1 can be chosen subadditive. Each F_n is continuous after smoothing. The numbers a_n=max_pi F_n(pi) are subadditive, and

    beta_k=lim_n a_n/n,
    alpha_k=-beta_k/log_2 B

exist. They give uniform natural bounds, for every epsilon>0,

    Z_q(pi_*mu_(s,t),2^(-m)) <= 2^[-(alpha_k-epsilon)m]

at sufficiently fine m, for all s and pi.

There is a projection pi_* attaining the worst limiting exponent. To see this, choose pi_n nearly maximizing F_n and pass to a convergent subsequence pi_n->pi_*. For any fixed N, subadditivity gives

    F_n(pi_n)/n <= F_N(pi_n)/N + O_N(1/n).

Hence beta_k<=F_N(pi_*)/N for all N. The reverse bound follows from F_N<=a_N, so the limiting exponent at pi_* is beta_k.

Define the finite mixture

    mu_bar = |S|^(-1) sum_s pi_*mu_(s,t).

Positivity and convexity give

    |S|^(-q) M_n(pi_*) <= Z_q(mu_bar,2^(-m(n))) <= M_n(pi_*).

Therefore mu_bar has natural q-exponent alpha_k at every sufficiently deep scale in the limiting sense. We do NOT assert that all individual state exponents are equal, including across transient states. The mixture is used only to witness the worst exponent; the eventual uniform conclusion applies to every original state.

## 4. Uniform flattening for the state family

Induct on k. Assume the uniform rank-(k-1) exponent equals (k-1)(q-1). If alpha_k<k(q-1), this gives a uniform positive hyperplane gap relative to alpha_k for the family of rank-k projected state laws.

The family satisfies the local tail decomposition (T) in UNIFORM_FAMILY_FLATTENING_LEMMA.md. Specifically, expand to a prefix depth for which each tail's entire support has diameter less than a fixed small fraction of the parent cube. Every tail component meeting that cube is wholly contained in its doubled cube, and hence the sum of its original prefix weights is bounded by the doubled-cube mass. The tails can have different terminal states, all still in the same finite family.

The uniform-family flattening lemma therefore applies with alpha=alpha_k. It gives a fixed gain whenever the other convolution factor has an exponentially small q-moment. The proof carries all component weights without normalizing the original state law or assuming a common spectrum for its components.

## 5. Fine-prefix comparison for a finite sum of convolutions

For the mixture mu_bar, group length-n prefixes by terminal state v:

    mu_bar = sum_(v in S) lambda_(n,v) * S_(B^(-n)) nu_v,

where nu_v=pi_*mu_(v,t), each lambda_(n,v) is a positive subprobability measure, and

    lambda_n=sum_v lambda_(n,v)

is the average ORIGINAL prefix law. No component is divided by its total mass.

Fix R>=1 and m=m(n). Partition each lambda_(n,v) into coarse cells I at scale 2^(-m). Write p_(v,I)=lambda_(n,v)(I), and let rho_(v,I) be its normalized restriction, rescaled by B^n; terms with zero weight are omitted. Bounded spatial overlap and the fixed number of states give

    Z_q(mu_bar,2^(-(R+1)m))
      <= C |S|^(q-1) sum_(v,I) p_(v,I)^q
           Z_q(rho_(v,I)*nu_v,2^(-Rm)).                 (1)

All normalized restrictions have bounded support after translation. The original weight p_(v,I)^q remains outside their q-moments. Also,

    sum_(v,I) p_(v,I)^q <= Z_q(lambda_n,2^(-m))
      <= C Z_q(mu_bar,2^(-m)).                          (2)

The last comparison follows from a coupling that moves every prefix point by at most C B^(-n), regardless of its terminal state.

For pieces with Z_q(rho_(v,I),2^(-Rm))<=2^(-sigma m), apply uniform flattening at scale Rm with spread parameter sigma/R to improve the exponent in (1). The normalized restrictions have a fixed uniform support bound after translation. Equations (2) and the exact natural exponent of mu_bar make their contribution exponentially negligible. For the remaining pieces, use the uniform natural tail bound at alpha_k. This yields

    sum_(remaining v,I) p_(v,I)^q
      >= 2^[-(alpha_k+o(1))m].                          (3)

By positivity of the component measures and the disjoint coarse partition within each component,

    Z_q(lambda_n,2^(-(R+1)m))
      >= c sum_(v,I) p_(v,I)^q Z_q(rho_(v,I),2^(-Rm))
      >= 2^[-(alpha_k+sigma+o(1))m].                   (4)

The factor |S|^(q-1) and every grid-comparison constant are fixed and vanish after normalization by m. Tiny subprobability components cause no inverse-mass factor anywhere.

Take R=43 and compare (4) with Section 2's fine-prefix upper bound. Since sigma>0 is arbitrary, alpha_k>=k(q-1), contradicting the assumed deficit. The ambient bound yields equality. Induction from rank zero proves the claim for all ranks and all states.

## 6. Actual source retention and scope

At good t, rank-3 q=2 dimension gives finite s-energy for each original state law for every s<3. A nonzero actual source sigma dominated by slope Lebesgue pushes to a measure dominated by the corresponding mu_(s,t), so it inherits these energies. On a positive actual time subset with bounded energy or potential-cut constants one obtains an original spacetime Frostman measure of exponent arbitrarily close to 4. This proves front dimension 4 and survives arbitrary positive original source restrictions.

No uniform whole-slab heavy-root power estimate is claimed: time-dependent constants are controlled by restricting to a positive set of actual times. The result is a finite-state branching class, not an assertion that every packing-three graph has finite state complexity. A general phase-cell process can have an increasing number of tail types and state-dependent laws; the fixed-state bounds and finite-sum comparison above do not automatically cover it.
