# Uniquely ergodic driven full-grid digit graphs

Status: handwritten extension of STATIONARY_GRID_GRAPH_PROJECTION_ESCAPE.md, using Corso–Shmerkin's actual pleasant-model theorem. This is not a formal Lean endpoint and does not infer stationarity or independent increments from packing dimension.

## Exact setup

Let (X,T,P) be a compact uniquely ergodic topological system. Fix B>=2 and D={0,...,B-1}^3. Suppose g_x(d) in R^3 is uniformly bounded in x,d; x -> g_x(d) is Borel and P-almost everywhere continuous for each of the finitely many d.

For independent uniform D-valued digits D_j, put

    A = sum_{j>=1} B^(-j) D_j,
    F_x = sum_{j>=1} B^(-j) g_(T^(j-1)x)(D_j),
    mu_(x,t) = law(t A + F_x).

Then for almost every actual time t, for EVERY x in X, every orthogonal projection pi of rank k=1,2,3, and every q>1,

    dim_Lq(pi_*mu_(x,t)) = k.

Every positive actual source restriction dominated by slope Lebesgue therefore has front dimension 4 over any positive-length time interval, for each x. The source is the original graph law of F_x as a Borel function of A off base-B boundary points.

## Why the stationary proof extends

For fixed t define

    Delta_t(x) = B^(-3) sum_(d in D) delta_((t d+g_x(d))/B).

Coincident atoms are aggregated. This is a pleasant model with contraction B^(-1): its finite support is uniformly bounded, it is Borel and P-almost everywhere continuous, and the base system is uniquely ergodic. Its infinite convolution law is precisely mu_(x,t). Every fixed orthogonal projection remains a pleasant model.

For EACH fixed x, the polynomial-minor argument in the stationary note applies verbatim to its varying finite prefixes. The leading source coefficients are still the same full B^(-n) grid. The estimates depend only on B, the exterior-product degree, and the common bound on the digit offsets, not on x or stationarity. The exceptional-time tail bound for n>=N is at most a constant times B^(-N).

All relevant finite-word coefficients depend measurably on x. Thus Tonelli plus Borel–Cantelli on P(dx) dt gives one full-measure set of t for which P-almost every x has the eventual minor bounds. Crucially, for each such x the fine-prefix estimate is uniform over every spatial projection and q:

    Z_q(pi_*mu_(x,t,n), 2^(-44m(n))) <= B^(-kn(q-1))

for sufficiently large n, where m(n)=ceil(n log_2 B). The threshold may depend on x,t but does not depend on pi or q.

Fix one such time t. Induct on k for the MODEL Lq dimension D_(pi model)(q). At rank zero the dimension is zero. If a rank-k projected model had dimension less than k, every one of its hyperplane projected models has dimension k-1 by induction; therefore it is q-unsaturated. Proposition 2.12(2) supplies a P-full set of base points for which the natural-scale Lq exponent equals the model spectrum. Intersect it with the already fixed P-full set having all-projection fine-prefix bounds. For any point in this intersection, Proposition 3.8 and the fine-prefix bound force the model spectrum to be at least k(q-1), a contradiction.

This argument is applied independently to each pi and q. It never intersects uncountably many typical-point sets: the good-time set was fixed using projection-independent polynomial minors, and for each proposed bad model only ONE base point in the appropriate full-measure intersection is needed.

Consequently all projected model dimensions equal k. Proposition 2.12(3), the uniform lower bound on the Lq exponent at EVERY base point, then gives dim_Lq(pi_*mu_(x,t))>=k for every x, including nongeneric x. The ambient upper bound gives equality. This last invocation is the step retaining a prescribed original sequence represented by a particular x.

## Precise external inputs

Corso–Shmerkin, Proposition 2.12(2)-(3) and Proposition 3.8:

https://arxiv.org/html/2409.04608v1#S2.SS3
https://arxiv.org/html/2409.04608v1#S3.SS4

The former supplies typical equality and the uniform all-base-point lower bound. The latter transfers an unsaturated model's natural exponent to every fixed exponentially finer prefix scale. Exponential separation of projected digit alphabets is not used.

## Uniformity boundary and macro-block warning

The exponent 42 in the polynomial-minor test is uniform in the base B and arbitrary bounded digit values. The asymptotic fine-prefix stabilization theorem has constants depending on the complete pleasant model and its quantitative unsaturation. The publication does not give the model-independent finite-block estimate that would be needed to replace arbitrary original macro blocks by a repeated artificial IFS.

For a FIXED base B, fixed digit bound, and fixed compact time window, compactness can in principle uniformize convergence on compact parameter subfamilies satisfying the full eventual minor inequalities. This is not uniform as B grows: the parameter dimension of g is 3B^3, and neither the compactness argument nor Proposition 3.8 controls its resulting scale in terms of log B.

A general sticky selector has not been shown to admit the driven independent-digit convolution identity used here. A sequence with long nonstationary concentration blocks also need not have a uniquely ergodic hull. Packing exponent 3 or sublinear vertical conditional entropy alone does not provide these hypotheses. Artificial repetition of one macro block changes the law; full dimension of the repeated model does not control its first block or the unrepeated source.
