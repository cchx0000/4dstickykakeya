# Stationary full-grid digit graphs: simultaneous full-dimensional projections

Status: handwritten proof, using an explicitly identified external theorem. No Lean theorem or replacement of the original Wang–Zakharov dependency is claimed. The proof applies to the stationary digit class below, including cyclic digit maps but also arbitrary coupled maps on one complete digit cube.

## 1. Exact class and conclusion

Fix an integer B >= 2 and any map g : {0,...,B-1}^3 -> R^3. Let D_1,D_2,... be independent uniform digits in this cube, and set

    A = sum_{j>=1} B^(-j) D_j,
    F = sum_{j>=1} B^(-j) g(D_j),
    X_t = t A + F.

Write mu_t for the law of X_t. The slope A is exactly uniform Lebesgue measure on [0,1]^3. Except on the null set of nonunique base-B expansions, F is a Borel function b(A). Thus the phase law is the actual graph source law, not a replacement of correlated marginals.

Claim: there is one full-Lebesgue-measure set of real times t such that, for EVERY orthogonal projection pi of rank k in {1,2,3}, and EVERY q>1,

    dim_Lq(pi_* mu_t) = k.

In particular the original front {(a t+b(a),t): a in E, t in J} has Hausdorff dimension 4 for every Borel E of positive Lebesgue measure and every interval J of positive length. More generally, the same holds for any nonzero finite actual source sigma dominated by a constant times Lebesgue measure on the slope cube. The source can be restricted arbitrarily before forming the front.

The phase carrier of the full digit law is the image of the symbolic product under the finite homogeneous graph IFS. It has upper box dimension at most 3. Compact positive-source graph restrictions can be obtained by Lusin if a literal compact single-valued graph is required. Nothing here decomposes a general sticky selector into this stationary class.

## 2. The external ingredient, precisely isolated

Use Corso–Shmerkin, *Dynamical self-similarity, Lq-dimensions and Furstenberg slicing in R^d*, Proposition 3.8, together with Proposition 2.12 / Lemma 1.5:

https://arxiv.org/html/2409.04608v1#S3.SS4

For a homogeneous self-similar measure nu with contraction B^(-1), its Lq spectrum T(q) is a limit. If nu is q-unsaturated on lines, meaning

    dim_Lq(nu) < dim_Lq(rho_*nu) + 1

for every hyperplane projection rho, then for every fixed integer R>=1 the level-n prefix measure nu_n satisfies

    lim_n -log_2 Z_q(nu_n, 2^(-R m(n))) / m(n) = T(q),

where m(n)=ceil(n log_2 B), up to an immaterial bounded rounding change, and Z_q denotes the grid q-moment. A one-point base is a pleasant model, so the typical-base-point hypothesis is automatic. The paragraph following Proposition 3.8 explicitly places exponential separation in the subsequent final step; it is NOT a hypothesis of this proposition. We replace that final separation step with the rank-counting estimate below.

Only this fine-prefix stabilization and existence of the natural spectrum are imported. In particular we do not invoke the stronger projected-exponential-separation condition for every line, which would fail whenever a projection identifies two first-level digit atoms.

## 3. Uniform polynomial minors at almost every actual time

For a word w of length n let a_w and b_w be the corresponding prefixes of A and F, and put x_w(t)=t a_w+b_w. There are B^(3n) words, all with weight B^(-3n), and their slope prefixes are exactly

    a_w in B^(-n) {0,...,B^n-1}^3.

Fix j in {1,2,3}. For each tuple w_0,...,w_j for which the j slope differences a_wi-a_w0 are linearly independent, choose one nonzero j-by-j coordinate minor of their matrix. Apply the same coordinate minor to x_wi(t)-x_w0(t). This gives a real polynomial p(t) of degree exactly j whose leading coefficient has absolute value at least B^(-jn).

Elementary sublevel bound: a degree-j polynomial with leading coefficient c satisfies

    Leb{t in R: |p(t)|<delta} <= 2j (delta/|c|)^(1/j).

Indeed factor p over C; if every root is at distance at least (delta/|c|)^(1/j), the product cannot have modulus below delta. Each root disk meets R in an interval of length at most twice this radius. This bound needs no arithmetic condition on the other coefficients, so g may have arbitrary real values.

At delta=B^(-42n), the exceptional time measure for one tuple is at most

    2j B^(n-42n/j).

There are at most B^(3n(j+1)) tuples. The union bound is summable in n, since

    3(j+1)+1-42/j < 0

for j=1,2,3 (the largest exponent is -1 at j=3). Borel–Cantelli therefore gives a single full-measure set T_good such that for t in T_good, and all sufficiently large n, EVERY chosen independent-slope minor has

    |p(t)| >= B^(-42n).

This event is chosen before ANY spatial projection, normal vector, q, or source restriction. It therefore permits time-dependent choices of those projections.

## 4. Fine projected cells contain at most the kernel-dimensional number of words

Fix t in T_good and an orthogonal rank-k projection pi. Let Q be any cube of side 2^(-44m(n)) in the k-dimensional target, and consider all words w with pi x_w(t) in Q.

If their slope prefixes have affine dimension at least 4-k, choose w_0,...,w_(4-k) with independent slope differences. Each output difference is within C 2^(-44m(n)) of ker(pi), a subspace of dimension 3-k. All output differences are bounded by a constant depending on t and g, uniformly in n. Multilinearity of exterior products then bounds every (4-k)-minor of these output differences by

    C(t,g) 2^(-44m(n)) <= C(t,g) B^(-44n).

For large n this is smaller than B^(-42n), contradicting Section 3. The constants are uniform over pi: orthogonal projection has norm 1, and the wedge bound uses only the common output diameter.

Thus the slope prefixes in Q lie in an affine subspace of dimension at most 3-k. Any affine d-plane intersects the finite grid {0,...,B^n-1}^3 in at most B^(dn) points: choose d coordinate functions whose restriction to its direction space is injective. Hence

    #{w: pi x_w(t) in Q} <= B^((3-k)n),
    (pi_*mu_(t,n))(Q) <= B^(-kn).

Consequently, simultaneously for every q>1 and every pi,

    Z_q(pi_*mu_(t,n), 2^(-44m(n))) <= B^(-kn(q-1)).       (1)

Exact projected collisions are allowed and their weights are aggregated in this inequality. No injectivity of the projected first-level alphabet is used.

## 5. Induction on projected dimension

Fix t in T_good and q>1. We prove the claim for all rank-k projections by induction on k. The rank-zero projected probability measure has Lq dimension 0.

Let pi have rank k, and suppose all projections of rank k-1 already have Lq dimension k-1. The measure nu=pi_*mu_t is homogeneous self-similar with contraction B^(-1); coincident first-level atoms can be aggregated without changing nu or its finite convolution prefixes.

Assume dim_Lq(nu)<k. Every hyperplane projection of nu is a rank-(k-1) projection of mu_t and has dimension k-1. Therefore nu is q-unsaturated on lines. Proposition 3.8 identifies the exponent on the left of (1), normalized by m(n), with T_nu(q). Equation (1) gives

    T_nu(q) >= lim_n [kn(q-1) log_2 B / m(n)] = k(q-1),

contradicting dim_Lq(nu)<k. The ambient bound gives equality. This proves all k simultaneously at the same t. As the geometric good-time event is independent of q, the conclusion holds for every q>1 without any uncountable-intersection step.

If a version of the flattening proposition is stated with an explicit positivity assumption on the Lq dimension, the zero-dimensional case can be excluded first by the standard elementary positive-Frostman-exponent fact for a nontrivial finite homogeneous self-similar probability measure. Nontriviality follows here from (1): a Dirac self-similar law would have only one first-level translation and hence all prefixes would also be Dirac, contradicting (1). A direct proof of the positive exponent chooses two sufficiently deep cylinder supports separated by a fixed gap. Any sufficiently small ball misses one of them, giving a recursive maximum-ball-mass contraction by a factor strictly below 1.

## 6. Retaining the original source and obtaining front dimension 4

Taking q=2 in the rank-3 conclusion gives dim_L2(mu_t)=3. Standard grid/ball comparison then yields finite s-energy of mu_t for every s<3, or equivalently enough finite-energy restrictions to show that mu_t annihilates every Borel set of Hausdorff dimension below 3. For the finite-energy version, choose s<s'<3; the q=2 grid moments are eventually <=r^(s'), and the dyadic energy sum converges. Thus no uniform-in-t constant is needed.

Let 0<sigma<=D Leb|_[0,1]^3 be the actual source measure, and let nu_t be its pushforward by a -> t a+b(a). Then nu_t<=D mu_t and nu_t has positive total mass for every t. It follows that every full-nu_t-measure slice carrier has Hausdorff dimension 3 for t in T_good. Hausdorff slicing over the actual height coordinate on any interval of positive length gives dimension at least 4 for the original front; the ambient upper bound is 4.

The same argument applies to an arbitrary positive restriction of sigma. No independent copy of sigma is introduced. Base-B boundary ambiguities have zero Lebesgue measure and hence zero sigma measure.

## 7. Scope and outstanding general gap

This proves a substantive stationary finite-alphabet graph class using an external inverse theorem. It is broader than a cyclic product class: g may couple all three digit coordinates. The proof is source-sensitive because the complete horizontal grid and its uniform word weights are essential in (1).

For a general sticky graph, packing exponent 3 does not supply an exact homogeneous convolution identity or Proposition 3.8's fine-prefix stabilization. Nor does it supply independent vertical digit increments with fixed distribution. Those are the remaining barriers to carrying this result into the unchanged general theorem. The result must not be presented as a decomposition of arbitrary selectors or as elimination of the main WZ dependency.
