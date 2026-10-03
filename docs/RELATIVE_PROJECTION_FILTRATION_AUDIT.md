# Relative projection transversality and the filtration boundary

Date: 2026-10-03. Status: handwritten proof audit for independent review, not
Lean formalization. The original theorem is unchanged. No general geometric
repair, entropy inverse theorem, or stopped-root estimate is asserted here.

The relative polynomial estimate is valid and uniform. The all-slack reference
source also supplies genuine intermediate-scale regularity on correctly
normalized macroscopic components. A source-preserving affine approximation
lemma gives the desired low moment under an additional, explicit hypothesis.
What remains unproved is an inverse output compatible with the original source,
actual times, and stopping law.

## 1. A uniform relative polynomial estimate

Write

    A(a,b) = a,                 P_t(a,b) = b + t a.

For a linear subspace W of R^3 x R^3 and an integer
1 <= r <= rank(A restricted to W), let

    S = ||Lambda^r(A restricted to W)|| > 0.

For every epsilon > 0 and interval J,

    |{t in J : ||Lambda^r(P_t restricted to W)|| <= epsilon S}|
      <= C_r epsilon^(1/r),
    C_r = 2r binomial(3,r)^(1/(2r)).                    (1.1)

Here |.| is unnormalized Lebesgue measure. The constant is independent of W,
J, and the intercept coefficients. The bound can always be replaced by its
minimum with |J|.

Proof. By singular value decomposition, choose orthonormal w_1,...,w_r in W
whose wedge attains S. Among the binomial(3,r) coordinates of
Aw_1 wedge ... wedge Aw_r, one has coefficient c with
|c| >= S/sqrt(binomial(3,r)). The corresponding coordinate of
P_t w_1 wedge ... wedge P_t w_r is a degree-r polynomial p(t) with leading
coefficient c. On the event in (1.1),

    |p(t)/c| <= epsilon sqrt(binomial(3,r)).

Factor p(t)/c = product_(j=1)^r (t-z_j) over C. At least one factor has
absolute value at most [epsilon sqrt(binomial(3,r))]^(1/r). For real t,
|t-Re z_j| <= |t-z_j|, so the event lies in r real intervals of twice that
radius. This proves (1.1).

The exponent is sharp: on W = {(a,-t_0 a): a in U}, with dim U=r, the
ratio of the exterior norms is |t-t_0|^r.

### A precise predictable-plane interface

Let Gamma be a finite measure on a measurable root space Omega. Let
omega -> W(omega) be measurable and chosen using omega alone. Fix r with
rank(A|W(omega)) >= r almost everywhere. Let kappa_omega be probability or
subprobability kernels on J satisfying

    kappa_omega(dt) <= K dt                              (1.2)

for one finite K. With the unchanged joint law Gamma(d omega) kappa_omega(dt),

    mass{||Lambda^r(P_t|W(omega))||
                  <= epsilon ||Lambda^r(A|W(omega))||}
      <= K C_r epsilon^(1/r) Gamma(Omega).              (1.3)

This follows by applying (1.1) for each omega and then Tonelli. It requires
neither a union bound over plane labels nor normalization of small root pieces.
Variable r can be handled by partitioning Omega into its three possible values.
The interface is conditional: W must be chosen before the remaining actual
time is sampled from the kernel in (1.2). Merely writing a joint filtration
does not verify that condition.

## 2. Macroscopic components and all intermediate scales

Let mu be the one fixed reference phase measure and assume
A_# mu <= D Lebesgue_3. The occupied global reference net balls at absolute
scale s have uniformly bounded overlap, radius O(s), and lower masses

    mu(reference ball) >= c_zeta s^(3+zeta)             (2.1)

for every positive zeta, with constants depending on zeta but with the source
and reference nets already fixed.

Take a measurable reference component C_T satisfying BOTH

    mu(C_T) >= c'_zeta T^(3+zeta),
    C_T lies in a phase ball of radius O(T).            (2.2)

An occupied coarse reference ball is an appropriate example. Normalize
mu restricted to C_T and rescale phase space by T^(-1), obtaining a probability
nu_T on a fixed bounded ball. Its horizontal marginal obeys

    A_# nu_T <= (D/c'_zeta) T^(-zeta) Lebesgue_3.        (2.3)

There is also a support-count estimate. For 0 < rho <= R <= 1,

    N_rho(supp(nu_T) intersect B(x,R))
      <= C_zeta T^(-zeta) rho^(-zeta) (R/rho)^3.        (2.4)

Dyadic radii may be rounded within a fixed factor. To prove (2.4), use the
occupied GLOBAL reference net balls at absolute scale s=T rho which meet the
relevant part of the carrier. These balls lie in an enlarged phase ball of
radius O(TR). Their original mu-masses, with bounded overlap, have total at
most C D (TR)^3 by horizontal domination. Divide by their individual original
lower bound c_zeta(T rho)^(3+zeta). This bounds their number and hence the
covering number. Taking the support closure does not change the estimate
beyond fixed covering constants.

No lower bound is claimed for the mass of an arbitrary intersection of such
a fine ball with C_T. In particular, an arbitrarily thin witnessed subset of
C_T inherits the upper support count by inclusion, but generally fails (2.2)
and therefore does not inherit the normalized marginal estimate (2.3).

Fix eta>0 and put fine absolute scale s=T^(1+eta), delta=s/T=T^eta. For any
epsilon>0, first choose zeta small compared with epsilon eta/(1+eta), and
then take T sufficiently small. Equations (2.3)-(2.4) give simultaneously

    A_# nu_T <= delta^(-epsilon) Lebesgue_3,
    N_rho(supp(nu_T) intersect B(x,R))
      <= delta^(-epsilon) (R/rho)^3
             for delta <= rho <= R <= 1.               (2.5)

The constants can depend on the one source, eta, and epsilon. The source
does not change after choosing epsilon.

The intermediate-scale condition is essential. At the terminal delta scale
alone, an arbitrary bounded delta-direction Kakeya tube family can be encoded
by choosing b constant on each delta slope cube. Its horizontal marginal is
Lebesgue measure and its phase graph has O(delta^(-3)) delta cells. Therefore
a uniform near-three projection theorem from only those two terminal facts
would already address unrestricted finite Kakeya in R^4. The second condition
in (2.5), at every intermediate rho and local radius R, contains additional
sticky information which a valid inverse theorem must actually use.

## 3. An unnormalized affine approximation low moment

Let mu be a finite positive Borel phase measure of mass m, with

    A_# mu <= D Lebesgue_3.

Suppose mu = sum_(j=1)^M mu_j is a decomposition into positive measures,
for instance unnormalized restrictions to a measurable partition, and each
mu_j is supported on

    |b - L_j a - c_j| <= h,                            (3.1)

where L_j is a fixed real 3-by-3 matrix, c_j is fixed, and h>=0. These data
and the pieces are chosen before time t. Let Q_r be a cubic spatial grid
of side r>0, and put p_Q(t)=((P_t)_# mu)(Q). For every bounded interval J
of positive length and 0<theta<1/3,

    integral_J sum_Q p_Q(t)^(1+theta) dt
      <= C_theta M^theta D^theta m
                   |J|^(1-3theta) (r+h)^(3theta).      (3.2)

The estimate has no dependence on ||L_j|| or c_j. Crucially, it has no
inverse power of mu_j(R^6). The factor m is explicit; simultaneous scaling
of mu and D gives the correct homogeneity m^(1+theta).

Proof. If z=(a,b) in the j-th piece satisfies P_t z in Q, then
(L_j+tI)a+c_j belongs to Q+B(0,h). Whenever the determinant is nonzero,
horizontal domination gives

    p_(j,Q)(t) <= C D (r+h)^3 / |det(L_j+tI)|.          (3.3)

Since sum_Q p_(j,Q)(t)=m_j=mu_j(R^6),

    sum_Q p_(j,Q)(t)^(1+theta)
      <= [C D (r+h)^3 / |det(L_j+tI)|]^theta m_j.       (3.4)

The polynomial det(L_j+tI) is monic cubic. If its complex roots are
z_1,z_2,z_3, then three-factor Holder and |t-z_k|>=|t-Re z_k| give

    integral_J |det(L_j+tI)|^(-theta) dt
      <= product_(k=1)^3
             (integral_J |t-Re z_k|^(-3theta) dt)^(1/3)
      <= C_theta |J|^(1-3theta).                       (3.5)

The condition 3theta<1 permits coincident real roots as well. Singular times
form a finite null set. Finally,

    (sum_j p_(j,Q))^(1+theta)
      <= M^theta sum_j p_(j,Q)^(1+theta).

Integrate, apply (3.4)-(3.5), and sum m_j=m to prove (3.2).

For a probability source, h<=C r and MD<=r^(-epsilon) produce a moment
bounded by C r^((3-epsilon)theta), with J fixed. The existing heavy-root
comparison then gives a summable original root-time charge at dyadic r for
any beta<3-epsilon, PROVIDED this decomposition is available for that original
source at those absolute scales.

Applied only to a normalized macro component, (3.2) is a local estimate.
Combining many phase parents into a physical parent, or passing to arbitrary
physical stopping scales, requires a further argument; those steps are not
automatic consequences of convexity. Likewise, (2.5) does not presently
imply a decomposition (3.1) with h comparable to delta and M subpower.

## 4. Time adaptation and the stopping cost

The rank estimate cannot be applied to planes selected after the actual time
is known. The exact countertest is

    W_t = {(a,-t a): a in R^3}.

Here rank(A|W_t)=3 but P_t|W_t=0 for every t. Thus a family of individually
valid exceptional-set estimates can select its own exceptional plane at
every time.

Revealing increasingly fine time cells in a joint filtration does not remove
this problem. Conditional probability on a time interval of length u has
an L-infinity density at least u^(-1). In the simplest uniform case the
constant K in (1.2) becomes exactly u^(-1). At u comparable to delta and
epsilon comparable to delta, (1.3) has size delta^(1/r-1), which gives no
smallness. Revealing the exact time produces a Dirac conditional law and
destroys (1.2) altogether.

There is a second manifestation using stopping branches. Suppose a bounded
kernel is split into unnormalized subkernels kappa_N, with sum_N kappa_N=kappa
and each kappa_N<=K dt. Even if W_N(omega) is chosen without looking at t,
the separate polynomial estimate gives

    bad mass on branch N <= K C_r epsilon^(1/r) Gamma(Omega),

not that bound multiplied by the branch mass. Summing pays the number or
complexity of possible branches. If f_N(omega)=kappa_N(J), normalizing the
branch changes its density bound to K/f_N(omega). This is exactly a
normalization cost and cannot be silently removed.

### What freezing a parent does and does not accomplish

One can legitimately freeze a positive-mass source/time parent and a time
density layer BEFORE sending the future resolution to zero. For example,
start with kappa_omega<=K_0 dt and restrict to a measurable event E of
positive joint mass. Put f(omega)=kappa_omega(E_omega). Some fixed alpha>0
has a positive amount of retained joint mass on {f>=alpha}. On that layer,
the restricted law disintegrates as

    [1_(f>=alpha) f(omega) Gamma(d omega)]
       [1_(E_omega)(t) kappa_omega(dt)/f(omega)],

and the displayed conditional probability kernel has density at most
K_0/alpha. This is a finite constant independent of subsequently chosen
finer scales. No all-root retention conclusion is asserted by this positive-
mass selection.

This freezing step can supply the kernel part of the interface (1.2). It
does NOT supply a plane measurable with respect to the frozen root data
before the remaining fine actual time is revealed. That is still an inverse-
geometry requirement. A statement that almost every fixed-time slice is bad,
including one obtained from common-time slice covers and fixed heavy-bush
families, does not itself provide such predictable planes.

## 5. Entropy release and the remaining input

For phase labels C_n=(A_n,B_n), put V_n=H(B_n|A_n). The horizontal predictive
release obeys

    I(A_(n+m); B_n | A_n) <= V_n.

Thus V_n=o(n) makes this term o(m) on blocks m comparable to n. This is a
valid reason to use macroscopic blocks; it does not justify a fixed-size
phase-tangent argument. The off-diagonal sparse digit deletion test has
fixed-block phase tangents with rank A=rank P_t=2 even though its actual
nonzero-time projections have dimension three.

A precise sufficient missing input for the present route is a source-faithful
finite-scale inverse statement which, from the ACTUAL projected deficit and
the intermediate-scale reference structure (2.5), yields useful geometry
before the remaining actual time is revealed, with controlled retained mass
and no inverse completion probability. One particularly concrete sufficient
output would be the affine graph decomposition (3.1), at h comparable to the
fine scale and with subpower M, on the relevant original law. It is stronger
than what has been proved and is not asserted to be necessary.

A different acceptable output could use predictable low-rank planes and
(1.3), but it would have to relate the actual entropy deficit to a relative
rank loss, control plane and stopping-label complexity, and pay the remaining
root weights. Neither relative ranks alone nor lower bounds from ordinary CP
sceneries establish that implication. Even a successful averaged entropy
comparison would still require the pointwise or maximal/stopped-scale
conclusion identified in ROOTED_ENTROPY_STOPPING_FRONTIER.md.

No further general proof route avoiding this missing inverse or geometric
input has been verified in this audit.

## 6. Primary theorem applicability checks

* [Benard and He, Effective equidistribution of random walks on simple
  homogeneous spaces, Theorem 4.1 and equation (14)](https://arxiv.org/html/2511.13512v3#S4)
  use avoidance of constraining pencils at the ambient threshold
  (k/d) dim W. Their covering conclusion retains exponent k/d, and the
  Brascamp-Lieb datum uses weights d/(kJ). In dimension six with output
  dimension three this is exponent one half and weights 2/J. Their theorem
  contains no replacement of ambient dimension by rank(A|W). On W=U x U,
  dim W=2 dim U while A and generic P_t each have rank dim U; the ambient
  Brascamp-Lieb constraint remains real. Consequently (1.1) does not turn
  their stated theorem into the desired near-three preferred-projection
  comparison.

* [He, Orthogonal projections of discretized sets, Theorem 1](https://arxiv.org/html/1710.00795v2#S1.SS1)
  assumes quantitative nonconcentration near every complementary-plane
  Schubert obstruction. The scalar pencil lies in a fixed such obstruction:
  its row space V_t={(tu,u)} intersects
  span{(e_1,0),(0,e_1),(e_2,0)} for every t. The theorem is therefore not
  directly applicable. Its input-exponent gain above one half is also not
  the full exponent needed here.

* [Du, Restricted Marstrand projection theorem for general families of
  linear subspaces, Conjectures 1.5 and 1.6 and Theorem 1.7](https://arxiv.org/html/2510.16671v1#S1)
  distinguishes its general analytic-family rank-profile conjecture from
  proved results. Theorem 1.7 concerns a family of two-planes in four-space
  with a maximal generic-rank condition on every input subspace; it does
  not establish the source-sensitive six-to-three assertion used here.
  The relative polynomial fact (1.1) is elementary, but the proposed entropy
  consequence is not a corollary of those stated results.

The conclusions above retain the original support and theorem. Equations
(1.1), (1.3), (2.3)-(2.5), and (3.2) are handwritten statements with the
proofs supplied here, not newly certified Lean declarations.
