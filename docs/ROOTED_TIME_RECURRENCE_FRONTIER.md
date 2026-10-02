# Rooted time recurrence from a literal front deficit

Date: 2026-10-02. The density-to-rooted-recurrence core is now Lean-certified
in `Theorems/Thm_StickyKakeya4_rooted_heavy_limsup.lean`. All eleven declarations
passed strict direct compilation, the dependency-aware 8,755-job target build,
and strict axiom readback, with only `propext`, `Classical.choice`, and
`Quot.sound`. Logs are `verification/rooted-heavy-limsup-build.log` and
`verification/rooted-heavy-limsup-axioms.log`.

The original-data endpoint uses only `IsStickyDatum` and a strict front
dimension deficit to construct one positive finite source bounded by volume,
a measurable intercept, a common height slab of length 3/8, and beta in (0,3).
It proves full product-almost-everywhere heavy-bush recurrence and divergence
of the sum of heavy-event product masses. Its displayed transverse radius is
2r_n; fixed dyadic shifts give the radius convention used below. The generic
recurrence theorem applies to any fixed supported bounded-slope source, so it
can be used after the existing reference packing pretrim. The short original-
data endpoint itself does not restate the vertical nets or counts.

The polynomial-logarithmic extraction, exact k-time synchronization, angular
pigeonholing, resonance countertest, and conditional near-coordinate analysis
below remain independently checked handwritten mathematics. The previously
published bush-count note is unchanged.

The new premise is stronger than an arbitrarily fine excessive graph: it keeps
one original source and a continuum of actual physical times. A finite number
of selected times cannot substitute for that continuum. The last section
identifies the estimate that has not been obtained.

## 1. One fixed actual front measure

Let sigma be a probability source with bounded slope support |a|<=A, let b be
its Borel intercept map, and let J be a fixed positive-length common marked
height interval. Write

    Pi_t(a)=b(a)+t a,
    F(a,t)=(Pi_t(a),t),
    nu=F_#(sigma x Lebesgue restricted to J).

Assume that this literal measure is supported on the one original compact
front K and

    dim_H K < 1+beta,       0<beta<3.                      (1)

There is no affine chart or source changing with the fine scale here. A
positive original source from the reference packing construction can first be
normalized once; its density constant then remains fixed.

For nu-almost every z, and every fixed C>0, one has

    nu(B(z,2^(-n))) > C 2^(-(1+beta)n)

for arbitrarily large n. To prove this, fix integer bounds C,N and consider
the set of centers where the reverse inequality holds for every n>=N. If
its restriction has positive mass, a small arbitrary ball meeting that set
is contained in a comparable dyadic ball centered in it. The restricted
measure is therefore (1+beta)-Frostman at small radii; finiteness supplies
the large-radius constant. This contradicts (1). A countable union over
C,N proves infinite dyadic upper (1+beta)-density almost everywhere.

The physical geometry gives an exact upper bound for these front balls:

    nu(B(F(a,t),rho))
       <= 2 rho sigma{a': |Pi_t(a')-Pi_t(a)|<=(1+A)rho}.   (2)

Indeed a contributing point F(a',s) has |s-t|<rho, and moving it back to t
changes its spatial coordinate by at most A rho. Its allowed s-interval has
length at most 2rho. This uses the original source and times, not a new
collision relation at a relabeled error.

Choose an integer ell with 2^ell>=1+A and apply (2) at
rho=2^(-(n+ell)). The preceding density statement holds with arbitrarily
large fixed coefficients. Thus, for every fixed c>0, the actual events

    E_n(c) = {(a,t): sigma(Bush(t,a,2^(-n))) > c 2^(-beta n)}

have full limsup in sigma x dt on the marked slab. The bush radius is really
2^(-n); the fixed shift ell absorbs the factor in (2).

The same argument works after any fixed positive source restriction or fixed
positive-length subinterval of the marked slab, as long as the resulting
literal front measure is still supported in K.

## 2. Same-scale root and time mass with logarithmic losses

Set r_n=2^(-n) and P_n=(sigma x dt)(E_n(1)). Full limsup implies

    sum_n P_n = infinity.

Otherwise the first Borel--Cantelli lemma would make the limsup null. In
particular there are infinitely many n with P_n>=n^(-2). This assertion does
not mean a positive proportion of all scales, nor a uniform positive lower
bound for P_n.

At one such scale write P=P_n, L=|J|, and

    l(a)=|{t:(a,t) in E_n(1)}|,
    R={a:l(a)>=P/2}.

Since sigma is a probability and 0<=l<=L,

    sigma(R)>=P/(2L),
    integral_R l(a) d sigma(a)>=P/2.                     (3)

Each root in R has a set of actual heavy times of length at least P/2, with
bush mass greater than r_n^beta at every such time. Along the selected scales,
root mass and time-fiber length are therefore bounded below by a negative
power of n. They are subpower in r_n, and the physical error remains r_n.

## 3. Exact synchronization of any fixed number of times

Fix k>=2 and put g=P/(4k^2). For a root in R, sample k times independently
from its heavy fiber, using unnormalized Lebesgue volume first. For any pair,
the conditional probability of separation below g is at most 2g/l(a).
The union bound over the pairs gives bad probability at most

    k(k-1)g/l(a) <= 1/2.

Hence at least half the k-fold time volume has every pair separated by g.
By Jensen and (3),

    integral_R l(a)^k d sigma(a) >= (P/2)^k.

Fubini therefore selects actual common heights t_1,...,t_k in J such that

    |t_i-t_j|>=g for i!=j,
    sigma{a in R: (a,t_i) in E_n(1) for every i}
        >= P^k/(2^(k+1)L^k).                            (4)

For fixed k and P>=n^(-2), this is a polynomial-in-n root mass and a
polynomial-in-n time gap. No replacement of t_i by a bin center is needed,
so synchronization creates no additional physical residual.

If sigma<=D volume with D fixed, a direction ball of radius theta has mass
at most C D theta^3. Take theta=c_D r_n^(beta/3) so that its mass is at most
r_n^beta/2. Deleting neighbors with |a'-a|<=theta leaves at least half every
heavy bush. The remaining angular range has O(n) dyadic shells. Choose one
heavy shell for each root and each of the k times, then pigeonhole the k
shell labels. One common-root set remains with at most an additional O(n)^k
loss, and every selected leaf has mass at least

    r_n^beta/(C n)

in its assigned actual shell. Different selected times may have different
shell radii. This does not assert fixed-angle separation independent of n,
and it never replaces the residual r_n by a smaller radius.

These synchronization statements are valid, but they discard information
that a closing argument needs: the original fiber had positive time measure,
not just k selected points.

## 4. A fixed resonance model excludes a finite-time substitute

The following construction was independently audited. It is included only
because it refutes the proposed inference from finitely many simultaneous
scalar leaves to dimension inflation. It does not satisfy (1).

Choose N>=2, B=N^2, and let

    C={sum_{l>=1} d_l B^(-l): d_l in {0,...,N-1}}.

Let X,Y be independent natural digit variables on C. The base-B digits of

    a=X+NY

are uniform on {0,...,B-1}, so a is exactly uniform on [0,1]. Define b(a)=X
by the canonical digits, and use three independent coordinate copies. The
compact phase support is

    G={(X+NY,X): X,Y in C^3}.

It is an invertible linear image of a sixfold product of 1/2-Ahlfors regular
Cantor laws. Thus G and its phase law are 3-Ahlfors regular and have packing
dimension three. The literal canonical graph is dense in G. A base-B direction
cell fixes all output digits through its depth, giving O_N(1) vertical support
count at every radius, also for the closure and every source restriction.

For the fixed sequence of positive times

    t_j=B^(-j)/(N-B^(-j)),       j>=1,

one has

    Pi_(t_j)=(1+t_j)(X+B^(-j)Y).

After the first j digits, each scalar output digit is in {0,...,2N-2}; there
are no carries because 2N-2<B. Set

    alpha=log(2N-1)/log(B).

The three-dimensional projected support has dimension 3alpha. Its radius-r
covering number is O_N(r^(-3alpha)), uniformly in j: each scalar support is a dilation of a subset of the same enlarged-digit
Cantor set, with dilation factor uniformly bounded. The projected
measures have nonuniform digit probabilities and are not asserted to be
Ahlfors regular.

For any probability measure with support covering number O(r^(-d)), the
measure of points z satisfying mu(B(z,r))<=r^beta is O(r^(beta-d)): partition
the support into O(r^(-d)) sets of diameter at most r and bound every cell
that contains such a low-mass center. Therefore, whenever beta>3alpha,
almost every root has r-bush mass greater than r^beta eventually at every
one of any fixed finite collection of the t_j. The constants and all selected
time gaps are fixed before r tends to zero.

There is a stronger version. For t_j<=r/(2sqrt(3)),

    Bush(0,a,r/2) subset Bush(t_j,a,r).

Only O(log(2/r)) remaining indices have larger t_j. The preceding uniform
cover bound and a union bound show that failure of simultaneous heaviness
at **all** resonant times has source mass at most

    C log(2/r) r^(beta-3alpha).

This is summable along dyadic scales. Thus all resonant times can be heavy
simultaneously at every sufficiently fine scale for almost every root. In
particular even a growing number k(r)=o(log(1/r)), with smallest selected
time gap r^(o(1)), does not replace actual time measure.

The model is an actual compact marked patch. With a in [0,1]^3, unit marked
segments contain [0,1/2], and t_j<=t_1=1/(N^3-1)<=1/7. If the unit slope-ball
chart is required, apply the fixed affine change

    a_tilde=(a-(1/2,1/2,1/2))/2,       b_tilde=b/2

and use literal volume on [-1/4,1/4]^3. The fixed source mass is then 1/8;
all exponents and eventual inequalities survive fixed constants. No changing
selector, moving support, or added full-direction front is used.

### The model does not have the required continuum recurrence

Its coordinate product structure gives a direct quantitative distinction.
For one scalar direction variable, the collision-time length of a pair is
at most

    min(|J|,2r/|a-a'|).

Uniform scalar direction density therefore gives the averaged scalar bush
mass O(r log(2/r)), independently of the digit resonance. A three-dimensional
ball bush has mass at most the product of the three scalar interval-bush
masses. If that product is at least r^beta, one factor is at least r^(beta/3).
Markov's inequality and a union bound yield

    (sigma x dt){sigma(Bush(t,a,r))>=r^beta}
       <= C r^(1-beta/3) log(2/r),       beta<3.           (5)

This is summable dyadically. It cannot obey the full-limsup conclusion of
Section 1. In fact (5), combined with that conclusion, proves the actual
compact marked front has dimension four: any strict deficit would permit a
beta<3 contradicting (5). This is an unconditional supported-front escape
for this coordinatewise-separable model.

The factorization used in (5) is not available for a general coupled selector
b(a_1,a_2,a_3). Three correlated coordinate events cannot simply be multiplied.

## 5. What the original continuum ledger actually supplies

The source's `v046-four-cluster-seed` and
`v046-sticky-four-cluster-extraction` provide nondegenerate projected tetrahedra
on a fixed positive-measure time set. The cluster weights obtained from a
source of mass m are only of size m r^(3+zeta). Remez control on a shorter
prescribed time set changes its determinant threshold, not these tiny masses.
The source's `v047-exact-spatial-endpoint` explicitly identifies the remaining
upgrade from such persistent seeds to uniform transverse Frostman kernels.
None of these statements bounds the product measure of the heavy events E_n.

A finite Hausdorff cover also does not remove the fixed physical error. If B
is a source bush of error r at height s_0, and |t-s_0|>=g, then its preimage
of a spatial ball of radius R at height t lies in a direction ball of radius
C(R+r)/g. Hence a slice cover by balls of radii R_i gives only

    sigma(B) <= C D g^(-3) sum_i (R_i+r)^3.                (6)

Hausdorff dimension controls sums of R_i^s, not the extra number-of-balls term
introduced when R_i<<r. Choosing the cover first and then r below its minimum
radius gives a small absolute bound, but supplies no relation between that
minimum radius, the incoming r^beta masses, and the number of later bushes.
Their source sets can vary with r. A weak limit of their normalized fronts
cannot silently be declared supported on one fixed low-dimensional set.

## 6. Conditional near-coordinate continuum charge

This section is a **conditional, unformalized source-level implication**. Its
external input is the three-dimensional shaded Kakeya theorem used in the
manuscript's `v058-dense-shading-multiplicity`; it is not proved by the current
Lean project and is not the preexisting four-dimensional Wang--Zakharov axiom.
It is not being inserted as an axiom or used to claim the user's required
axiom-free completion.

The primary statement was checked in Guth--Wang--Zahl,
[A streamlined proof of the Kakeya set conjecture in R^3, Theorem 1.1 and
Remark 1.2](https://arxiv.org/html/2601.14411v1). For each epsilon>0 it supplies
kappa>0 such that sufficiently dense shadings of direction-separated r-tubes
have union volume at least c r^epsilon times the total unshaded tube volume.
The theorem states this using maximal convex-set density and average shading;
Remark 1.2 verifies the needed density bound for direction-separated tubes.
Fixed chart and radius constants can be absorbed by reducing the exponents.

Here is the exact reduction if that input is available. Work on the fixed
regular reference source, at phase scale r, with

    number of phase cells N_r <= C r^(-3-zeta),
    vertical cells per direction r-cell B_r <= C r^(-zeta),
    each assigned source-cell weight <= C D r^3.

Let q be one fixed scalar slope coordinate. Define H_(r,R) to be the actual
root-time set where the r-bush contains at least r^beta source mass from
neighbors satisfying |q(a')-q(a)|<=R. Put R=r^alpha, r<=R<=1. Partition q into
R-slabs; neighboring slab groups have bounded overlap. In one group, the
projected tangential tubes in R^2 x J can be colored into

    J_r <= C B_r R/r

direction-separated families, by the source's `v058` coloring construction.

A root in H_(r,R) has at least

    L_r >= c D^(-1) r^(beta-3)

target cells in its actual bush. Enlarging tangential tubes by a fixed factor
puts an entire c r-radius cross-sectional disk around that root trajectory
inside the tangential region of multiplicity at least L_r.

Write m=sum_j m_j for the tangential multiplicities by color. For a threshold
K_r=C r^(-epsilon), if L_r>=2J_r K_r, then pointwise

    m 1_{m>=L_r} <= 2 sum_j m_j 1_{m_j>K_r}.              (7)

The low-multiplicity colors together contribute at most J_r K_r. This explicit
inequality avoids assuming that a root's own color has high multiplicity.

For each color, the external dense-shading theorem implies that a sufficiently
high own-multiplicity dyadic level has at least half its incidence on shadings
of relative tube volume below r^kappa. Sum those sparse incidences and the
O(log(2/r)) levels to get

    integral m 1_{m>=L_r}
        <= C r^kappa log(2/r) N_r r^2.                  (8)

Convert this to root-time measure using the phase-cell weight bound and the
whole r^2 cross-sectional disks. Their factor is at most C D r^3/r^2=C D r.
Summing the bounded-overlap slab groups in (8) gives

    (sigma x dt)(H_(r,R))
        <= C D r^(kappa-zeta) log(2/r).                 (9)

The high-multiplicity threshold holds for sufficiently small r whenever

    alpha > beta-2+zeta+epsilon.

Choose epsilon small relative to 3-beta, then obtain kappa from the external
theorem, choose zeta<kappa also small relative to 3-beta, and finally choose
alpha between max{0,beta-2+zeta+epsilon} and 1. The source is fixed after these
choices, before taking r to zero. Equation (9) is dyadically summable.

Thus, **under the stated external input**, q-near heavy root-times can be
removed by Borel--Cantelli. The surviving full-limsup heavy events must carry
actual q-far neighbors, with |q-q'|>r^alpha. This preserves the continuum
root-time mass and uses no division by the incoming graph mass or by a rooted
completion success probability.

Independent inspection confirmed the cross-color inequality (7), the sparse
incidence sum, and the source-weight/cross-section conversion in (9). This
still does not pay the q-far part, and the external input remains unformalized.

## 7. Exact remaining continuum obligation

For the one fixed source define

    P_r(beta)=(sigma x dt)
      {(a,t):sigma(Bush(t,a,r))>=r^beta}.

The actual dimension deficit forces full dyadic limsup of these events and
hence nonsummable P_(2^-n). A bound such as

    P_r(beta)<=C r^c,       c>0,                          (10)

would contradict that premise and close this particular route. Mere
P_r(beta)->0, a finite collection of heavy times, or a sequence of shrinking
positive absolute costs does not do so. A supported Frostman construction is
an alternative; (10) is a sufficient target, not an additional assumption.

The elementary full-vector time estimate gives only

    integral_J sigma(Bush(t,a,r)) dt
       <= C r integral |a-a'|^(-1) d sigma(a') <= C D r,

so Markov bounds a heavy time fiber by C D r^(1-beta), which is vacuous in the
relevant beta>1 range. Packing/reference-cell counts and the source-only
bush cover have not improved this whole-vector bound. The original normal
window estimate supplies one scalar factor; the further conditional tangential
factor in `v078-final-coherent-factor-budget` is still an additional geometric
obligation, not a consequence of multiplying marginal probabilities.

Even if the conditional near-coordinate reduction is allowed, q-far root-time
mass remains. Its old normal phase lies within O(r^(1-alpha)) of
-(p-p')/(q-q'), but recording these many windows does not bound their total
root-weighted continuum mass. That is the precise remaining incidence/entropy
estimate after this attack. No frozen source, actual physical error, original
root measure, or final theorem has been replaced to bypass it.

### Connection to the original residual target

This sufficient target is connected to the original proof, rather than a new
final hypothesis. With the marked interval J strictly inside a buffered J+,
the already checked collision-time bridge and bounded direction density give

    integral_J integral sigma(Bush(t,a,r)) d sigma(a) dt
       <= C r Z_r^(J+) + C r^3.

The second term is the explicit near-direction/boundary-time contribution.
Consequently, if the original residual target Z_r<=C r^(2-eta) were proved,
then for 0<eta<epsilon,

    P_r(3-epsilon)<=C r^(epsilon-eta)+C r^epsilon,

which is dyadically summable. The manuscript's
`v078-final-coherent-factor-budget` (original TeX line 15141 onward) assumes
the needed conditional tangential gain;
`v081-bush-tree-edge-carleson-criterion` (line 12478 onward) assumes the
quadratic paid/cross inputs. Their conservation consequences do not separately
prove that missing quantitative input. No such input is assumed by the new
Lean recurrence theorem.
