# Finite-time obstruction with actual horizontal Lebesgue measure

Date: 2026-10-03. Handwritten, independently reviewed research note; not Lean-certified. This records an obstruction to a proposed intermediate inference, not a proof of a continuum-time inverse theorem.

## 1. General digit lift

Fix an integer B >= 2, let D = {0,...,B-1}^3, and let f:D -> R^3 be arbitrary. Let d_1,d_2,... be independent uniform D-valued digits and set

    a = sum_{n>=1} B^{-n} d_n,
    b = sum_{n>=1} B^{-n} f(d_n).

Write mu for the law of (a,b), E for its compact support, A(a,b)=a, and P_t(a,b)=b+t a. Then A#mu is Lebesgue probability measure on [0,1]^3. Apart from the null union of B-adic coordinate hyperplanes, a has a unique digit sequence, so b is a measurable function of a.

Let C0 >= 1 be a fixed upper bound for the diameter of E. Every level-n phase cylinder has diameter at most C0 B^{-n} and mu-mass B^{-3n}. The latter assertion holds even if phase cylinders meet, since their horizontal projections are distinct B-adic cubes with pairwise disjoint interiors.

For z in E and 0<r<=1, choose a cylinder through z with n = ceil(log_B(C0/r)). It lies in B(z,r), hence

    mu(B(z,r)) >= B^{-3n} >= (r/(B C0))^3.

Conversely, horizontal domination gives

    mu(B(z,r)) <= volume_3(B(Az,r)) <= C r^3.

Thus the full phase support is 3-Ahlfors regular, with constants depending only on B and f. In particular, the usual disjoint-ball argument gives, at every pair of scales 0<rho<=R<=1,

    N_rho(E intersect B(z,R)) <= C(B,f) (R/rho)^3.

This directly audits the all-intermediate local-count requirement; it does not rely on a generic tangent theorem.

To obtain a genuinely compact single-valued graph, choose by inner regularity a compact K of Lebesgue measure at least 1/2 inside the set where all three coordinates have unique B-adic expansions. The digit map is continuous on that set, so E_K={(a,b(a)):a in K} is compact. The normalized restriction mu_K is an actual graph probability, satisfies A#mu_K <= 2 volume, has positive horizontal volume, and inherits every covering upper bound above. Lower Ahlfors regularity is not claimed for this restriction and is not needed.

For any fixed t, put Q_t = {f(d)+t d:d in D}. The projection P_t E is the self-similar digit set with base B and alphabet Q_t. Covering its level-n cylinders gives

    upper_box_dim(P_t E_K) <= upper_box_dim(P_t E)
                                <= min(3, log |Q_t| / log B).

All constants are fixed once the finite alphabet is fixed. Therefore, for every epsilon>0, these examples satisfy the normalized bounds with delta^{-epsilon} at all sufficiently small delta.

## 2. Arithmetic Kakeya configurations survive all these assumptions

Let F_k(B) be the smallest cardinality of an integer set S containing, for every d in {1,...,B}, a progression f(d)+j d, j=0,...,k-1. Use digits d in {1,...,B} instead of {0,...,B-1}; this translates the horizontal interval and leaves it Lebesgue. Apply the scalar digit lift with vertical digit f(d)/(k-1), then take its third Cartesian power.

At times t_j=j/(k-1), every projected scalar digit lies in S/(k-1). Consequently all k projections obey

    upper_box_dim(P_{t_j} E_K) <= 3 log F_k(B) / log B.

The phase set still has all-scale exponent 3 and the actual horizontal marginal still has bounded density.

Green and Ruzsa prove that, for k sufficiently large,

    lim_{B->infinity} log F_k(B)/log B <= 1-c/log log k.

Their Theorem 1.2 therefore yields simultaneous upper-box projection deficits of order 1/log log k in the present class. This is substantially stronger than the elementary periodically allocated-digit deficit 3/k. A theorem at equally spaced times forcing max_j dim(P_{t_j} E) >= 3-eta must therefore allow k at least doubly exponential in a constant multiple of 1/eta, up to the unknown absolute constant and harmless losses.

Moreover, proving such equally spaced finite-time conclusions for every eta would prove the arithmetic Kakeya conjecture: the displayed projection upper bound would force log F_k(B)/log B >= 1-eta/3. This is a precise reduction, not an assertion that the sticky Kakeya conjecture itself is equivalent to arithmetic Kakeya, nor a claim about every possible adaptively selected irrational time set.

Primary source: Green--Ruzsa, On the arithmetic Kakeya conjecture of Katz and Tao, Theorems 1.1 and 1.2 and Conjecture 1:
https://arxiv.org/html/1712.02108

A November 2025 primary source still describes the arithmetic Kakeya infimum as open and gives the best known sum-difference upper bound 1.67513...:
https://arxiv.org/html/2511.15135v1

## 3. Elementary failure of a summed-deficit budget

Let u_n,v_n be independent uniform {0,1} digits, set x=sum 4^{-n}u_n, y=sum 4^{-n}v_n, and define

    a=x+2y, b=-y.

The horizontal digit u_n+2v_n is uniform on {0,1,2,3}; hence a is uniform on [0,1]. At times 0, 1/2, 1 the scalar projections are respectively -y, x/2, x+y. Their upper-box and Hausdorff dimensions are

    1/2, 1/2, log 3/log 4.

The third equality follows from the separated base-4 digit alphabet {0,1,2}. After taking the third Cartesian power and, if desired, a compact positive-measure graph restriction, the projection dimensions are at most

    3/2, 3/2, 3 log 3/log 4.

Therefore the sum of their deficits from 3 is at least

    6 - 3 log 3/log 4 = 3.622556... > 3.

Thus even a proposed inequality sum_j (3-dim P_{t_j} E) <= 3 is false under phase Assouad dimension 3 plus horizontal Lebesgue measure. Additive collisions let losses at different times overlap; the canceled-digit budget is not universal.

## 4. What this establishes and what remains open in this investigation

These examples obstruct finite exact-full projection conclusions, simple summed-deficit arguments, and modest-size equally spaced finite-time substitutes. The independent long-block construction discussed by the other worker additionally allows Hausdorff dimension zero at any prescribed finite collection of times, but relies on different good scales for different times. The arithmetic lift above gives simultaneous upper-box deficits and so is a distinct obstruction.

None of these examples refutes the sought continuum-time low-q estimate. Indeed the arithmetic examples are coordinatewise products, for which the already established scalar-energy/Hölder argument supplies the logarithmic averaged bound for q<=4/3. I have not obtained a new general continuum-time consequence beyond that previously known model result. A repair must use the actual positive-measure time family together with source-faithful scale bookkeeping, or prove a genuinely new additive/geometric theorem; the all-intermediate phase count alone does not make the finite-time shortcut elementary.
