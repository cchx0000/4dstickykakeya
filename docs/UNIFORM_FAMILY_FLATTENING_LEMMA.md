# A finite uniform-family flattening lemma

Status: handwritten proof using the published finite Lq inverse theorem. This supplies the missing proof adaptation in FINITE_ALPHABET_EXTREMAL_FAMILY_ESCAPE.md. It is not a Lean theorem. The original-mass doubled-cell recursion below was independently checked by independent mathematical review.

## A. Inputs and conclusion

Fix dimension d, q>1, a uniformly bounded family F of probability measures, and 0<=alpha<d(q-1). Assume:

(U) For every epsilon>0, at all sufficiently fine scales m, every nu in F satisfies

    Z_q(nu,2^(-m)) <= 2^[-(alpha-epsilon)m].

(H) For some gamma>0, at all sufficiently fine scales m, every nu in F and every orthogonal hyperplane projection pi satisfy

    Z_q(pi_*nu,2^(-m)) <= 2^[-(alpha-(q-1)+gamma)m].

(T) At each parent cube Q of side 2^(-s), each nu in F admits a local positive decomposition into translated copies of family members, all at a scale comparable to 2^(-s). The copies meeting Q have weights p_j with

    sum_j p_j <= nu(2Q),

and reproduce nu on Q. The comparability and support constants are uniform. Finite or countable sums are allowed; limits of finite sums follow by monotone convergence.

Conclusion: for every sigma>0 and fixed uniform support bound for eta, there is epsilon_*>0 such that, for every sufficiently fine m, every nu in F, and every discretized probability eta within that support bound and with Z_q(eta,2^(-m))<=2^(-sigma m),

    Z_q(eta*nu,2^(-m)) <= 2^[-(alpha+epsilon_*)m].       (UF)

The only deep external input is the finite inverse theorem, Corso–Shmerkin Theorem 2.1. Its relevant output is a nearly constant-weight, uniform branching subset of nu retaining q-norm up to 2^(-delta m), with centered cells and hyperplane saturation at a positive fraction of generations whenever eta has exponentially small q-moment:

https://arxiv.org/html/2409.04608v1#S2.SS1

Everything after that finite structural output is proved below. No invariant measure, unique ergodicity, or per-member spectrum limit is assumed in this lemma.

Normalization and translation convention: the estimates and local decomposition are also used after a fixed common support normalization and for the bounded translations introduced by the inverse theorem. Condition (T) must hold for translated parent grids as well. This is harmless for the intended convolution and graph-directed families but must be explicit. Translating a grid changes its q-moment by at most a dimensional comparison constant, the hyperplane bound has the same property, and (T) simply translates the prefix offsets. A fixed common dilation changes scale by a bounded amount. Thus one may enlarge the working family by these normalized bounded translates without changing any asymptotic exponent or positive margin.

## B. Global removal from a line-saturated family

We first prove that there are positive constants theta,kappa and an integer m_0 such that, whenever a family D of 2^(-m)-cubes satisfies

    N_m(pi(union D)) <= 2^[-(1-theta)m] |D|,

one can discard at most 2^(-theta m)|D| cubes so that the q-moment on all remaining cubes is at most 2^[-(alpha+kappa)m], uniformly in nu in F.

Partition D into weight levels, with all masses in one level between w and 2w. If a level D_j has N_j cubes and q-mass E_j, projected-cell multiplicities and Holder give

    Z_q(pi_*nu,2^(-m)) >= c E_j (N_j/N_m(pi D_j))^(q-1).

If E_j >= 2^[-(alpha+u)m]/(C m), assumption (H) implies

    N_m(pi D_j) >= c N_j 2^[-m+(gamma-u)m/(q-1)]/(C m)^(1/(q-1)).

Choose u and theta much smaller than gamma/(q+1). The hypothesized small projected count of the WHOLE family then forces each such heavy level to have at most 2^(-3theta m)|D| cubes for sufficiently large m. There are O(m) relevant levels: levels below mass 2^(-Jm), for fixed large J, contribute at most 2^(dm)2^(-Jqm), which is smaller than the desired bound. Delete all heavy levels. Their total cardinality is at most 2^(-2theta m)|D|; the remaining levels and the tiny-mass tail have total q-mass at most 2^[-(alpha+u/2)m]. Shrinking theta and kappa gives the stated claim.

Constants caused by rotations, enlarged cubes, and changing scale by a bounded amount are absorbed by reducing the positive exponents and increasing m_0.

## C. Conditional removal with actual parent mass

Use (T) at a parent Q. After rescaling, apply Section B separately to every tail copy nu_j. Grid comparison gives a good child family D_j for each tail, with at most epsilon_m |D| bad children and retained tail q-mass at most 2^[-(alpha+kappa)m], where epsilon_m<=2^(-theta m).

Put p=sum_j p_j. For a child R define its bad-copy weight

    b(R)=sum_{j: R not in D_j} p_j.

Since sum_R b(R)<=epsilon_m p |D|, discard the children with b(R)>sqrt(epsilon_m)p. At most sqrt(epsilon_m)|D| children are discarded. On the retained children split the actual measure into good-copy and bad-copy parts. Convexity gives

    sum_R good(R)^q <= p^q 2^[-(alpha+kappa)m],

and, using (U) for all tails,

    sum_R bad(R)^q
      <= [sqrt(epsilon_m)p]^(q-1)
           sum_j p_j sum_R nu_j(R)^q
      <= p^q epsilon_m^((q-1)/2) 2^[-(alpha-epsilon)m].

Choose epsilon smaller than theta(q-1)/4. Both terms improve on exponent alpha by a fixed positive amount. Since p<=nu(2Q), we obtain positive theta_1,kappa_1 such that, after deleting at most 2^(-theta_1 m)|D| children,

    sum_(retained R) nu(R)^q
      <= 2^[-(alpha+kappa_1)m] nu(2Q)^q.                (C)

Without a saturation hypothesis, the same decomposition and (U) give the baseline local estimate

    sum_(R subset Q) nu(R)^q
      <= C_epsilon 2^[-(alpha-epsilon)m] nu(2Q)^q.     (B)

These arguments keep the original weights throughout. They remain valid when different copies use different members of F, so there is no independence assumption about a selected source remainder and no normalization loss from a small component weight.

## D. Doubled-cell pruning: the mass recursion

Apply the finite inverse theorem at block scale L and final depth m=SL. Its selected leaf set A is uniform in leaf masses up to a factor 2, is uniform in its branching numbers R_s, retains q-norm, and can be centered: every selected point lies in the central half of its occupied level-sL cube, for all s<S.

At a parent Q, let D be its selected children at level (s+1)L. Let D^+ consist of all same-scale neighboring cubes needed to cover each 2R, R in D. There is a dimensional constant C_d with

    D subset D^+,  |D^+|<=C_d |D|,
    N(pi D^+)<=C_d N(pi D).

Centering and sufficiently large L ensure that EVERY such neighbor lies inside the original parent Q. Thus Section C applies at Q, without enlarging the parent again.

At a saturation generation, the inverse theorem gives N(pi D)<=C_d 2^[-(1-delta)L]|D| for some pi. For delta<theta_1 and sufficiently large L, D^+ satisfies Section C's saturation condition. Apply (C) to D^+. Delete an original child R whenever its neighbor cover meets the deleted part of D^+. Bounded overlap shows that at most

    C_d^2 2^(-theta_1 L)|D|

original children are lost. This is at most |D|/2 when L is large. For the retained original children, convexity and bounded overlap give

    sum_R nu(2R)^q
      <= C_d^q sum_(retained neighbors R') nu(R')^q
      <= C 2^[-(alpha+kappa_1)L] nu(2Q)^q.             (G)

At an ordinary generation retain every original child and use (B) on D^+ instead:

    sum_R nu(2R)^q
      <= C_epsilon 2^[-(alpha-epsilon)L] nu(2Q)^q.    (O)

Now define the actual recursion quantity by

    K_s = sum_(retained occupied level-sL cubes Q) nu(2Q)^q.

It uses ORIGINAL mass, not the mass restricted to retained leaves. Equations (G) and (O) give the desired recursion for K_s exactly. The initial value is bounded by a fixed dimensional/support constant: after the inverse theorem's translation, only a bounded number of root cubes meet the support, and their doubled cubes have bounded overlap. If a single-root normalization is chosen it is at most 1, but that normalization is unnecessary. The final value K_S dominates the q-mass of the retained leaf set. There is no comparison of nu(2Q) with (nu restricted to A)(Q).

## E. Contradiction and parameter order

Write the q-spread assumption on eta as Z_q(eta)<=2^(-sigma m). The inverse theorem ensures that at least

    c_0 m/L,  with c_0 depending only on sigma,q,d,

of the generations are saturation generations, provided its parameter delta is sufficiently small. One may take any 0<c_0<min(1/2,sigma/[2d(q-1)]).

At each such generation retain at least half the children. Uniform original branching then leaves at least 2^(-S)|A| leaves. Since original leaf masses on A differ by at most 2, the retained q-mass is at least 2^(-S-q) times the q-mass on A. The inverse theorem's q-norm retention therefore gives a lower bound

    retained q-mass >= 2^[-(q delta+1/L+o(1))m] Z_q(nu).

Suppose (UF) fails with a small exponent epsilon_*. Young's inequality gives Z_q(nu)>=Z_q(eta*nu)>2^[-(alpha+epsilon_*)m]. The lower bound is consequently close to 2^(-alpha m).

On the other hand, the original-mass recursion yields

    K_S <= C^S 2^[-alpha m + epsilon m - c_0 kappa_1 m].

Choose parameters in this order: first theta_1,kappa_1 from Sections B–C; next the ORDINARY LOCAL error epsilon_loc and inverse delta much smaller than c_0 kappa_1/(q+1); next L sufficiently large for centering, neighbor deletion, the inverse theorem, all local estimates, and (log C)/L and 1/L to be negligible. The inverse theorem then supplies a positive near-convolution threshold epsilon_inv. Finally choose epsilon_* and a SEPARATE GLOBAL error epsilon_U so that epsilon_*+epsilon_U<q epsilon_inv and both are small relative to the retained exponent gain. Use (U) with epsilon_U only to trigger the near-convolution hypothesis; epsilon_loc was already fixed for the local recursion. Take the final scale m large enough for these distinct uniform bounds. This order has no parameter loop.

The upper exponent gains a fixed fraction of c_0 kappa_1, while the lower exponent loses less than that fraction, a contradiction. This proves (UF).

## F. Application boundary

The finite-alphabet compact convolution family has property (T) by truncating at a scale slightly finer than the parent cube: every tail copy meeting Q lies inside 2Q, so its complete weight is charged to nu(2Q). A finite-state graph-directed family has the same property after grouping copies by their terminal states. Thus the flattening lemma itself permits both.

The remaining step in either application is to supply the actual worst-spectrum limit and a fine-prefix stabilization comparison. For the compact convolution family, the extremal cocycle construction does this. For the finite-state family, a finite-mixture extremizer and a finite sum of prefix/tail convolution pieces are the proposed route; that separate bookkeeping must be checked before claiming the measure-sensitive finite-state conclusion.
