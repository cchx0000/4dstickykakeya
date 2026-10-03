# What a small anticipation budget does and does not control

Status: exact elementary test for the proposed general macro-block transfer. This does not refute the original sticky theorem or the stationary/driven escape results.

## A causal delayed-digit example

Use base 2 and three independent uniform bit streams D_j in {0,1}^3. Define

    A = sum_(j>=1) 2^(-j) D_j,
    b(A) = sum_(j>=1) 2^(-2j) D_j.

The intercept digits in odd positions are zero; those in position 2j equal the slope digit in position j. This is a genuine bounded Borel graph off the null binary-boundary set. Its symbolic phase prefixes have exactly 3n bits of entropy, because the first n slope digits determine all first n intercept digits. Thus the anticipation budget

    V_n = H(B_n | A_n)

is exactly zero for the symbolic digit partitions. Ordinary dyadic geometric partitions change this only by bounded boundary/carry issues, which are immaterial to V_n=o(n).

The graph has a uniform upper covering exponent 3: each depth-n slope cylinder determines all first n intercept digits, and the remaining phase diameter is O(2^(-n)); inside a depth-n cylinder there are at most 2^(3m) depth-(n+m) cylinders. A Euclidean phase ball meets only O(1) relevant depth-n horizontal cylinders, so the same local upper estimate holds geometrically.

## Linear macro dependence despite zero anticipation

Consider a block from n+1 to n+m, where 0<m<n. The intercept digits in this block copy the slope digits with indices

    floor(n/2)+1, ..., floor((n+m)/2).

Every one of these slope digits lies in the ORIGINAL coarse slope prefix A_n. Therefore the block is determined by A_n, but its unconditional entropy is

    H(B_(n,n+m]) = 3 [floor((n+m)/2)-floor(n/2)].

Consequently

    I(B_(n,n+m]; A_n) = (3/2)m + O(1).

Take geometric macro scales n_(j+1)≈(1+epsilon)n_j with 0<epsilon<1. The sum of anticipation budgets is still zero, but the sum of these coarse-prefix dependence amounts is

    sum_j I(B_(n_j,n_(j+1)]; A_(n_j))
      = (3/2)(n_last-n_first)+O(number of blocks).

It is linear in the final resolution. Hence V_n=o(n), even V_n=0, does not bound the total dependence of phase macro blocks on the actual earlier source labels. Freezing those labels or replacing them by fresh independent copies cannot be charged solely to V_n.

Qualification: in this delayed-digit example, once A_n is fixed the copied intercept block is merely a deterministic translation. That dependence is geometrically harmless for a within-block projection estimate. The example therefore refutes a naive inference of total block independence, but does not refute a conditional method that quotients translations and measures only the dependence of the CURRENT-block map shape on the coarse state.

This example is already triangular (each intercept coordinate depends only on its own slope coordinate), so its original front has dimension 4 by the completed triangular theorem. It tests the entropy-transfer premise, not the conclusion.

## Refinement after quotienting translations: current-map shape masks

The same zero-anticipation phenomenon can encode linear information in the current map SHAPE. Choose successive macro blocks (n,n+m] with m<=n. Within such a block define, coordinatewise,

    intercept_digit_(n+j) = D_j * D_(n+j),  1<=j<=m.

Here the product is the product of bits, and all mask digits D_1,...,D_m lie in the already observed coarse prefix. Define any unused initial intercept digits to be zero. Every intercept digit depends only on source digits at that or earlier positions, so V_l=0 at every depth l.

Given A_n, the relative current-block map on the 3m fresh source bits is u -> mask*u coordinatewise. Its value at the zero word is zero for every mask, so distinct masks cannot become identical by a translation. Testing one nonzero fresh bit at a time recovers every mask bit. Thus the entropy of the current-block map even modulo translations is exactly 3m. Along geometric macro blocks the sum of these shape entropies is linear in the final depth.

This remains an own-coordinate triangular graph and hence has full front dimension 4. It does not obstruct a geometrically informed conditional theorem. It does show that the entropy of the CURRENT-block map shape, as well as ordinary past-state dependence, cannot itself be bounded by the anticipation budget. Any valid transfer must exploit the actual-time geometry of these shapes rather than infer independence from V_l=o(l).

## A second failure: stationary exponent limits do not follow from V_n=0

Choose a deterministic sequence c_j in {0,1} consisting of alternating zero and one blocks whose lengths each dominate all previous lengths. Put

    b(A) = sum_(j>=1) 2^(-j) c_j D_j.

Again V_n=0 and the phase graph has upper covering exponent 3. At the fixed time t=0, the slice digit law is uniform on the active positions c_j=1. If N_1(n) counts those positions up to n, then its natural dyadic q-moment is, up to a fixed grid-comparison constant,

    Z_q(mu_0,2^(-n)) = 2^(-3(q-1)N_1(n)).

The ratio N_1(n)/n has subsequences tending to both 0 and 1, so no natural Lq exponent limit exists. An unrestricted conditional analogue of Corso–Shmerkin Proposition 3.8 cannot simply infer such a limit from an o(n) anticipation budget. This example only singles out exceptional times and does not preclude an actual-time averaged theorem with additional hypotheses.

## What remains a valid target

The geometric macro identity controlling H(A_(n+m)|C_n) by 3m-V_n is compatible with both examples. The missing estimate must retain the actual coarse state and its potentially linear information about the intercept block. A valid conditional or matrix version would need to control this state-dependent family while averaging the ORIGINAL independent time law. It cannot replace the family by one repeated convolution law, or charge all prefix dependence to the anticipation budget alone.

The new stationary and uniquely ergodic driven proofs avoid this issue because their complete independent-digit convolution identity is an actual hypothesis. In the autonomous driven case the base state evolves independently of the random digit. A digit-dependent phase-cell state is a different, branching process.
