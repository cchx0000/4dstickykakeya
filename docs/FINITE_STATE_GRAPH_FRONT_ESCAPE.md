# Finite-state graph fronts via sparse stationary loop models

Date: 2026-10-03. **Handwritten argument and independent audit.**
This is not a Lean theorem. The dimension step explicitly uses the external
Corso-Shmerkin Proposition 3.8. No original-source root-charge estimate or
hereditary positive-source-restriction theorem is asserted.

## 1. Inputs from the preceding stationary audit

The elementary all-subspace prefix proof is in the separate, unchanged note

    /tmp/SCALAR_PENCIL_PREFIX_SUBSPACE_OCCUPANCY.md

Its setting is a horizontal base-`R` grid in three dimensions, bounded output
prefixes, and the scalar pencil `output+t*input`. At almost every time, every
rank-`k` projection cell of side `R^(-43n)` contains at most `R^((3-k)n)`
source labels. This is simultaneous over `k=1,2,3`, all projection subspaces,
and all choices of orthonormal cell coordinates and translations. Its proof
uses polynomial minors at threshold `R^(-42n)` and a summable exceptional-time
bound. It does not use independence of the three output coordinates.

The scale-transfer input is Corso-Shmerkin, *Dynamical self-similarity,
Lq-dimensions and Furstenberg slicing in R^d*, Proposition 3.8, together with
the stationary-model limit existence in Lemma 1.5 / Proposition 2.12:

https://arxiv.org/html/2409.04608v1

Precisely, for a stationary model that is `q`-unsaturated on lines, the
`q`-moment of its `n`-prefix measure at any fixed exponentially finer scale,
normalized by the **original** scale index `m(n)`, has limiting decay equal
to the full measure's `Lq` spectrum. Here `m(n)=n log_2 R+O(1)`.
This proposition does not require exponential separation. It is the
external step used below, not a conclusion of elementary prefix counting.

## 2. Sparse stationary horizontal alphabets

Fix an integer `R>=2`, a nonempty alphabet

    S subset {0,...,R-1}^3,   M=|S|,

and a fixed output digit map `h:S->R^3`. Choose symbols `s_j` independently
and uniformly from `S` and define

    A = sum_(j>=1) R^(-j) s_j,
    F = sum_(j>=1) R^(-j) h(s_j),
    X_t = F+t A,   mu_t = Law(X_t).

Assume

    M >= R^(3-delta),    0 <= delta < 1.              (1)

One may take the exact deficit `delta=3-log_R M`.

**Sparse stationary conclusion.** For almost every real `t`, simultaneously
for every `q>1`, every `k=1,2,3`, and every rank-`k` orthogonal projection
`pi`,

    D_q(pi mu_t) >= k-delta.                         (2)

No independence or cyclic structure is required of the coordinates of `h`.

### 2.1 The sparse prefix count

The `M^n` words of length `n` have distinct horizontal prefixes, all lying
in the full grid `R^(-n){0,...,R^n-1}^3`. They have uniform weights `M^(-n)`.
The previous polynomial-minor proof applies to these labels with the same
constants, since their tuple count is no larger than the full-grid count.
Equivalently, extend the bounded output prefix map arbitrarily to the
missing grid points and apply that lemma.

Thus, outside one null set of times, for all sufficiently large `n` every
rank-`k` projected cell `Q` of side at most `R^(-43n)` satisfies

    (pi mu_(t,n))(Q)
       <= R^((3-k)n) M^(-n)
       <= R^(-(k-delta)n).

Here `mu_(t,n)` is the finite symbolic prefix law, with coincident outputs
retaining their combined masses. Consequently

    sum_Q (pi mu_(t,n))(Q)^q
       <= R^(-(k-delta)n(q-1)).                      (3)

All these geometric conclusions hold simultaneously over the projections
and over `q`; no union over uncountably many subspaces or exponents is used.

### 2.2 Induction on the rank using Proposition 3.8

Fix one time outside the preceding null set and one `q>1`. For any fixed
projection, the projected measure is a homogeneous stationary self-similar
measure with ratio `1/R`, hence a pleasant one-point-base model. Its Lq
spectrum has a limit by the cited stationary-model result.

For rank one, suppose that `D_q(pi mu_t)<1-delta`. In particular this
dimension is less than one, so the one-dimensional model is `q`-unsaturated
on lines: its zero-dimensional projection has dimension zero. Proposition
3.8 therefore identifies its normalized fine-prefix decay with its full
spectrum. Taking the fine dyadic scale `44 m(n)` ensures, for all large `n`,
that its cubes have side at most `R^(-43n)`, regardless of the harmless
`O(1)` rounding in `m(n)`. Formula (3) forces

    D_q(pi mu_t) >= 1-delta,

a contradiction.

Inductively, assume (2) for every projection of rank `k-1`, where `k=2` or
`k=3`, and fix a rank-`k` projection `pi`. Suppose

    D_q(pi mu_t)<k-delta.

Every hyperplane projection of this measure is a rank-`k-1` projection of
the original measure, up to an isometry. The induction hypothesis gives

    D_q(hyperplane projection of pi mu_t)+1
       >= k-delta
       > D_q(pi mu_t).

Thus the model is `q`-unsaturated on **every** hyperplane. Proposition 3.8
applies, and (3) again contradicts the assumed dimension deficit. This proves
(2). Since the only exceptional times came from the geometric prefix lemma,
the conclusion is simultaneous for all `q>1` and all subspaces, including
subspaces chosen as functions of `t`.

## 3. The sparse model has front dimension at least 4-delta

Let `I` be any nondegenerate bounded interval. Consider the symbolic front

    F_I = {(t,F(omega)+t A(omega)): t in I, omega in S^N}.

Its closure for closed `I` is compact. From (2) with `k=3`, almost every
time slice carries `mu_t` with `D_q(mu_t)>=3-delta` for every `q>1`.
This implies

    dim_H F_I >= 4-delta.                            (4)

For completeness, one can obtain (4) without hiding the parameter step
inside a slicing assertion. Fix `s<3-delta` and choose `q` sufficiently
large that `s<(3-delta)(1-1/q)`. The Lq bound implies that, at almost every
time, `mu_t` obeys a Frostman upper bound

    mu_t(B(x,r)) <= C_t r^s,   0<r<=1,

for all `x`, with some finite `C_t`. This follows by bounding each grid-cell
mass by the `q`-th root of the grid moment and using the Lq limit with a
small exponent margin; balls meet a bounded number of comparable grid
cells. The constants may be chosen measurably from countably many grid
conditions. On some positive-measure measurable subset `J subset I`, one
has a common bound `C_t<=C`. Integrating these measures against normalized
Lebesgue measure on `J` gives a spacetime measure whose radius-`r` ball mass
is at most

    (2C/Leb(J)) r^(s+1).

It is carried by the symbolic front. The Frostman principle gives dimension
at least `s+1`; let `s` increase to `3-delta`.

If we discard a coding-null collection of input sequences, the same
argument works with the unchanged push-forward probability laws and proves
the lower bound for the corresponding literal front as well.

## 4. Exact finite-state deterministic transducer setting

Fix an integer `B>=2`, a finite nonempty state set `Q`, and the full input
alphabet

    D = {0,...,B-1}^3,   d=|D|=B^3.

For each state `q` and each input digit `a in D`, there is exactly one next
state `T(q,a)` and one output digit `h(q,a) in R^3`. Let the initial state
be `q_0`. Along an input sequence `(a_j)`, define

    q_j = T(q_(j-1),a_j),
    A = sum_(j>=1) B^(-j) a_j,
    F = sum_(j>=1) B^(-j) h(q_(j-1),a_j).

All output digits are bounded because the state and input sets are finite.
Under independent uniform input digits, `A` is uniform on `[0,1]^3` and
this coding defines a Borel graph `F=f(A)` off the usual input-expansion
boundary null set. Assigning any convention on that null set gives the
literal full transducer graph.

## 5. Reachable terminal component and elementary return-loop count

The finite directed state graph reachable from `q_0` has a terminal strongly
connected component `C`: once it is entered, every transition remains in
it. Let `m=|C|` and choose a state `s in C`, reachable from `q_0` by a fixed
finite input word `u` of length `L`.

For every `v in C`, choose one path from `v` to `s` of length `ell_v<=m-1`
(take the empty path if `v=s`). Fix its input labels once and for all.

Starting at `s`, all `d^n` input words of length `n` remain in `C`. Some
state `v_n` is their endpoint for at least `d^n/m` of these words. Append
the chosen return path from `v_n` to `s`. This produces distinct return
words from `s` to itself, all of length

    N=n+ell_(v_n),

and their number is at least

    d^n/m >= c d^N,
    c = 1/(m d^(m-1)) > 0.                          (5)

The lengths `N` are unbounded because `n<=N<=n+m-1`. Thus there is an
unbounded sequence of lengths for which the set `L_N` of all length-`N`
return words to `s` obeys

    |L_N| >= c B^(3N).

No aperiodicity, mixing estimate, Perron-Frobenius theorem, or assertion
about all sufficiently large lengths is needed. The argument automatically
respects whatever return periods the component has.

## 6. Equal-length loops produce actual stationary block graphs

For one of these lengths `N`, put `R=B^N`. For a return word
`w=(a_1,...,a_N)`, define its horizontal block digit and output block digit
by

    a(w) = sum_(j=1)^N B^(N-j) a_j,
    H(w) = sum_(j=1)^N B^(N-j) h(q_(j-1),a_j),

where the states along this word start at `s`. The map `w->a(w)` is injective:
coordinatewise, finite base-`B` words are unique integer representations.
Its image

    S_N subset {0,...,R-1}^3

therefore has cardinality `|L_N|`. Define the stationary block digit map by
`H_N(a(w))=H(w)`.

Concatenate arbitrary words from `L_N`. Each word returns the state to `s`,
so its output block depends only on that block's input word. Consequently
the resulting graph coding is **exactly** the stationary model

    A_loop = sum_(r>=1) R^(-r) a(w_r),
    F_loop = sum_(r>=1) R^(-r) H(w_r).

Choosing loop words independently and uniformly gives the sparse model of
Section 2, with exact deficit

    delta_N = 3-log_R |L_N|.

Since `|L_N|<=R^3` and (5) holds,

    0<=delta_N<=-log(c)/(N log B) -> 0.              (6)

In particular `delta_N<1` for all sufficiently large selected lengths.

### 6.1 Literal graph containment and expansion boundaries

For such a length, `|S_N|>R^2`. In any one horizontal coordinate, no single
digit can have probability greater than `R^2/|S_N|<1`, because there are at
most `R^2` alphabet elements with that coordinate fixed. The scalar
coordinate law has no atoms: the probability of any prescribed infinite
digit string is zero, and any point has at most two base-`R` expansions.

Thus the loop probability law gives zero mass to all horizontal expansion
boundary hyperplanes. After discarding these coding sequences, grouping
into base-`R` blocks agrees with the unique base-`B` expansion of the input.
Every remaining phase point is on the actual transducer graph starting
at `s`. The sparse-model front lower bound survives this null removal.

### 6.2 Prefixing the route from the original initial state

Let `A_u` and `F_u` be the finite horizontal and output prefixes along the
fixed word `u` from `q_0` to `s`. Prefixing any loop input gives exactly

    A = A_u+B^(-L) A_loop,
    F = F_u+B^(-L) F_loop.

At the front level this is the map

    (t,x) -> (t, F_u+t A_u+B^(-L)x).                 (7)

It is an invertible affine transformation of spacetime, hence bi-Lipschitz
and dimension-preserving. Its image of the nonboundary loop front lies in
the actual full transducer front from `q_0`.

## 7. Proven full-front conclusion and its exact scope

By Sections 2-3 and (7), the full transducer front over any nondegenerate
bounded time interval contains subsets of Hausdorff dimension at least
`4-delta_N`. Taking the unbounded sequence of lengths in (6) gives

    dim_H(full transducer front) = 4.

The upper bound is just the ambient spacetime dimension.

The same conclusion holds for the front generated by any closed phase
carrier of the **full original uniform-input law**. Indeed, the coding map
from the full input shift to phase space is continuous, the uniform
Bernoulli input law gives positive mass to every cylinder, and its support
is the entire full symbolic phase attractor. A closed set carrying that
whole law contains this support, including the loop submodels. Likewise,
a closed spacetime carrier of the full time/input law contains its full
symbolic spacetime support. Compact carriers are special cases of these
closed-carrier statements.

**Not proved: preservation of arbitrary positive source restrictions.**
The constructed loop Bernoulli laws generally have zero mass for the
original uniform source. If `|L_N|<R^3`, the original probability of staying
inside these loop blocks for `j` consecutive blocks is

    (|L_N|/R^3)^j -> 0.

A positive-measure input set `E` can exclude a countable family of such
proper loop Cantor sets, even without losing original measure. Therefore
this proof does not establish the same dimension bound for the literal
front restricted to an arbitrary positive-measure `E`, nor for an arbitrary
compact carrier of a law merely absolutely continuous with respect to
Lebesgue measure on such an `E`. A density point alone does not put an
entire one of these singular stationary subsets inside `E`.

In particular, no original-mass Frostman allocation, original root-charge
identity, or manuscript-wide final theorem follows from this extraction.
A hereditary or measure-sensitive extension needs an additional argument
that genuinely retains the specified source restriction.
