# Why autonomous finite-alphabet sequences cannot be replaced by all adapted controllers

Status: exact elementary countertest to a simultaneous-family extension. It does not contradict the almost-every-time theorem for a fixed source, and every graph constructed below has a four-dimensional front.

## 1. One fixed finite alphabet implements every focus time in a bounded interval

Fix B>=2 and a bounded interval J of target times. For a chosen t_0 in J use scalar digits d_n in {0,...,B-1}. Start with carry e_0=0. With a fixed measurable nearest-integer convention, define

    g_e(d) = -round(B e+t_0 d),
    e_n = B e_(n-1)+t_0 d_n+g_(e_(n-1))(d_n).

Then e_n lies in [-1/2,1/2] (with the appropriate half-open endpoint convention). At every step the entire map d -> g_e(d) is selected from the already known carry, BEFORE the next fresh digit is drawn.

Let T=max_(t in J)|t|. Since |B e+t_0 d|<=B/2+T(B-1), the integers g_e(d) all lie in a fixed finite set depending only on B,J. Hence all possible functions d -> g_e(d), for ALL e and ALL t_0 in J, belong to one finite alphabet. There is no alphabet growth with the target time or depth.

Write

    A_N=sum_(n=1)^N B^(-n)d_n,
    F_N=sum_(n=1)^N B^(-n)g_(e_(n-1))(d_n).

Multiplying the carry identity by B^(-n) and summing gives exactly

    F_N=B^(-N)e_N-e_0-t_0 A_N.

The carries are bounded, so with e_0=0 the infinite intercept is

    F(A)=-t_0 A.

Apply this construction independently in three coordinates. The horizontal source is exactly Lebesgue on the slope cube; the intercept graph is the smooth affine graph b(a)=-t_0 a. At actual time t=t_0, the entire spatial source collapses to the origin.

Therefore no full-measure time set can simultaneously give full-dimensional slices for ALL adapted controllers taking values in this one finite digit-map alphabet: for each t in J there is a controller focusing exactly at t.

## 2. Infinite state is real, but translations alone are not the issue

For irrational t_0, the reachable scalar carries are centered fractional parts of t_0 k for integers 0<=k<B^n. Thus infinitely many, indeed densely varying, carries occur. The construction is not a finite-state transducer merely because the output digit alphabet is finite.

There is a sharper qualification. Starting with arbitrary carry e gives the infinite tail identity

    F_e(A)=-e-t_0 A.

For a FIXED controller t_0, all carry-tail laws have the same shape modulo translation. Thus quotienting translations correctly removes the irrelevant carry complexity. It does not rescue a theorem over the closure of ALL controllers: those normalized shapes still range over the continuum of affine slopes -t_0.

The original actual-time quantifier is essential. For each fixed t_0, only one actual time is bad, and the full front has dimension 4. A proof cannot replace one fixed source/controller by a family selected AFTER observing t and still retain the same good-time conclusion.

## 3. Related obstruction for a continuous autonomous alphabet

If the autonomous digit-map alphabet itself contains all maps g_t(d)=-t d for t in J, the same obstruction is already present without adaptive control. The constant sequence at g_t has an invariant Dirac measure on the full shift and collapses at time t. Hence a common almost-every-time assertion for ALL invariant measures of that full shift is false.

Even the orbit closure of one deterministic sequence can contain all these constant sequences: concatenate increasingly long constant blocks at target times dense in J. This topological fact alone does not make that fixed sequence's slices deficient. Deficit at resolution B^(-n) would require approximation of a focus time at an exponentially fine rate relative to the relevant block length. Passing to arbitrary weak or topological invariant limits discards that time/scale rate.

## 4. Exact boundary of the current positive results

- A fixed stationary full-grid digit map: proved at handwritten level using Corso–Shmerkin Proposition 3.8.
- An autonomous uniquely ergodic driven map: same, including every prescribed base point.
- An arbitrary autonomous sequence from a fixed finite map alphabet: proved by the audited uniform-family adaptation using the finite inverse theorem.
- A fixed finite-state branching transducer: the source-retaining uniform-family argument has passed independent handwritten audit.
- The family of all adapted controllers over a finite map alphabet: the simultaneous-time assertion is false by the construction above.

Nothing here supplies a counterexample to the original sticky theorem. The purpose is to prevent an illicit enlargement of the family over which an extremal argument is taken: the original time law must remain independent of the chosen source/controller.
