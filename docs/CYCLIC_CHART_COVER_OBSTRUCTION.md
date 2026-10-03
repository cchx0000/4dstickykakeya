# A packing-three cyclic graph that resists simple chart extraction

Date: 2026-10-03. Handwritten explicit countertest. It concerns chart extraction
from packing and bounded slope density ALONE, not a decomposition-or-Frostman
dichotomy under an actual front dimension deficit.

## 1. One scalar graph with two uniform marginals

Let U,V be independent random series

  U=sum_(n>=1) u_n 4^(-n),  u_n uniform on {0,1},
  V=sum_(n>=1) v_n 4^(-n),  v_n uniform on {0,2}.

Each marginal is an Ahlfors-1/2 Cantor measure. Their product is Ahlfors1.
Set A=U+V and F=U-V. The digits of A are independently uniform on {0,1,2,3},
so A is uniform Lebesgue on [0,1]. The digits of F are independently uniform
on {-2,-1,0,1}, so F is uniform on [-2/3,1/3]. Except at countably many base-4
boundary values, A uniquely determines (U,V). Thus F=f(A) for a Borel f,
up to a null set, and the compact phase carrier of (A,F) is a fixed invertible
linear image of the Cantor product: it is Ahlfors1.

Null boundary fibers may be retained in the compact carrier. A positive
compact literal graph restriction is available by Lusin; all upper covering
bounds and all concentration upper bounds below survive restriction. We do
not assert that such a restriction retains the carrier's lower Ahlfors bound.

A useful uniform estimate is, for every real c and every interval B(y,h),

  P{f(A)-cA in B(y,h)} <= C h^(1/2),  0<h<=1.          (1)

Indeed f(A)-cA=(1-c)U-(1+c)V, and max(|1-c|,|1+c|)>=1. Condition on the other
independent Cantor variable and apply its 1/2-Frostman upper bound. The
constant is uniform in c.

## 2. A genuine cyclic three-dimensional selector

Take three independent copies of A and define

  b(a_1,a_2,a_3)=(f(a_2),f(a_3),f(a_1)).

The original source is ordinary Lebesgue on [0,1]^3. Its compact phase carrier
is, after permuting coordinates, the product of the three scalar phase
carriers, hence Ahlfors3 and packing-three. The actual selector is a graph
outside a null set; a compact positive-source graph restriction can again be
used if required. No abstract entropy law is being substituted for geometry.

## 3. Approximate triangular charts in coordinate-permuted frames

Let g be a triangular Borel map in ANY fixed simultaneous permutation of the
original coordinates. Its first output coordinate depends only on its own
first slope coordinate a_j. The actual b_j is f(a_k), k!=j, an independent
uniform variable. Therefore

  volume{a: |b(a)-g(a)|<=h} <= C h.                    (2)

This holds even if the chart is retained only on an arbitrary measurable
source piece. Covering a fixed positive source mass p by M such h-charts
requires M>=c p/h. A subpower number of these charts is impossible.

A broader chart L a+g(a), with arbitrary fixed matrix L and triangular g in
a coordinate-permuted frame, still obeys

  volume{a: |b(a)-L a-g(a)|<=h} <= C h^(1/2).           (3)

Use its first output relation, condition on the other two source coordinates,
and apply (1) to the remaining f(a_k)-L_(j,k)a_k. The constant is independent
of L and g. Such chart covers need at least c p h^(-1/2) members.

These statements do not address triangularity after an arbitrary fixed
rotation, since the first transformed coordinate then mixes source variables.

## 4. Even approximate rank-one OUTPUT charts cost a power

Let L be any fixed matrix, u any vector, c any constant vector, and g ANY
scalar Borel function of all three slopes. Then

  volume{a: |b(a)-La-c-u g(a)|<=h} <= C h^(1/2).        (4)

Choose a unit covector w orthogonal to u. The left event implies
|w dot (b-La-c)|<=h. Expanding this scalar expression gives a sum of three
independent terms of the form alpha_i f(a_i)-c_i a_i, with the alpha_i a
permutation of the coordinates of w. One satisfies |alpha_i|>=1/sqrt(3).
Conditioning on the other two variables and scaling (1) bounds the event
by C h^(1/2), uniformly in L,u,c,g.

In particular no positive original source lies exactly in one such graph,
and covering a fixed mass p by M h-approximate rank-one-output charts again
requires M>=c p h^(-1/2). This remains true for any actual source restriction
because its measure is bounded above by the same original cube volume.

## Scope

The model tests proposed source-faithful chart allocations. It is not a
counterexample to the sticky Kakeya theorem and does not establish low front
dimension. No elementary proof of the whole three-feedback model's front
is asserted here. In particular a valid argument using the ACTUAL front
deficit could still yield one of these chart structures OR a Frostman escape;
only the claim that packing-three by itself supplies cheap charts is refuted.
