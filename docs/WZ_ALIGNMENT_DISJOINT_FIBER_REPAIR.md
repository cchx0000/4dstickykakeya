# A disjoint-fiber repair of the projection step in WZ Lemma 5.3

Handwritten mathematical audit, 2026-10-03. Source: Wang--Zakharov,
arXiv:2609.22035, Section 4 and Lemmas 5.2--5.3, pp. 19--25.

## Result and scope

There is a constructive replacement for the preparation on p. 23 which makes
the point projection injective, while retaining the tube upper profiles,
point AD bounds, and anchored fiber AD bounds needed on p. 24. It uses a
greedy disjoint decomposition, not an assertion that a dense set of pairs has
a dense point projection. The construction below proves that preparatory
statement. It does not by itself audit all of the subsequent transverse
AD/product construction or the final patching of local boxes in Lemma 5.3.

Constants below depend only on ambient dimension unless indicated. Fixed
constant tube dilations and the equivalence of covering numbers and separated
point counts change these constants only. All spatial cells are cells of ONE
fixed ambient dyadic grid.

Let A be delta-separated and (delta,t,C_A)-AD regular, C_A=delta^{-eta}, in a
bounded box. Let epsilon>0 be a small fixed parameter. There are scales
rho<=tau with R=tau/rho>=delta^{-chi(epsilon)}, a source set E_0 subset A,
and disjoint sets F_j subset E_0, each in a C rho by C tau tube of direction
theta_j, such that:

1. Sum_j |F_j| >= |A| / O_epsilon(log(1/delta)^2).
2. For every rho<=u<=v<=tau and every u by v tube T,
   |E_0 intersect T|_u <= R^epsilon (v/u)^s, initially with s>=0.
3. Every F_j has size between
   lambda delta^kappa (rho/delta)^t R^s and
   C C_A (rho/delta)^t R^s.
4. For every dyadic r in [rho,tau],
   |F_j|_r <= R^epsilon (tau/r)^s.
5. Every point a in their union has ONE assigned direction theta_j.

Here lambda^{-1}=O(C_A^3 log(1/delta)), kappa>0 is any chosen sufficiently
small fixed number, and chi(epsilon)>0 is explicit. The factor in item 1
also depends on kappa. One may take kappa=epsilon chi(epsilon).

After one same-set self-uniform refinement, including the fixed partitions
specified below, one obtains B subset union F_j with |B|>=delta^{o(1)}|A|
and simultaneously:

* B is t-AD regular with loss delta^{-O(eta)} R^{O(epsilon)};
* every nonempty B intersect F_j is s-AD regular between rho and tau, with
  loss R^{O(epsilon)+(kappa+O(eta))/chi(epsilon)};
* all retained points remain assigned to their ORIGINAL fiber F_j, so every
  anchor is in its own regular fiber;
* the usual finite collection of geometric configuration uniformity
  relations can be imposed in this SAME refinement;
* the inherited tube upper bounds hold for B automatically.

Here o(1) is for fixed epsilon, eta, kappa, and fixed-depth working radii.
With the existing coarse self-uniform theorem, choose its Q as a small
power of delta^{-1}; its retention factor is then a constant depending on
the fixed parameters, and its uniformity loss is delta^{-O(eta)}. No
self-uniform call on all O(log(1/delta)) scales is needed.

The exponent s can be clipped to [0,min(t,1)] at the cost of adding
O(eta/chi)+o(1) to the R-loss. Thus these losses can all be made as small as
required by choosing epsilon first, kappa=epsilon chi, eta sufficiently
small afterwards, and then delta sufficiently small.

## 1. Extremal COVER profiles, rather than cardinal profiles

For nonempty E subset A and dyadic rho<=tau, set

  M_{rho,tau}(E) = max_T |E intersect T|_rho,

over rho by tau tubes. This maximum exists: its possible values form a
nonempty bounded set of positive integers. Pure geometry gives

  1 <= M_{rho,tau}(E) <= C_d tau/rho.

Start with (rho_0,tau_0)=(delta,1), R_i=tau_i/rho_i, and
s_i=log(M_{rho_i,tau_i}(E))/log(R_i). If some nested pair (rho',tau')
satisfies

  M_{rho',tau'}(E) >= R_i^epsilon (tau'/rho')^{s_i},

pass to it. Then s_{i+1}>=s_i+epsilon and

  R_{i+1} >= C_d^{-1} R_i^epsilon,

because s_i>=0. For 0<epsilon<1/2, iteration gives

  R_i >= C_d^{-2} delta^{-epsilon^i}.

Let L=ceil(2/epsilon). For sufficiently small delta, all ratios in the first
L possible steps are large, hence all s_i<3/2; but L increments of epsilon
would give s_L>=2. Therefore the process stops before L steps. One may take
chi(epsilon)=epsilon^L/2 after decreasing delta_0.

At the stopping pair, all nested dyadic u,v satisfy item 2. Nondyadic radii
follow by bounded dyadic enlargement, with harmless constants. The case
rho'=tau' cannot be a successor once R_i^epsilon>C_d, so the logarithmic
definition never encounters a zero denominator.

This argument needs no uniformity of E. That is the useful difference from
the cardinal profile in Lemma 5.2.

Since E subset A, original AD regularity also implies

  M_{rho,tau}(E) <= C_d C_A^2 (tau/rho)^t.

Consequently s<=min(t,1)+O(eta/chi)+o(1), justifying the later clipping.

## 2. Dynamic spatial pruning has a GLOBAL deletion budget

Let N=1+log_2(1/delta). Original AD regularity gives

  #D_r(A) <= C_d C_A^2 r^{-t},
  |A| >= C_A^{-1} delta^{-t},

for dyadic r in [delta,1]. The first estimate follows from a maximal
r-separated set and lower AD mass in disjoint comparable balls; it does
not assert that every occupied original dyadic cell has large population.

Choose lambda=(100 C_d C_A^3 N)^{-1}, with C_d large enough. Whenever a
current residual E has an occupied dyadic r-cell q satisfying

  |E intersect q| < lambda (r/delta)^t,

delete every current point of q. Repeat until no such cell remains.

This pruning can be run again after EVERY tube extraction. Its total cost
over the entire algorithm is still at most |A|/100: a fixed spatial cell
can be deleted at most once, because points are never added back. Summing
the deletion threshold over all original occupied cells and all scales
gives

  total discarded <= C_d lambda C_A^2 N delta^{-t}
                  <= C_d lambda C_A^3 N |A|.

This global charging argument is essential. It is not a fresh loss charged
once per extraction or once per epoch.

After pruning, every occupied current rho-cell contains at least
lambda(rho/delta)^t ORIGINAL points. Original AD gives the matching upper
bound C_d C_A(rho/delta)^t.

## 3. Greedy epochs and disjoint whole-cell extraction

Begin with E=A and run spatial pruning. If E is nonempty, start an epoch
with E_0=E. Apply the cover-profile stopping argument to E_0 and freeze its
rho,tau,s. Let M_0=R^s.

As long as M_{rho,tau}(E)>=delta^kappa M_0:

* choose a maximizing rho by tau tube T;
* let Q be the collection D_rho(E intersect T);
* extract F = union_{q in Q}(E intersect q);
* remove F from E, and rerun dynamic spatial pruning.

End the epoch once its selected profile has fallen below delta^kappa M_0,
or once E is empty. If E remains nonempty, start a new epoch from it.
Every extraction removes a nonempty set, so the finite algorithm terminates.

All extracted F are disjoint as sets of original points. Within an epoch,
their rho-cells are disjoint too: extraction removes the ENTIRE current
population of every selected rho-cell, and no point ever returns.

The population bounds of Section 2 give item 3. A selected rho-cell lies
within O_d(rho) of T, so the entire F lies in a C_d rho by C_d tau tube.

There is also an exact useful grid observation. For any dyadic r>=rho,

  D_r(F) = D_r(E intersect T).

Indeed, every selected rho-cell is contained in its unique r-ancestor, and
that ancestor already contains a witness point of E intersect T. Thus
whole-cell expansion creates NO extra r-ancestors. Since T is contained in
an r by tau tube, item 2 for the fixed E_0 gives item 4.

There are O(N^2) possible dyadic scale pairs. Every completed epoch lowers
its selected monotone profile by a factor delta^kappa. For a fixed pair,
this can happen at most O(1+1/kappa) times before its integer value falls
below one, because initially M<=C_d/delta. Profiles never increase as E
shrinks. Thus the TOTAL number of epochs is O_kappa(N^2).

At least 99|A|/100 points were extracted, because the total pruning budget
was at most |A|/100. Some epoch therefore extracted
|A|/O_kappa(N^2) points. Select that epoch. Its ONE initial E_0 supplies
the SAME upper profile for every one of its fibers. It is unnecessary to
freeze a complete binned profile vector; freezing one selected profile
until its specified drop gives the same polynomial epoch bound.

## 4. One-pair-per-point configuration

For a in F_j put x_a=(a,theta_j), where theta_j is the direction of its
source tube, and set X={x_a}. The F_j are disjoint, so the projection
X -> union F_j is a bijection. In particular, for EVERY subset X' subset X,

  |P[X']| = |X'|.

Choose one of finitely many slope charts by the total mass of its fibers;
this loses only a dimensional constant and does not cut fibers internally.
Rotate that chart into the configuration coordinates if necessary.
One can use the coordinate in which the direction has maximal absolute
component, so only finitely many coordinate permutations/sign changes are
needed. Retain the ORIGINAL spatial partitions (or their pullbacks under
this chart map). Do not silently replace them by an unrelated rotated grid
when invoking the exact ancestor equality of Section 3.

The source fiber labels remain actual fixed labels, even when two tubes
are geometrically close. Their number J satisfies

  J <= |X| / [lambda delta^kappa (rho/delta)^t R^s].

Every source fiber fits in O_d(1) configuration rectangles of dimensions
(C tau,C rho,rho/tau). Hence any cardinality-retaining refinement also
retains the concentration at this scale up to the existing small losses:
cover X by O_d(J) such rectangles and average |X'| over them.
The upper concentration is at most
C_d C_A(rho/delta)^t R^s, by the fixed source tube profile.

## 5. Fixed partitions restore BOTH lower bounds on the SAME set

Use the proved same-set uniform refinement with all desired geometric
relations AND these fixed partition relations:

(a) ambient spatial cells at fixed-depth working radii r in [delta,1];
(b) pairs (source fiber j, ambient spatial r-cell), at fixed-depth working
    radii r in [rho,tau].

Let K be its degree comparability factor and c_ref its cardinal retention
factor. For ANY fixed partition pi, every retained occupied class has

  |X' intersect pi^{-1}(pi(x))| >= |X'| / [K #pi(X)].

For (a), #pi(X)<=#D_r(A)<=C_d C_A^2 r^{-t}. Since
|X'|>=c_ref |A|/O_kappa(N^2), every retained spatial r-cell contains at
least

  [c_ref/(O_kappa(N^2) K C_A^3)] (r/delta)^t

points. These are counts of the SAME final point set B=P[X'], since
projection is injective. Upper counts are inherited from A. Choosing a
small working cell containing a point and lying in its prescribed ball
gives point AD lower bounds.

For (b), item 4 implies

  #pi_r(X) <= J R^epsilon (tau/r)^s.

Use |X|>=J lambda delta^kappa(rho/delta)^t R^s and
|X'|>=c_ref|X|. Every occupied retained fiber-r-cell therefore has at least

  c_ref lambda delta^kappa K^{-1} R^{-epsilon}
  (rho/delta)^t (r/rho)^s

points. An original rho-cell has at most
C_d C_A(rho/delta)^t points. Dividing gives the lower rho-cover count

  [c_ref lambda delta^kappa/(C_d C_A K)] R^{-epsilon}(r/rho)^s.

The small working cell containing any retained point lies in a comparable
ball around it and is in that SAME original fiber. Thus this is an
anchored lower bound at EVERY retained point of EVERY nonempty retained
fiber. The upper local bound follows from item 2, since the fiber lies in
a constant dilation of its source rho by tau tube. Constant dilations are
covered by a bounded number of tubes of admissible dimensions.

For fixed-depth working radii, take consecutive fiber radii with ratios
at most R^beta, beta<<epsilon. Interpolation loses at most R^{O_d(beta)}.
For ambient radii, use a fixed depth with consecutive ratios at most
delta^{beta'}, choosing beta'<<chi(epsilon)epsilon/d. Its loss is also
R^{O(epsilon)}. Include rho, tau and all direction-pigeonhole working
radii separately if needed. The total number of relations depends only
on the chosen parameters, not on delta.

This addresses the previously missing shared-scale and shared-final-set
quantifiers: source upper bounds come from one E_0; each fiber has one
fixed label; every final lower count is obtained in the same single
refinement; and the point projection is injective throughout.

An additional useful property is that the assigned direction theta_j is
exactly constant on each final B intersect F_j. Therefore, if a coarse
direction is selected in a parent box Q and one retained point of F_j has
that angular label, EVERY child box met by F_j intersect B intersect Q
has that same label. This avoids a second implicit witness-retention step
when the later proof selects its set J of child boxes.

## 5a. Budget relative to the FINAL scale ratio

The later directional pigeonhole step uses m consecutive intervals and
changes the scale ratio from R to R_new=R^{1/m}. Its final density target
is R^{-zeta/m}, not R^{-zeta}. A safe hierarchy is:

* m>=C_d/zeta;
* epsilon<<zeta/m;
* chi_profile=epsilon^{ceil(2/epsilon)}/2;
* kappa=epsilon chi_profile;
* eta<<epsilon chi_profile;
* fiber working-radii interpolation exponent beta<<epsilon;
* ambient working-radii interpolation exponent beta'<<epsilon chi_profile/d.

All preparation losses are then R^{O_d(epsilon)}, which can be made much
smaller than R^{zeta/m}. Polylogarithmic epoch losses and fixed-parameter
cardinality losses from self-uniformity are absorbed by taking delta small.
The final separation exponent may be weakened to the positive constant
chi_safe=chi_profile/m. There is no need to match the paper's particular
displayed formula for chi(zeta).

## 6. Standalone correction of the displayed (34)

Independently, total tube population plus (33) do not by themselves prove
the pointwise lower bound at every original point. The weaker conclusion
that the tube CONTAINS a regular subset has a direct pruning proof.

If S is rho-separated in a tau-tube, |S|>=a R^s, has local upper counts
C(r/rho)^s, and global r-cover counts <=D(tau/r)^s, iteratively delete any
occupied dyadic r-cell with fewer than

  mu(r/rho)^s,  mu=a/[2 C_d D(1+log_2 R)],

remaining points. Each cell is charged once. The total loss is at most
|S|/2, and every point of the final set has the desired local lower bound.
This alone need not retain an arbitrarily specified anchor. The
fixed-partition construction in Section 5 DOES retain and regularize every
surviving anchor, which is what the alignment argument actually needs.

## Audit conclusions

Section 4 of WZ contains no hidden convention converting pair density to
point density. The proposed replacement avoids needing one. It requires
only finite greedy choices, the original AD input, the elementary tube
cover bound, the proved same-set uniform refinement with fixed partitions,
and explicit threshold charges. It adds no projected-density certificate
and no alignment hypothesis.

No repository file has been edited and no Lean theorem is claimed from
this handwritten audit. The remaining work is to implement these finite
constructions and independently audit the transverse AD/product and local
patching steps after the corrected preparation.
