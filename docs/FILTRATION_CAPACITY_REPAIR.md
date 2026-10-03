# Filtration density budgets and the remaining geometric capacity term

Date: 2026-10-03. This is a repair attempt for the original manuscript's
density-cocycle and small-hairbrush aggregation argument. The probability
and finite-tree calculations below have been independently checked. The
finite-capacity module has passed strict Lean compilation and axiom readback,
with the exact scope recorded below. Neither the original hypotheses nor its final theorem
are changed. The general geometric closure is still open.

## 1. A genuine filtration removes one replenishment error

Let `sigma` be a probability reference, `nu=f sigma`, `0<=f<=L`, and
`m=nu(Omega)>0`. Let `F_n` be an increasing filtration and initially take
`F_0` trivial. Define `q_n=E_sigma[f|F_n]`. For `K>1`, put

    c_K = log K - 1 + 1/K > 0.

Logarithms in the capacity budgets are natural; Section 5 explicitly uses
base-two Shannon entropy. The following is a real weighted
bound, not a claim about the product of the increasing factors on one path:

    c_K sum_n nu{q_(n+1)>=K q_n}
        <= integral f log(f/m) d sigma
        <= m log(L/m).                                      (1)

At a parent atom, write its reference-child probabilities as `alpha_i`
and `r_i=q_child/q_parent`. Then `sum alpha_i r_i=1`. The conditional
`nu`-weighted logarithmic increment is

    q_parent sum_i alpha_i phi(r_i),
    phi(r)=r log r-r+1 >= 0.

For `r>=K`, `phi(r)>=c_K r`. Summing the nonnegative relative-entropy
increments telescopes to (1). Zero parent density carries zero `nu` mass.
Finite stopped partitions give the same argument; bounded-likelihood
optional sampling and monotone convergence extend the count to increasing,
almost-surely finite stopping times. There is no assumption that their
expected time is finite.

This repairs a specific inference in the manuscript's
`lem:v081-bush-return-density-cocycle` and
`cor:v081-stopping-tail-compensation`: bounded densities alone do not bound
the product of their increasing factors. A genuine likelihood martingale
does give the stronger *expected, original-mass-weighted count* (1).
It does not make arbitrary cap densities into likelihood ratios.

### Allowing genuine deletion of original mass

The useful version permits a bounded nonnegative supermartingale `q_n`:

    0<=q_n<=L,    E_sigma[q_(n+1)|F_n]<=q_n,    q_0=m.

The surviving measure at level `n` has density `q_n` against the reference
at that level. With

    g(x)=x log(x/L)-x+L,      g(0)=L,

the function `g` is convex and decreasing on `[0,L]`. Its Bregman remainder
at a positive parent `x` is

    g(y)-g(x)-g'(x)(y-x)=x phi(y/x).

The conditional expectation of its linear term is nonnegative because
`g'(x)=log(x/L)<=0` and the process loses, rather than creates, mass.
Since `0<=g<=L`, telescoping gives

    c_K sum_n integral q_(n+1) 1_{q_(n+1)>=Kq_n} d sigma
       <= m [1+log(L/m)].                                  (2)

At a zero parent the next density is zero almost surely. Formula (2)
charges the surviving child's actual mass, not the mass of a separately
renormalized conditional success law. It applies, for example, to
`q_n=E_sigma[f_n|F_n]` when `0<=f_(n+1)<=f_n<=L`.

## 2. The exact finite geometric-tree inequality

At each node `v`, let `p_v>=0` be its actual mass and `c_v>0` its claimed
reference capacity. Assume

    q_v=p_v/c_v<=L,      sum_(w child of v) p_w<=p_v.

Define a nonnegative potential, with value zero at `p=0`, by

    Phi(p,c)=p [1+log(Lc/p)].

The local inequality is

    c_K sum_(w:q_w>=Kq_v) p_w
      <= Phi(p_v,c_v)-sum_w Phi(p_w,c_w)
         +q_v [sum_w c_w-c_v]_+.                           (3)

Here `[x]_+=max(0,x)`. Its proof identifies the missing term exactly. Put
`s=sum_w p_w/p_v<=1`, `S=sum_w c_w/c_v`, and `r_w=q_w/q_v`. For positive
parent mass,

    B=sum_w c_w q_v phi(r_w)
      =sum_w p_w log r_w+p_v(S-s),

and direct algebra gives

    Phi_v-sum_w Phi_w+q_v(sum_w c_w-c_v)
      =B+p_v(1-s)log(L/q_v)>=B.

The terms with `q_w=0` are interpreted continuously, so their contribution
to `B` is `c_w q_v`. On a growing child, its contribution is at least
`c_K p_w`. Replacing the capacity difference by its positive part proves
(3). If the parent mass is zero, mass subadditivity forces all its child
masses to vanish.

Summing over a finite rooted tree and discarding nonnegative leaf potentials
therefore gives

    c_K sum_(growing edges v->w) p_w
       <= Phi(p_root,c_root)
          +sum_(internal v) q_v [sum_w c_w-c_v]_+.           (4)

No depth or number-of-children factor is hidden. The mass-preserving case
has the sharper initial entropy `p_root log(L/q_root)` when every level
preserves total mass. The extra `p_root` in (4) safely permits arbitrary
mass deletion and terminal leaves.

If the reference atoms really form subpartitions, `sum_w c_w<=c_v`, the
last term vanishes. This is the geometric realization of (2). For moving
or repeatedly labeled caps, (4) instead displays their density-weighted
reference-capacity creation. Source-mass conservation does not imply
reference-capacity conservation.

### Sharpening to the entropy of duplicated capacity

There is a stronger version of (3)--(4). Put
`S_v=(sum_w c_w)/c_v`. Then the linear debt can be replaced by

    p_v log(max(1,S_v)).                                  (4a)

Indeed set `C=max(c_v,sum_w c_w)`, keep the actual parent mass `p_v`
unchanged, and use the reference density `p_v/C`. The child reference
capacities now sum to at most `C`. Any old `K`-gain child is also a
`K`-gain relative to this smaller reference density. Apply the
subcapacity version of (3). Its parent potential is exactly

    Phi(p_v,C)=Phi(p_v,c_v)+p_v log(C/c_v),

and the child potentials are unchanged. Summing gives

    c_K sum_(growing edges v->w) p_w
      <= Phi_root+sum_v p_v log(max(1,S_v)).                (4b)

This proof does not normalize or enlarge any actual occurrence measure.
It changes only the reference capacity used in one inequality. Thus the
remaining geometric quantity is more precisely cumulative duplicated-cap
entropy, rather than a linear count of cap overlap. Bounded overlap at
each generation alone still allows this quantity to grow linearly with
the number of generations.

## 3. A fixed geometric countertest to dropping the capacity term

Take the original source to be ordinary Lebesgue measure restricted to a
small dyadic cube `Q_0` inside the unit slope ball, with one fixed smooth selector

    b(a)=diag(1,2,3) a.

Its compact phase graph has packing dimension three. It satisfies every
positive-slack graph-cover bound. All exact reference-line hairbrushes
have source mass zero: away from the three resonant times, the equation
`(diag(1,2,3)+tI)a=b_0+t a_0` determines a rational curve in `t`; at a
resonant time its solution set has dimension at most one. The physical
front nevertheless has an open-set/Frostman escape on any positive time
interval away from these times. Thus this is a test of an intermediate
ledger inference, not a counterexample to the no-Frostman branch or the
main theorem.

Start at a node whose source and cap label are the same dyadic cube `Q`,
so its density is one. Perform two steps:

1. Divide `Q` into its 64 quarter-side cubes `Q_ij`. Label each source
   child `Q_ij` by its containing half-side cube `Q_i`. Each of the eight
   cap labels `Q_i` is used eight times. Child density is `1/8`, and the
   total child cap capacity is eight times the parent capacity.
2. At each child, keep its source unchanged but refine its cap label to
   `Q_ij` itself. Its density becomes one, an eightfold increase.

Repeat inside all the quarter-side cubes. Every step strictly halves the
cap side length. Every source partition is disjoint and exhaustive. Every
source and cap path is nested. Cap overlap is at most eight at any single
step. Nonetheless the entire original source is counted by an eightfold
density gain every second step, indefinitely.

The true source-partition likelihood ratio remains identically one. The
cap density is a different process, because its labeled capacities are
duplicated during the first step. The positive capacity term in (4) is
therefore essential even with strict shrinkage, fixed bounded overlap,
perfect original-mass conservation, and pointwise exact-hairbrush nullity.
These nodes are local physical bushes up to the fixed Lipschitz constant
of this selector; the example does not assert that the manuscript's full
non-Frostman routing algorithm selects this particular tree.
In (4b), each first step costs exactly `p_v log 8`, while the following
relabeling uses the previously created density slack. This realizes a
genuine repeated release of label information, even though no new source
mass or geometric carrier is introduced.

Requiring tight cap labels does not fix the inference. In every half cube
`Q_i`, group its eight quarter cubes into four opposite-corner pairs.
The first-step sources are these 32 pair unions; each pair has minimal
axis-aligned bounding cube `Q_i` and the same minimal enclosing-ball radius
as `Q_i` (its closure contains two opposite corners). Capacity multiplication
is four and density is `1/4`. Next split each pair into its two quarter
cubes, restoring density one while halving cap radius again. Repetition
gives the same obstruction with geometrically tight cubes or enclosing balls.
For ball-volume capacities all densities acquire the same dimensional
constant, so the fourfold growth and capacity ratios are unchanged.

## 4. Why two immediate fixes do not yet settle the geometry

### First-hit likelihood trimming

For a fixed `nu=f sigma`, first-hit atoms where `q_n<epsilon m` form an
antichain. Hence

    nu{inf_n q_n<epsilon m}<=epsilon m.

Along the remaining paths, the *original* conditional law on every
visited atom obeys `nu_Q<=L/(epsilon m) sigma_Q`. This avoids paying
separate small child masses at successive stopping times. It does not
assert the same lower-mass bound for the additionally trimmed measure
`nu|good` inside all those atoms. Nor does it bound a normalized fresh-cycle
law whose density relative to the product reference becomes singular.

For a fixed old root, `1/m` is a fixed constant before later scales are
chosen. At the original scale, however, `m` can already be a power of the
old collision thickness. Trimming improves neither that inherited
thickness nor the raw-completion normalization. The repository's existing
one-source/all-slack support construction already removes the separate
`L/H` vertical-support pruning loss in the manuscript's v057 lemma.

### Replacing caps by disjoint dyadic stopping cubes

Such cubes really do have conserved reference capacity. If one replaces a
qualifying geometric child by the entire old measure in its containing
cube, its density can only increase. But the extra source points need not
carry that child's actual physical-bush witness. If one instead retains
only its original witnessed subset, the parent density is no longer the
fixed original-measure conditional density. Reconstructing witnesses by
positive hereditary exhaustion preserves existence and old mass, but
does not by itself preserve the quantitative geometry needed for the
paid/root-scale estimate. A valid repair must prove that compatibility,
rather than identify the two densities by notation.

There is a second, quantitative failure even if all extra points can receive
some genuine witness. Starting with a witnessed sublaw `Gamma_H<=Gamma_Q`,
one needs a gain relative to the whole density `Gamma_Q(Q)/|Q|`, whereas
the original witness only supplies one relative to `Gamma_H(Q)/|Q|`.
In the tight-cap example, merging the four pair labels over `Q_i` yields
the whole source on `Q_i`, already of density one. Its quarter-cube children
also have density one, so the supposed fourfold gains disappear. Keeping
the pair marks retains their `1/4` conditional densities and restores the
capacity duplication. Even exhaustive genuine-witness aggregation therefore
does not establish a common-parent density gain; that is an additional
geometric implication, not a consequence of probability-kernel conservation.

## 5. Joint source/time filtrations still retain predictive release

In this section `H` denotes base-two Shannon entropy. Let `A` have a
probability law `sigma<=D Lebesgue` on a bounded slope patch, and let `T`
be uniform on a bounded interval `J` of positive length, independently of
`A`. Let `B=b(A)` and `X=B+TA`, and use dyadic labels

    C_n=(A_n,B_n), U_n=(A_n,T_n),
    F_n=(A_n,T_n,X_n), G_n=(T_n,X_n).

On the bounded patch, `(a,b,t)<->(a,b+ta,t)` is bi-Lipschitz. Consequently
the two joint labels `F_n` and `(C_n,T_n)` determine each other up to a
bounded number of alternatives. Their conditional entropies in either
direction are `O(1)`, not literal equality of sigma-algebras.

Writing `E_n=H(X_n|U_n)` gives `E_n=H(B_n|A_n)+O(1)`. The exact identity is

    H(X_(n+m)|U_(n+m),X_n)
      =E_(n+m)-E_n+I(U_(n+m);X_n|U_n).                     (5)

The release term agrees up to `O(1)` with the old predictive term
`I(A_(n+m);B_n|A_n)`. Appending time does not remove it. Also, if
`L_n=H(A_n|G_n)`, then exactly

    L_(n+m)-L_n
      =H(A_(n+m)|A_n,G_(n+m))-I(A_n;G_(n+m)|G_n).          (6)

The audited sparse-deletion shear `b(a)=(f(a_3),0,0)` with `T` uniform on
`[1,2)` makes the release and innovation in these ledgers both order `m`
on density-one fixed-block scales, while `E_n,L_n=O(sqrt(n))`. The
conditional observed block entropy given `F_n` is `3m+O(1)`, yet that
given only `G_n` tends to `4m`. Mixing different coarse source fibers
supplies the missing bit per scale. This is an actual packing-three
selector with a full-dimensional front, so it tests the filtration
argument without changing the source or time law.

There is a useful positive macro-block fact. The fixed all-slack compact
carrier bounds the number of occupied `F_n` atoms by
`C_epsilon 2^((4+epsilon/2)n)`. Thus the original probability of an atom
of mass below `2^(-(4+epsilon)n)` is summable in `n`. Almost every original
root eventually has, for every depth-`n+m` source/time child `u`,

    P(U_(n+m)=u | F_n)<= (D/|J|) 2^(epsilon n-4m).          (7)

This is rootwise macro-block nonconcentration, valid on the same eventual
good-atom event at genuine `F`-stopping times for the original atom-conditioned
law. It does not cover arbitrary additional branch restrictions.
For `m` comparable to `n`, it improves the former
averaged entropy bound. It gives no useful fixed-block estimate and does
not bound the physical fiber-entropy growth in (6).

## 6. Exact source interface and remaining conclusion

The original `prop:v081-bush-tree-edge-carleson-criterion` (TeX12480ff)
assumes the paid and cross-edge budgets. The subsequent occurrence
exhaustion and target/time/flag partitions preserve source marginals but
do not assert cap-capacity subadditivity. The disjoint nonterminal source
sets in the earlier stopping-tail criterion do not supply it either,
as Section 3 demonstrates.

The filtration attempt therefore gives a strict partial repair: a correct
mass-weighted replacement for the invalid positive-density-gain argument,
including deletion and an explicit geometric error term. To close the
general small-hairbrush branch, one must still either construct a
source-faithful nested reference partition compatible with the actual
geometric witnesses, or control the cumulative capacity-creation term
using additional no-Frostman geometry. The joint entropy route instead
needs a stopped physical projection estimate beyond (5)--(7). Neither
missing implication is established here.

## 7. Verification

`Theorems/Thm_StickyKakeya4_filtration_capacity_budget.lean` proves eleven
declarations, including the positive gain constant, nonnegative entropy
remainder, local growth budgets, exact parent-incidence telescoping, both
finite-tree capacity-error bounds, and the no-capacity-creation corollary.
Zero-mass nodes can be omitted; the finite-tree endpoints use positive
densities on the listed nodes and allow arbitrary actual mass deletion.

The targeted Lake build passed 1,948 jobs. Source compilation and the import
readback both passed with `-DautoImplicit=false -DwarningAsError=true`.
All eleven readbacks use only `propext`, `Classical.choice`, and `Quot.sound`.
The logs are `verification/filtration-capacity-budget-{build,strict,axioms}.log`;
the exact source hash and scope are in
`verification/filtration-capacity-checkpoint.json`.

The probability filtration extension, geometric countertest, and
joint-filtration discussion are handwritten results and audits, not extra
Lean declarations. The previously passed 185-module default-build snapshot
is unchanged; this checkpoint tests the additional independent module and
does not claim a fresh full 186-module rebuild. The main theorem's existing
Wang--Zakharov axiom dependency is unchanged.
