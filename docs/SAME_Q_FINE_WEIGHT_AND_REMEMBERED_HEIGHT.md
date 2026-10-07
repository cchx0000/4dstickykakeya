# One coarse source retaining fine-pair weight and original heights

Mathematical audit, October6,2026. The argument below has been checked
independently against the existing source constructors and finite selection
lemmas. Its new source assembly is being implemented; this note does not
claim a completed Lean proof of that assembly or of the final theorem.

## The source quantity that must survive

Let r be the fixed native reference thickness, epsilon the existing
configured mesh, and G the actual deduplicated configured pair set of the
same third source. Let d=8rho be the ABSOLUTE coarse thickness produced
after planar Lemma5.3. Only rho>=epsilon/8 is guaranteed, so every inverse
fiber cap needing a radius at least epsilon is applied at d, not rho.

The weight on an occupied original d-phase parent q is

    W(q) = number of currently retained fine configured pairs in q.

It is not the coarse shading volume. Direction thinning and native pruning
must preserve this weight on the SAME final parent set Q. Two independently
selected sets, one retaining fine pairs and the other being native, would
not supply the next construction.

The baseline density reader is source-derived. Sparse admission at the
matched baseline gives actual shading volume at least epsilon^(5eB/16).
Selected-Q rows are a sub-sum of the full-shadow rows of the same incidence
set. The exact cell volume is (epsilon/2)^4, and the matched comparison is
shadow.card<=5^4*G.card. Thus

    |G| >= (16/5^4) epsilon^(-4+5eB/16).

The configured physical-height image Z has |Z|<=18/epsilon. It is
identified with the old translated-height labels only on an actual frozen
baseline satisfying Hsingle. No ambient backbone count replaces |G|.

## Arbitrary weights are permitted by the actual selection tools

NativeCoarseDirectionThinning.exists_dense_direction_thinning accepts any
nonnegative parent weights. Use shading=W and tube=1. Original HB occupied
phase populations and direction packing give a color with

    W_color >= r^p W_total / Ccol,    Ccol=23328*512^3.

NativeCoarsePruningBudget.weighted_pruning_power_budget also accepts any
weight, subject to a uniform upper bound U. It is not restricted to volume
weights. Removing parents preserves their already established direction
separation and original representative labels.

Put Cf=130^3*5832*66^3. The actual fixed-old-height inverse cap and the
height bound give

    U = 18 Cf r^(-p) d^3 epsilon^(-4).

For a pruning target exponent 8z, the deletion ledger is at most

    Cprune (b+1) r^(8z-2p) epsilon^(-4),
    Cprune=746496*18Cf*64^3,

because d=64/2^b cancels the parent-count factor (2^b)^3. This is a
finite additive ledger on the actual weight W.

Assume p<=z and epsilon^4 W_total>=r^z. If Ccol*r^z<=1, the chosen
color has weight at least r^(3z)epsilon^(-4). A cutoff enforcing
2Cprune(b+1)r^(3z)<=1 makes pruning remove at most half that color.
Consequently the SAME final Q retains

    W_Q >= r^p W_total/(2Ccol),
    W_Q >= (1/2)r^(3z)epsilon^(-4),

and has every terminal occupied-ancestor lower population required with
exponent8z.

## Actual shading of this same Q

For an absolute d-cell and its d-tube parent, the actual shadow displacement
confines old configured heights to an interval of length4d. The epsilon/8
height lattice therefore gives at most34d/epsilon heights. At each old
height, the fine-pair inverse cap is Cf*r^(-p)*(d/epsilon)^3. Hence

    |G_Q| <= 34Cf*r^(-p)*(d/epsilon)^4 * |coarsePairs_Q|.

This is proved by a union of actual inverse-image sets. It does not assume
that the later shadow point is a single-valued function of a deduplicated
fine pair; several original antecedents may yield different shadow cells.
The genuine shading-cell volume (d/2)^4 now gives

    shading(C_Q) >= r^p*epsilon^4*W_Q/(544Cf).

If1088Cf*r^z<=1, this is at least r^(5z). The direction-separated Q,
its terminal pruning law, and this actual shading lower bound are exactly
the geometric inputs to NativeCoarseNativeAdmissibility.native_input.
That theorem derives upper AD from direction packing, lower AD from the
same pruning, and CW from original HB and actual shading mass. No new
IsNative(C_Q) hypothesis is introduced.

## Effective exponent and the pre-source order

Use the existing effective threshold

    z=(eA/16)*log(d)/log(r).

Then r^z=d^(eA/16), r^(8z)=d^(eA/2), and r^(5z)=d^(5eA/16).
For the fixed permitted output window d<=r^window, one has the fixed
lower bound z>=zMin=window*eA/16>0.

Every preceding coefficient cutoff is uniform for z>=zMin. The number
b+1 is bounded by the reference dyadic depth plus1. The existing logarithmic
cutoff at3zMin pays the pruning ledger; a constant cutoff atzMin pays
Ccol,1088Cf,densityCost,cwCost and10077696. Taking etaRef<=zMin pays the
CW exponent. These choices occur before D and before the output d is known.

The following single-output scalar calculation was an initial proposed
input-weight payment. Its inequalities are valid when its exponents can
be chosen independently. The actual baseline hierarchy does not give
that independence; see the18:17 correction below. It is not a completed
original-source parameter choice.
Write gamma=5eB/16 and bound the old/Q3/menu taxes by r^(-lambda).
Strong retention is at least8^(-zeta53)d^zeta53/N. Since epsilon>=r,

    epsilon^4 W_total >= c*8^(-zeta53)
                         *d^[zeta53+(gamma+lambda)/window].

Choose zeta53<eA/64 BEFORE the planar output chi. After chi and the
resulting fixed window are known, choose eB<=window*eA/40 and
lambda<=window*eA/128. The displayed exponent is then less than eA/32;
a source cutoff absorbs the fixed coefficient and yields

    epsilon^4 W_total >= d^(eA/16)=r^z.

There is no zeta53/chi payment. Replacing strong ratio retention by its
weaker old-mesh bound would destroy this useful order.

### Actual baseline hierarchy: unresolved full parameter join at18:17 UTC

The baseline window may be amin/8=c^3/64, while its quotient cost has an
exponent comparable to c. Paying that baseline cost after converting
everything to the reference r would ask for eB much smaller than c^3,
while the baseline cost requires c much smaller than eB. Those two
requests cannot be treated as an available parameter choice. The older
single-output recipe above therefore does not close the actual caller.

A sharper candidate keeps the baseline volume and menu losses at their
native epsilon scale. Before absorption its normalized graph lower is

    [16/(625*N*Q3^4)] * (sigma/32768)^zeta53 * epsilon^(5eB/16).

The actual5.3 gap gives sigma<=epsilon^(chi/2), after paying its fixed
32768 coefficient in the original-source cutoff. A menu bound
N<=epsilon^(-menuTax) and the raw third-core allowance give total
epsilon-tax5eB/16+2c3/window+menuTax. In the candidate original hierarchy
c3=eta0*c^3/32 and window=c^3/64, so2c3/window=4eta0. This avoids paying
eB/window and can allow the order chi, then eB, then c, then eta0.

This is still an actual-field audit in progress. In particular the
reference-native exponent, old parent-profile exponent, raw third-core
allowance, and the initial baseline retention factor must all come from
the SAME source with that parameter order. Separate valid choices for
these exponents are not a proof of simultaneous compatibility. The
already certified local same-Q and cutoff theorems remain valid on
their stated inputs; the complete source-budget caller is not claimed.

## Choosing the original parent

After the globally native Q has been obtained, use the original HB menu
to choose a massive OLD w-parent of the retained fine G, where
w=tau/4096. The total old w-parent menu is at most

    (373248*64^3)*r^(-profile)*w^(-3).

The exact C-parent readback keeps the direction label and divides every
old intercept integer by512. Thus an old parent determines an actual
C-parent. Keep that C-parent's entire backbone, while shading only with
the selected old-parent incidences. This uses the globally established
native C as reference and does not assert that a source already confined
to one parent was globally native.

The inverse label count is at most512^3, but it is unnecessary to pay that
factor merely to rediscover an old subparent: choose the old parent first.
The bound never asserts a population ratio for an arbitrary chosen old
parent inside its larger C-parent.

At one actual old height, the old full phase includes BOTH slope and
intercept. The literal phase-depth offset is +9. Actual phase gaps and
configured graph residuals bound quotient Y-distance by148w. Including
the planar rho-ball uncertainty requires148w+2rho<tau, which follows
from8rho<=w and tau=4096w. Thus a genuine original planar anchor applies;
no larger substitute tau-ball or higher-field Lipschitz assumption is used.

## Remember the genuine higher-plane height through the local source

For the intended NativeLocalParentSource, the relative thickness is

    sigma=d/w=32768rho/tau.

This is its literal thickness. A different PaddedRescalingCubicalSource
would have additional fixed scale factors and must not be substituted
without updating the time-bin map and output scale.

Carry the actual original-edge relation to triples

    (old configured height h, FINAL local tube/cell pair j).

A fixed h,j has fine-pair preimage in one absolute d-parent, so the same
fixed-height cap applies. It is not necessary to pay the full local
175616N fiber bound and its time factor again.

The local constructor's final time bin pulls back to an interval of
length256sigma in the input coarse-cell-center time. The old-height/shadow
displacement is at most2d. Thus its possible old h lie in an interval of
length256sigma+4d<=260sigma. The epsilon/8 lattice gives at most
2082sigma/epsilon heights;4096sigma/epsilon is a convenient upper bound.
Here sigma>=epsilon follows from d>=epsilon and w<=1.

If the massive old parent has |G_w|>=a*w^3*epsilon^(-4), the relation gives

    |(h,j)| >= (a/Cf)*r^p*sigma^(-3)*epsilon^(-1).

Choose the largest h-fiber in EACH LITERAL FINAL time bin. After choosing
one h, forgetting h is injective because j includes that final bin. Hence

    |finalPairs| >= a*r^p/(4096Cf)*sigma^(-4),
    actual shading >= a*r^p/(65536Cf).

This uses one retained-mass factor. The older method multiplying separate
height-count and per-height-richness bounds spends that factor twice, and
those two lower bounds do not automatically survive an intervening padding
selection. The direct remembered-height relation avoids that assertion.

The old-height tag is the one determining the genuine higher plane. An
already coarsened input grid-time label does not recover it. The existing
shifted-height theorem alone cannot erase this distinction.

## Remaining formal and mathematical scope

### Two output scales: corrected parameter order

The preceding single-output calculation is not sufficient to pay the later
relative scale. Write r for the original reference thickness, d for the
absolute intermediate mesh, and sigma=d/w for the final relative mesh.
The actual range is 0<r<=d<=sigma<1 and sigma<=r^window, with window>0
fixed before the source. The implementation defines

    exponent(x,y,e) = (e/16) * log(y)/log(x).

For a fixed final tolerance E>0 use

    z1   = exponent(r,sigma,E/256),
    etaA = exponent(d,sigma,E/16),
    z2   = exponent(d,sigma,E).

The exact identities are

    r^(8z1)=sigma^(E/512),   r^(5z1)=sigma^(5E/4096),
    d^etaA=sigma^(E/256),    d^z2=sigma^(E/16),
    etaA=z2/16,             d^(2z2-etaA)=sigma^(31E/256).

Thus the first selected Q's terminal populations supply the next actual
profile, and its mass bound supplies the next source mass bound. Both
comparisons go in the required direction for sigma<=1. The fixed lower
bounds are z1>=window*E/4096 and z2>=window*E/16. A cutoff for the two
actual outputs pulls back to one cutoff in r, chosen before D. It is not
legitimate to choose a new cutoff after substituting the variable etaA.

The first planar fraction must consequently be kept as
(sigma/32768)^zeta53 divided by its finite menu cost. Choose
zeta53<E/16384 before the planar output window is known. The fixed factor
32768^zeta53 is paid in the pre-source cutoff. Original-source
profile, retention, and menu exponents are then chosen sufficiently small
after that window, without changing zeta53 or its resulting window.

The former fixed-minimum-profile admission interface asks too much at the
second stage. Its fixed eta bound served to deduce source mass; here actual
mass is already available. The new explicit-mass selection retains the
same original R,E and retention factor, and the new actual-profile caller
uses the actual z2 after the output is known. The fixed positive minimum
still determines all cutoffs. As of17:24 UTC the cutoff and explicit-mass
selection have passed strict source compilation; the combined independent
axiom readback is running. The actual-profile caller is an unchecked draft.

### Actual current-parent profile and fine-weight distinction

The first globally native source D_A has line intercepts contracted by512.
At height0 its literal parent label is the original parent label with each
intercept index divided by512. It is not the original label itself.
For ell<=b-6, every occupied D_A parent contains one entire old ancestor
fiber of Q. Its cardinality is therefore at least

    r^(8z1) * (2^b/2^ell)^3.

Since d=64/2^b and d^z2<=r^(8z1), this exceeds the lower population needed
by the actual local-source AD/CW readers. The upper follows from the
native parent count with fixed coefficient5832 and its small-power
payment. Neither conclusion needs a population ratio for an arbitrarily
chosen old component inside the current parent.

At the same time, the mother graph at the baseline fine mesh epsilon must
continue to carry its original fine tube indices. Coarsening those indices
to d deduplicates graph pairs. A d-scale native volume bound yields only a
d^(-4) count and cannot replace the epsilon^(-4) fine-weight retention.
The same-Q source restriction and exact fine-weight readback are being
implemented with separate fine index b0 and coarse ancestor index b<=b0.

### Status of the genuine fine-weight-to-shading bridge

The finite argument uses a chosen original occurrence for each fine pair,
and maps that occurrence to its actual coarse shadow cell. This is a
relation: the coarse shadow must not be asserted to be a canonical
function of a fine pair unless that is separately proved. For one shadow
cell, its old configured heights occupy an interval of length at most4d.
The original epsilon/8 lattice gives at most34d/epsilon heights. Each
fixed-height fiber is bounded by Cf*r^(-p)*(d/epsilon)^3. Consequently

    |Gfine(TQ)| <= 34Cf*r^(-p)*(d/epsilon)^4*|shadow(TQ)|.

The literal coarse cell volume is (d/2)^4, giving exactly the denominator
544Cf in the same-Q shading bridge. This proof must be connected to the
actual source rows and incidences of TQ; an assumed scalar bridge does not
complete that connection. Its formal implementation is still pending.

At17:25 UTC, independent batch1721 passed all20 declarations of
NativeFineWeightedCoarseCore, NativeFineWeightedCoarseCutoff, and
NativeMassReferenceCoarseSelection. Their separate source compilations
were strict, every frozen declaration received an imported-axiom readback,
and only the standard foundational axioms were reported. The complete
actual first planar source chain had already passed batch1653.

The remaining actual source maps, fine-weight-to-shading relation, and
current-parent/native assembly still require their own checks. The
verified same-Q theorem includes that geometric bridge as an explicit
premise and is not being presented as its derivation.

These density conclusions do not by themselves prove multiplicity
preservation, dense higher-grain populations after the selected subsets,
or all-radius AD on the new current configuration. Those are separate
remaining parts of the original kappa=0 proof. The original final theorem
has not been completed by this audit.

### Source readbacks certified at17:59 UTC

Independent batch1755 has passed the actual same-Q source restriction,
fine graph, and shadow mass readers. The retained graph keeps its baseline
tube indices b0 while the selected parent uses b<=b0. Both relevant sums
are now exact on the same TQ: the fine weights sum to |Gfine(TQ)|, and the
original coarse shading weights sum to the literal shadow image count
times (d/2)^4. This does not yet prove the inverse-fiber capacity estimate;
that separate source proof is being checked through its direct dependencies.

The same batch certifies NativeRememberedHeightGeometry: the exact local
cell-height formula gives an inverse input-center interval of length256sigma;
the actual 2d shadow-center error gives an old configured-height interval
of length260sigma; the original midpoint lattice bounds its occupied
heights by4096sigma/epsilon. No actual time is replaced by a coarse label.

### Next near-extremal-volume argument, not yet formally completed

After one original height has been chosen in each final time bin, the
unchanged full reference slice stored in HasThirdXYData still has its
all-radius AD bounds with exponent3-kappa. Its lower bound may be used
for a separated covering of that full reference set; no lower bound is
claimed for its later Y/Q subset. The old w-phase footprint localizes the
selected witnesses, and the resulting d-cover has size at most a fixed
multiple of KXY^2*(w/d)^(3-kappa). The actual physical-map and cell-halo
readbacks should transfer that covering to the final cells. With O(1/sigma)
final time bins this gives the candidate union-volume upper
fixed*KXY^2*sigma^kappa.

The literal occurrence-to-shadow-to-localPair map and its halo counting
are still under implementation. In particular an intermediate pair may
have several original antecedents of different heights. The selected
occurrence relation supplies a good antecedent for each retained output;
it does not assert that all antecedents of a forgotten pair have the same
height. The proposed volume bound is not yet a certified replacement for
the remaining multiplicity/near-extremal input.

### Actual same-Q source construction certified at19:24 UTC

Independent batch1920 strictly reads back
NativeActualFineWeightedSourceSelection.exists_same_Q_source, together with
its actual matched-shadow source, output and mass readers. Every reported
axiom is one of propext, Classical.choice and Quot.sound; the source and
artifact hashes are unchanged. The literal configured cell volume is
(epsilon/2)^4.

The public same-Q construction derives the fine-level reference populations
from the original HB, derives both the per-parent fine-weight capacity and
the fine-weight-to-original-shading inequality, and then selects one Q.
It returns the actual native coarse source, its terminal ancestor
populations, shading lower bound and retained BASELINE fine graph on that
same Q. The former hU, hbridge and Hfine interfaces are no longer input
assumptions of this source-facing theorem.

The actual configured-point separation, normalized total fine-graph mass
and scalar parameter payments remain explicit. The pending epsilon-native
factory must derive them from its same final third relation, and the
remembered-height volume construction remains pending. This result does
not itself assert the original kappa=0 theorem.

### Actual higher-chart bound and consumer scope at19:26 UTC

The literal Lemma5.3 planar near-graph currently supplies absolute slope
at most1. Its installed normalization uses translation, dilation and
coordinate permutation; it does not justify replacing that slope bound
by1/4. Keep the actual slope theta. For lower coefficients |A|,|B|<=1/4,
the corrected higher coefficients C=B-theta*A and F=theta satisfy
|C|<=1/2 and |F|<=1. These are sufficient for the existing
NestedPlaneQuantization.quantized_movement_bounded theorem, whose
coefficientCost_le_five premise is only |A|,|C|,|F|<=1. No angle selection
or change of the original source is required for that consumer.

The encoded quotient AD theorem itself has no matrix-norm premise; its
source-specific support reader and any later stronger chart predicate
must still be checked with the actual higher field. No smaller higher
chart norm or higher-field Lipschitz estimate has been inferred here.

The original paper also uses the unit entry bound: on p65 immediately
before Definition17.2, Mat(k,l) consists of matrices with entries in
[-1,1], and Definition17.4(1) uses that Mat for the higher field. This
confirms the bound appropriate to the actual configuration predicate.
Paper reference: https://arxiv.org/pdf/2609.22035#page=65.

### Remembered-source geometry certified at20:26 UTC

Fresh independent batch2025 passed all36 declarations of
native_remembered_source_construction, plus the actual paid-planar and
final-third total-mass suppliers. All source and artifact hashes were
unchanged and all reported axioms were foundational.

The checked occurrence map retains a selected original witness before
forgetting antecedents. Its actual old-height count, tagged fine-graph
fiber estimate, and one-height-per-final-time selection compose with the
original full-slice AD cover to prove the literal union upper
unionConstant(KXY)*sigma^kappa. The constant is
129^4*257^4*9^3*13^6*KXY^2*36^(3-kappa). Neither an output point-count
upper nor a selected-subset AD lower is assumed by rank_two_union.

The actual final-third supplier also derives its planar witnesses,
baseline admission payment and whole-Y graph retention from the same
raw budget, final HT and newCutCharge. It returns the exact normalized
fine-graph total and existing epsilon separation after that Y choice.
The original-source front end still has to instantiate that record and
all scalar parameters in one checked call.

Next, the simultaneous remembered-source constructor must choose its
old phase and selected occurrence relation and discharge the shading
lower on the same S bounded by rank_two_union. The fixed-S Reference
producer, source-level higher-Y halo cover and the genuine Eq143 lower
population transfer remain under verification/assembly. No kappa=0 or
final dimension-four claim follows from this checkpoint alone.
