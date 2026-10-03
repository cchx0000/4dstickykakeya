# Current milestones: original-paper standard

The final target is unchanged: Definition 1.1 / Theorem 1.2 of the original
manuscript, namely Hausdorff dimension four for the unit front of a compact valid
full-direction marked family with packing-dimension-three unmarked carrier.
No new regularity, routing certificate, or energy bound is a final hypothesis.
See [ORIGINAL_PAPER_TARGETS.md](ORIGINAL_PAPER_TARGETS.md) for exact references.
The earlier eight-item proposal is preserved in `PROVE2ME_TARGETS.md`.

## 2026-10-03 filtration repair checkpoint

A strict finite-tree density budget now replaces the invalid inference
from bounded cap density to a bounded product of increasing factors.
It permits deletion of actual mass and controls the total mass of
`K`-fold density-growth edges by an initial entropy potential plus
`sum p_parent log(max(1, sum child_capacities / parent_capacity))`.
For genuine nested reference subpartitions the latter term vanishes.
All eleven declarations are strictly compiled with standard-only axiom
readbacks. See [the filtration repair](docs/FILTRATION_CAPACITY_REPAIR.md).

The existing geometric source partitions do not establish reference-capacity
conservation. A fixed smooth packing-three example realizes indefinitely
repeated growth through strictly shrinking, overlapping cap labels. Thus
the general small-hairbrush charge still requires a bound on that cumulative
duplication term or a source-faithful geometric partition that removes it.
This is a partial repair, not a completed main theorem.

The subsequent capacity-envelope construction is strictly stronger:
`R_v=max(c_v,sum R_child)` constructs the least conserved reference capacity.
If its distortion is at most `B`, actual `K`-density gains are controlled
by the filtration bound at threshold `K/B`, for `K>B`. This avoids summing
local overlap entropy at every generation. Ten new declarations are strictly
checked; the tight-cap cycling test has `B=4` even though its cumulative
positive local entropy is unbounded. The actual geometric envelope bound
is still missing. See
[the witness-pooling analysis](docs/CAPACITY_ENVELOPE_AND_WITNESS_POOLING.md).

A new original-data endpoint now constructs the needed **whole-parent
physical** heavy-bush families: one source is fixed before all coefficients
and cutoffs, finite disjoint families retain any threshold below full mass,
and every piece has its own source mass greater than `A p R^beta`, with
`p` the initial parent mass. This removes the initial graph-retention factor
from that source-only restart. Nine declarations are strictly checked.
The conversion of physical radius `R` into a useful single direction-cap
radius is still open; no inherited old-edge error is improved by this result.
See [the precise restart](docs/WHOLE_PARENT_HEAVY_BUSH_RESTART.md).

The restart now uses one common actual time chosen before all coefficients,
radius cutoffs, and retention thresholds. Compact-front slicing supplies
arbitrarily cheap finite covers for almost every actual time; at any good
time, the same maximal-family construction works for every positive remainder.
Thirteen new declarations are strictly checked. This canonizes the witness
time while leaving the physical-to-angular radius step open. See
[the common-time result](docs/COMMON_TIME_HEAVY_FAMILIES.md). The separate
[relative-projection audit](docs/RELATIVE_PROJECTION_FILTRATION_AUDIT.md)
proves an elementary predictable-plane bound by hand, but finds no justified
inverse statement deriving the needed predictable geometry from the original
hypotheses. It adds no assumption or axiom to the final target.

The finite incidence regularization now constructs actual nested sets
`C subset B subset A`, retaining at least a fixed profile-count fraction of
the original cardinality or positive integer weight. Every root in C sees
local B-counts within the prescribed factor of every other root in B, for
all listed neighborhood types. Eleven declarations are strictly checked.
This avoids independently normalized local laws, but supplies neither a
large common density nor the missing angular contraction. See
[the constructed uniform core](docs/UNIFORM_INCIDENCE_CORE.md).

The renewed two-time attack has precise constraints: two fixed projections
can both have Hausdorff dimension zero while the original phase carrier is
Ahlfors three-dimensional, and relative heavy children may occur beyond every
fixed power of an already chosen parent radius. The full actual front in
that test still has dimension four. The continuum annular bound is
`C D T^2 r`; converting it to a heavy-time bound retains the inverse actual
cap density. These tests isolate missing implications without refuting the
full original hypotheses. Their detailed handwritten audits are linked from
README; no failed inference has been added as a theorem or axiom.

A new positive special case is fully closed: arbitrary Borel triangular
intercepts on a bounded-density (possibly coupled) source have actual
front-supported Frostman measures at every exponent `1+3s`, `0<s<1`, and
therefore front dimension four. The same original source/time law is cut
only by scalar reference-potential bounds; product structure is used for
an upper reference bound, not assumed for the actual source. All 31 theorem
declarations and the final no-certificate caller are strictly checked. See
[the triangular escape](docs/TRIANGULAR_BOREL_FROSTMAN_ESCAPE.md).
The general source is not proved triangularizable. The canonical-input
one-channel extension `c+L a+u f(a1)` is now checked, including arbitrary
linear coupling and the derived rational original-time window. The arbitrary
input `v dot a` is also now formalized: positive bounded localization, an
explicit basis, exact determinant density, and original-front transport are
derived internally from a finite positive bounded-Lebesgue source. These
29 further proved declarations remove all basis/support certificates. The
external osculating-projection interface remains separately scoped. No
one-channel representation has been extracted from the general datum.

The original-weight estimate for this triangular special class is now
proved as well. For every `0<beta<3`, the actual unmodified source/time law
of `r^beta`-heavy roots is bounded by `C r^epsilon` at small radii, with
`epsilon=(3-beta)/12` available, and its dyadic sum is finite. The public
endpoint derives all potential, energy, and cutoff-threshold facts from
source density and Borel triangularity. These 44 new strict readbacks do
not assume the requested charge. They also do not extract triangularity
from the general datum. See [the direct charge](docs/DIRECT_HEAVY_ROOT_CHARGE.md).

The original root moment now also satisfies `integral Z_r^theta <=
C r^(3s theta)` for all radii, `0<s<1`, and `0<theta<1/3`. The proof
saturates the cutoff threshold and integrates its cubic-root tail; it
derives all potential and energy inputs. Together with the native-time
rank-one endpoint, this adds 57 standard-only checked declarations. See
[the moment](docs/TRIANGULAR_ORIGINAL_ROOT_MOMENT.md) and
[the one-channel theorem](docs/RANK_ONE_NATIVE_TIME_ESCAPE.md).

The new digit-model research supplies a broader handwritten escape for
stationary coupled full-grid graphs, a uniquely ergodic independently driven
version, and a finite-state FULL-front support consequence. The precise
external dependency is Corso--Shmerkin Proposition 3.8; these results are
not counted as Lean completion or as a representation of the general
original selector. The finite-state loop argument does not preserve an
arbitrary positive original-source restriction. The elementary polynomial
small-value bound used in their geometric prefix analysis is separately
strictly proved in Lean (four declarations). See
[the stationary proof](docs/STATIONARY_GRID_GRAPH_PROJECTION_ESCAPE.md),
[all-subspace counting](docs/SCALAR_PENCIL_PREFIX_SUBSPACE_OCCUPANCY.md),
and [the exact scope of finite-state loops](docs/FINITE_STATE_GRAPH_FRONT_ESCAPE.md).

A later handwritten proof strengthens the digit result to arbitrary
autonomous sequences in a fixed finite alphabet and to the actual laws of
finite-state full-input transducers. The source-retaining finite-state
argument supersedes the loop-only proof's positive-subset limitation in
that exact class. It keeps every component weight to the q-th power and
uses original doubled-cell masses in the pruning recursion. The finite
inverse theorem remains an explicit external input, not a Lean axiom.
The [precise general-source boundary](docs/ADAPTIVE_FINITE_ALPHABET_FOCUS_BOUNDARY.md)
and [audited proof](docs/FINITE_STATE_MEASURE_PROJECTION_ESCAPE.md) do not
assert that original packing3 supplies few conditional phase-tail shapes.
The general main theorem is still incomplete.

The finite-volume route now has nine new constructive local modules:
weighted self-uniformity on the same retained set, real and mesh-preserving
cyclic padding, exact independent predecessor fibers with labelled grain
weights, heavy-bin transfer, its actual global shear/per-tube counting
inputs, and the combined physical multiplicity transfer. The four original-front finite-input constructors have fresh
standard-only readbacks, so dense native input is already available without
the final volume axiom. There are 138 new checked proofs and four additional
input checks in this checkpoint. The combined metric closure, matched
extremal multiplicities and actual transverse rich-layer construction are
still open; see [the exact scope](docs/WZ_LOCAL_GEOMETRY_PROGRESS.md).
This route would prove the auxiliary finite estimate rather than assume it;
it does not assert a hereditary old-occurrence cap charge.

The next finite geometric checkpoint constructs rich predecessor layers
with original weights, all-stage compatible good-tuple choices, and a
single final refinement that has both incidence uniformity and grain
richness. It additionally proves literal padded cube witnesses and the
native graph-to-marked-line normalization. All 75 new proofs are strictly
checked, with no project axiom. These remove local construction premises;
the geometric profile/menu callers, complete native AD rescaling and
Step 6 slice/quotient estimates remain. See
[the exact new scope](docs/WZ_COMPATIBLE_GRAINS_CHECKPOINT.md).

The next checkpoint constructs native padded cubical sources on the full
original backbone and derives injective slice quantization, fractional
quotient AD transfer with nearby rich cells, and arbitrary-real-exponent
metric AD coarsening. Actual two-tube path counts are also proved. All 153
new declarations pass strict standard-only readbacks; the full 234-module
build passes. These remove local construction premises, while complete
aligned-slice geometry, admissible rescaling assembly and the final volume
proof remain open. See [the exact scope](docs/WZ_STEP6_GEOMETRIC_CALLERS.md).

The alignment preparation now has actual finite constructors for disjoint
epochs and globally charged pruning, exact whole-cell ancestor images,
fractional fiber/quotient estimates, geometric spine overlap and periodic
patch isolation. All 88 new proofs are strictly checked; the complete
240-module default build passes. The [combined handwritten repair](docs/WZ_LEMMA53_COMPLETE_PATCH_ADAPTER.md)
is established at the mathematical level, while its complete Lean caller,
slab/rank reconstruction and global volume proof remain unfinished.
[Exact formal scope](docs/WZ_ALIGNMENT_CONSTRUCTORS.md).

## 1. Exact collision identity

Existing theorem compiled in the pinned environment. It is the algebraic input
for the original residual-content route. The quantitative collision-time fiber
bound and its Tonelli integration are
now strictly compiled and axiom-checked; they retain explicit near-direction
and time-window terms.

## 2. Contact/Maslov incidence

Existing matrix-pencil/Maslov incidence theorem compiled. Actual rooted C4
witnesses now preserve the whole inherited old occurrence and give four
distinct vertices under diffuse/zero-diagonal hypotheses. Genuine
nondegenerate contact cycles have checked original-time clustering and
scalar-plane error `O_M(r_0/Delta^2)`. Mesoscopic nondegenerate-or-paid/Frostman
availability remains unproved; these inputs do not yet construct the complete
mass-preserving geometric routing.

## 3. Borel selector and compact ambient front

Original Proposition 3.1 gives a Borel selector inside the compact datum.
The existing reduction is compiled and has standard-only axiom readback.
The new actual-slope construction instead pulls the selector through normalized
`(a,1)`, restricts ordinary slope Lebesgue measure to a positive marked-center
bin, and derives a common front slab of length `3/8`. The source is finite,
nonzero, dominated by Lebesgue measure, and has slopes bounded by one. Its
physical pushforward is supported literally on the original compact front.
The stronger Borel-selector-only target is explicitly archived in
`verification/ARCHIVED_TARGETS.md`; it is not assumed as an axiom.

## 4. Original source measure and residual content

The general weighted residual-content function and its measurability are
checked, retaining collision-time windows, inverse-secant weights, and the
nonzero-secant cutoff. The actual selector supplies a proved bounded-density slope source and
measurable intercept. The geometric power bound for its weighted residual
content remains open. Existing shaded sources do not automatically supply it.

The original packing hypothesis now constructs one fixed positive reference
source before any residual graph: literal `volume|B`, original carrier map,
pointwise common slab, occupied lower-mass nets, and uniform vertical counts
`A tau^(-zeta)`. Live subfamilies preserve the upper support counts for every
later subset. No later graph-mass denominator is used, and no lower mass for
arbitrary descendants is asserted. See
[the reference-source guide](docs/PACKING_REFERENCE_SOURCE.md). The same original
source now supplies every positive literal angular-shell graph and a genuine
localized dense block, with derived cubic normalized density cost
`O(tau^(-zeta))`; no cover or proximity certificate is assumed in that
original-data endpoint. The actual affine rescaling now preserves
collision times, scales residuals exactly, constructs the normalized source
probability with derived density, and preserves the normalized directed
graph mass and product domination. From the original sticky datum and
strict front dimension deficit alone, these constructions now give arbitrarily
fine directed physical graphs with mass at least `r^(2-eta/4)`, actual
probability-source density at most `r^(-eta/8)`, and a fixed bounded chart.
The original front deficit persists on each fixed affine image. The geometric
contradiction from that actual seed remains unproved.

This is now strengthened to one reference source for **every** positive
slack: the new exact-critical compact-piece construction and simultaneous
weighted pruning select one literal `volume|B` and one net sequence before
`zeta` is chosen. The original-data endpoint derives upper box dimension at
most three, all positive-slack occupied masses, and subpower vertical counts
on that same source. The 19 new declarations have standard-only readbacks;
no normalized-descendant density or root-weighted charge is inferred.

The strict front deficit now also forces a stronger recurrent input on one
fixed original source. For some `0 < beta < 3`, almost every original
source/time pair has a physical `2r` bush heavier than every fixed
`C r^beta` at arbitrarily small dyadic radii. The sum of the actual
source-times-Lebesgue-time measures of these heavy events diverges. Both
conclusions are derived from the actual front dimension deficit, not assumed
as a slicing or density input. The final endpoint constructs the positive
source and its common slab from the original sticky datum. Eleven strict
standard-only readbacks certify `rooted_heavy_limsup`; this new module has a
dedicated dependency-aware build and the full 177-module default build.

## 5. Finite occurrence-flow conservation

The scalar forest ledger is compiled. The new measure-valued ledger is compiled
and has standard-only axiom readback. Nodewise equality of measures implies the
terminal root-measure budget and its preservation under a fixed endpoint map.
This is an actual proved implication. Constructing the original geometric
routing forest satisfying the required paid/cross bounds remains open.
A genuine finite first-stage source route is now constructed: time averaging
and maximal disjoint bush extraction capture at least half the original
ordered graph mass, in at most `4 L/(r M)` physical `2r` source bushes. Its
source-only restrictions retain every original target and have exact
complement bookkeeping; geometric payment of those moving bushes is separate. Its original-data composition now constructs this route
from `IsStickyDatum` and a strict front deficit, retaining superquadratic
root mass with power-controlled source pieces and family count. A further actual
finite source resolution leaves any prescribed relative tail theta, with
explicit count and source-mass floors and exact kept-plus-tail conservation.

## 6. Source-faithful routing and terminal / paid / cross budgets

Original §§8–9 restrict ordered marked edge occurrences, not arbitrary tube
shadings. The new global terminal theorem is compiled and axiom-checked:

- disjoint occurrence restrictions preserve one root endpoint budget
- varying terminal caps imply a global near-diagonal direction band
- root product domination and original direction density give `8 C m T^3`
- `T^3 <= m q` gives `8 C m^2 q`
- a single global reversal allowance changes 8 to 16

The integrated forest theorem derives that terminal budget from nodewise
conservation. Checked Markov-kernel lemmas now derive inherited endpoint
preservation and density-root domination for actual probability-label
extensions and disjoint fractional restrictions. The actual old-neighbor
conditional law and degree-density disintegration are now constructed with
standard-Borel kernels. A checked fixed-angle guardrail shows that shrinking
terminal caps alone leaves all unpaid root mass in the cross-cap complement.
A checked physical separated-time bush theorem now pays all old targets,
not only same-cap targets. A packet-free version is now proved directly from
affine-line tube covers, with the explicit quadratic bound
`81 C ((R+r_0)/g)^2 sigma(univ)`. Fresh independent genuine flags also have checked
measure-valued separation/retention bounds while inherited labels stay intact.
Positive-event conditional kernels now preserve the full old occurrence on
the positive-success base. Positive hereditary source cuts admit exact
countable exhaustion and arbitrary finite-tail truncation without a uniform
retained fraction. A qualitative two-stage reversal lemma now derives the
whole-support cap from actual pair domination, retains a finite majority of
selector support, and excludes a second excessive support-growth reversal.
These are constructed measure operations; actual geometric
success and quantitative paid/cross estimates remain separate.
Their global geometric use still requires the designated-flag comparison and
root-weighted summation/termination, as explained in the two new research notes.
Still open: the actual geometric routing kernels and cuts, their conservation
and root/support invariants, stopping schedule, and paid/cross-cap bounds.
The finite-index probability and weighted growth/star split are now proved;
actual common-target kernels now sample whole original occurrences from
aggregate disintegration. Their inherited half/quarter mass bounds and distinct
physical sources are proved; post-cut fresh marginals are only dominated.
Genuine submeasure exhaustion avoids unnecessary rare-event normalization.
A further finite separated route is now constructed directly from the actual
front dimension deficit: it preserves all old measures and observables and
has proved fractional weights at most `8 R_i/(v-u)`. The actual cover-functional bound is now integrated from this constructor
and the packet-free geometry, with no routing certificate among its inputs.
Its global quadratic payment remains open. No missing
bound is replaced by a hidden capacity field.

## 7. Relative residual / Frostman alternative

Follow Corollary 9.31 and the residual-content criterion, rather than requiring
the false arbitrary-shading universal estimate. Conditional finite-scale
Frostman implications already in the repository do not prove their missing
inputs. The concrete residual collision-time bridge is checked, including its explicit
near-direction error. The small-secant mass is now bounded cubically from an
actual slope measure dominated by three-dimensional Lebesgue measure. A
residual power bound of exponent `2 - η` consequently gives averaged collision
sublevels of exponent `3 - η` and finite averaged transverse `t`-energy for
`0 < t < 3 - η`. These new analytical implications are strictly checked.
The actual supported source is now constructed. A direct spacetime collision
estimate supplies one extra power of radius and finite physical E4 energy;
bounded-potential restriction supplies a supported Frostman probability. The
resulting original residual criterion now proves `dimH(unitFront ambient)=4`
from the literal residual bounds on that constructed source. A further genuine geometric escape is now checked: uniformly positive
individual shrinking bushes force full front dimension. This does not assume
a fixed mass in each member of a merely positive-total-mass family. Failure of front Frostman now implies exact-collision product nullity and
qualitative decay of both the fixed-angle graph and full inverse-secant
weighted residual content, by genuine nondegenerate C4s, exact-bush escape,
and finite inverse-secant energy. Conversely, a strict front dimension deficit
now supplies arbitrarily fine violations of every finite residual power
coefficient on the same positive source, rather than assuming an excessive
fine graph. The geometric residual power rate itself remains
open. No slicing axiom or assumed
measurable Frostman kernel is used. The full vector-family escape is now also
checked from original normalized open-cap condition (340), including genuine
compactness and exact support. Obtaining that synchronized vector bound or
routing its failure remains geometric work. A further checked geometric
exit derives actual front Frostman bounds directly from subpower covering of
one fixed centered-intercept image. This premise is not known for the general
remaining source branch and is not added to the final theorem.

The line-hairbrush branch is now closed by a separate checked geometric
argument, without a common contact time. A positive source with
`b(a)=c-tau(a)(a-v0)` almost everywhere has an actual supported dimension-four
escape for any measurable `tau`. Restricting the original source/time law
away from each source's own focus yields finite energies below four; the
inverse-distance tube bound is derived, not assumed. Its contrapositive now
gives exact-null for **every** reference line under front deficit, and compact
reference families have uniform qualitative maximum-row decay. The original-
data endpoint constructs its fixed source and common slab before the compact
reference family and collision window are selected.

These five modules add 60 standard-only readbacks. They do not convert
qualitative decay into a power rate or aggregate individually vanishing
hairbrushes. The smooth flat-selector stress test in
[the moving-focus guide](docs/MOVING_FOCUS_LOW_MOMENT_ESCAPE.md#10-uniform-qualitative-decay-does-not-supply-a-power-rate)
shows why that numerical inference needs an additional argument. The test
has a full-dimensional front and is not a counterexample under the actual
front-deficit hypothesis.

## 8. Original compact marked closure and axiom audit

Use Theorem 9.32's intended residual/Frostman closure and transfer the conclusion
to the original compact front. The current legacy route still uses
`wang_zakharov_published_volume_estimate`. Repairing its API calls and compiling
it does not complete the requested internal proof.

Completion requires both an unchanged final theorem statement and transitive
kernel readback with no project-specific axioms or `sorryAx`. The latest full
default build passed all **185** project modules and **8,894** Lake jobs,
including the line-hairbrush escape, simultaneous all-slack reference source,
rooted recurrence, and all physical bush-cover modules;
there are now **961** checked new declarations with only standard logical
axioms or no axioms. The actual residual-cycle adapter derives all four contact
errors on actual marked lines and preserves the inherited root time. The
latest final readback still reports the preexisting WZ project axiom in the
two main closure declarations; the unconditional theorem remains incomplete.

## Geometric stress test after the finite source route

The independently audited [count/reuse test](docs/DISJOINT_BUSH_COUNT_REUSE_TEST.md)
proves a source-faithful fixed-time-bin refinement and its exact counting cost.
It also constructs one fixed packing-three selector satisfying the new bush
bounds, null exact collisions, qualitative decay, and hereditary residual
excess, while its front has a genuine four-dimensional Frostman escape.
The example does not satisfy the strict dimension-deficit hypothesis and is
not a counterexample to the main theorem. It shows that those intermediate
properties, even with two-time persistence, do not by themselves yield the
aggregate quadratic payment. A collective quantitative use of the actual
front dimension deficit remains necessary. This note is handwritten, not a
new kernel-checked declaration.

The [rooted-time frontier audit](docs/ROOTED_TIME_RECURRENCE_FRONTIER.md)
explains why this continuum recurrence cannot be replaced by finitely many
heavy times, even a growing subpower-separated set. Its conditional fixed-q
near-time charge cites the original manuscript's external Guth--Wang--Zahl
three-dimensional shaded theorem, which is not formalized in this project.
The full coupled-selector root-time charge remains unproved.

A subsequent [scalar-pencil projection audit](docs/SCALAR_PENCIL_PROJECTION_AUDIT.md)
checks a different direct continuum route against primary restricted-projection
and convolution-inverse results. Their hypotheses or exponents do not supply
the missing correlated estimate. A projected Renyi moment of order
`1+theta`, `0<theta<1/3`, would suffice and is compatible with the radial
Frostman escape; proving it from the actual packing-three source remains
open. This is a handwritten sufficient-target analysis, not a new Lean
lemma or an imported axiom.

## Manuscript repair: new supported escape classes

Two new independently checked handwritten arguments make real partial gains.
The [moving-focus estimate](docs/MOVING_FOCUS_LOW_MOMENT_ESCAPE.md) proves the
actual low-order projected moment for `b(a)=c(a)-tau(a)a` when one fixed center
image has subpower covers. The focus time may vary arbitrarily with the source;
no common time, regularity of that time map, or fresh source law is used.
Component estimates are linear in the original mass, and recombination loses
only the explicit center-count factor `N(r)^theta`.

The [correlated-entropy audit](docs/CORRELATED_ENTROPY_CP_AND_TRIANGULAR_ESCAPE.md)
proves a separate Borel triangular escape, allowing three distinct fixed
scalar focus times and arbitrary measurable off-diagonal shears. It also
constructs a packing-three source whose ordinary fixed-block phase tangents
lie in a bad pencil plane while its actual projections are full-dimensional.
The exact entropy identity has a horizontal-information release term, so a
bounded vertical-entropy potential alone does not pay repeated increments.
Macroscopic blocks avoid that particular scale mismatch but still require a
new source-sensitive projection or incidence estimate.

This earlier checkpoint treated the low-moment/center-entropy and triangular
arguments as handwritten. The triangular actual-front and original-root
moment routes are now formalized as recorded above; the general
center-entropy-to-coupled-selector implication remains open.
The fixed-center and affine-reference escape now also have the separate
Lean-certified finite-energy proof described above. Neither representation
has been derived for the general unpaid branch.
The final theorem and its existing WZ axiom dependency are unchanged.

The [rooted entropy-stopping construction](docs/ROOTED_ENTROPY_STOPPING_FRONTIER.md)
strengthens the deficit input: the actual front law has entropy-deficient
blocks at positive upper density along almost every root's own prefixes.
An actual-time stopping split preserves the full inherited occurrence law,
without inverse success probabilities. Its stopped blocks still need a
geometric charge; no such charge is asserted by the construction.
