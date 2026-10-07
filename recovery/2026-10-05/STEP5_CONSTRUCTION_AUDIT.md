# WZ Step 5: source-faithful compatibility and deletion audit

Source: [Wang–Zakharov, pp. 70–71, (117)–(126)](https://arxiv.org/pdf/2609.22035#page=70). Audited 2026-10-05 against the current Lean repository. This is a mathematical implementation audit, not a claim that the remaining geometric adapters are already formalized.

Current status, 14:05 UTC: the historical construction plan below has now produced strictly checked actual successor menus, weighted compatible selection, approximate packet fibers, source-derived reference density, and an actual finite grain history. The latter keeps one original E2 and proves a fixed2^J mass loss, subsequently absorbed once by a source-uniform cutoff. Actual fixed-node planes and their compatible variation are also checked. The actual rank-four exclusion and source construction with rank2or3 and final dense grains are now verified. The lower-rank horizontal-slice/configuration and contradiction steps remain in progress. See [the current verification ledger](VERIFIED_NATIVE_PROGRESS.md) and [machine-readable status](CURRENT_RECOVERY_STATUS.json). The open obligations in the historical plan are not all still open; no unconditional main-theorem completion is claimed.

## Source reading and the exact gap in a naive transcription

The backward candidate construction takes unions of compatible finer candidates. The forward construction additionally deletes sparse direction-segments. The union identity does not, by itself, imply that one entire finer candidate lies inside the surviving parent set. Intersections must be tracked explicitly. Nor does density of a union guarantee comparable density of an individual member. The paper's compact presentation must therefore be expanded into an incidence argument before being used as a Lean premise.

For example, partition a child point set into N disjoint candidate supports, all having one coarse angular ancestor. Their union is the whole child. Selecting a single candidate retains only 1/N, and an arbitrary parent deletion can cut every candidate. Repeating a fresh density lower bound at every level introduces an unjustified product loss.

The stated paper retention exponent must not be implemented by multiplying the same power once per level. A finite number of constant-factor losses is harmless after the final source cutoff; a power loss at each level requires an explicit exponent budget.

## Concrete replacement architecture

Use one original point-label set I and a finite set G(x) of good TERMINAL angular cells for every x in I. Keep A={(x,u): x∈I, u∈G(x)} until the compatible-selection theorem is applied. Do not first choose one tuple per point. Spatial maps q_j depend only on x. Angular maps k_j are literal dyadic ancestors of the terminal cell and satisfy k_J(u)=u. Actual transverse tuple representatives may be chosen per spatial/angular node from genuine good-tuple witnesses; a cell center must not be substituted when transversality is not stable at that coarse angular resolution.

The existing CompatibleTupleSelection.weighted_good_tuple_family_selection already gives a compatible subset S of ORIGINAL labels with

    W(S) ≥ (sum_x w(x) #G(x)) / product_j B_j.

It also proves injectivity of the selected witness-pair projection to original labels. Thus the numerator is the full good-tuple multiplicity, not merely W(I).

### Actual successor menu needed

For a child spatial cube Q of side r and a fixed angular rho-cell, use the ORIGINAL reference incidence set E1, not a newly normalized refinement. Restrict E1 to incidences whose original point lies in Q and whose tube direction lies in the fixed angular cell. Two geometric bounds are sufficient:

1. This restriction meets at most C original rho-phase parents. At a common spatial location, slope confinement also confines the intercept.
2. Its actual same-R r-shadow occupies at most C physical point labels. This uses representative coherence and the spatial localization of the original points.

The hereditary conditional physical upper then bounds the number of r-phase parents, hence the number of r-angular cells, by C delta^(-tau) (r/rho)^(-kappa). For ell-tuples, take the ell-th power. These are genuine finite image-cardinality conclusions, not pointwise uniformity assumptions.

With grain radii Delta_1>...>Delta_J, the bounds have the form

    B_1 ≤ C^ell delta^(-ell*tau) Delta_1^(-kappa*ell)
    B_{j+1} ≤ C^ell delta^(-ell*tau) (Delta_{j+1}/Delta_j)^(-kappa*ell).

The scale factors telescope to Delta_J^(-kappa*ell). A terminal good-tuple lower bound of that same order cancels this factor. Rank-stage retention is paid once. The remaining loss is a fixed constant to power ell*J and an original-delta exponent O(ell*tau*J).

J must be chosen BEFORE tau, independently of the master's interpolation count g and of the later native input exponent eta. One may use a separate fixed grain count and depths floor(j*stopDepth/J), retaining the endpoint exactly. Using J=g is invalid because g itself grows as tau decreases. The winner-depth lower fraction must also be fixed independently of tau before converting delta errors to stopping-scale errors.

## Additive pruning after compatible selection

After selection, fix the chosen angular tuple at each occupied spatial node. Let S0 be the compatible original point set, with W(S0)≥f W(I). All later sets are literal subsets of S0 and all weights remain unchanged.

### Spatial sparsity

For each level, remove a node P when its current retained mass is below epsilon_j W(I∩P). Spatial nodes at that level partition I, so the charge is at most epsilon_j W(I). Across levels the charge is their SUM. To ensure final, rather than historical, node density, use finite peeling until stable. Charge a node only when it is removed; that node cannot return, so the same sum bound remains valid despite cascades.

Taking epsilon_j=f^2 with J f≤1/4 leaves at least 3f/4 of the original mass before direction pruning. More generally require sum_j epsilon_j≤f/4.

### Actual direction-segment family statement

For each node P and each of its ell fixed chosen directions, construct finitely many core packets L and fixed reference supports A_L such that:

* every relevant candidate point belongs to a core packet;
* S_current∩L is contained in A_L;
* A_L is a literal subset of the original reference point set in a fixed enlargement L+ of L;
* the enlarged packets have overlap at most C, and remain inside a bounded enlargement of P;
* A_L contains enough original reference mass relative to the maximum mass carried by one geometric vertex at the grain resolution.

Delete a core packet if W(S_current∩A_L)<theta_j W(A_L). The first three properties give an actual bound on the mass deleted from L. Bounded overlap gives charge ≤C theta_j W(I∩P+) per chosen direction. Summing over spatial nodes, directions, and levels gives ≤C' ell sum_j theta_j W(I). No repeated multiplicative density loss is required.

The localization implication must be stated in the needed direction. Knowing that a tube segment is contained in L+ does not automatically say that L is contained in a coarse tube. A safe reference is I∩L+ together with an actual shading subfamily proved to lie there. The proposed length-Delta/direction-error-Delta localization into a 14 Delta^2 packet is a suitable starting adapter.

Predecessor richness is asserted in the PREVIOUS deletion layer. Later deletions need not preserve it inside the final set. BackwardFiberGrains.layered_backward_fiber_bound has exactly that layering convention. A final subset still inherits the ambient backward-fiber count. To make all occupied final grain classes dense, charge sparse grain classes additively over all levels using the proved ambient grain-count bound; repeated half-retention is unnecessary.

## Existing Lean coverage and remaining actual geometry

* CompatibleTupleSelection supplies weighted compatible original-label selection, conditional successor menus, and the exact numerator retaining all good terminal witnesses.
* RichDirectionalLayers.richLayers_card_loss and WeightedRichDirectionalLayers.weightedLayers_mass_loss already provide additive class-deletion ledgers.
* WeightedRichDirectionalLayers.weighted_predecessor_vertices converts original predecessor weight to distinct vertices using an original vertex cap.
* BackwardFiberGrains proves the multiplication of exact predecessor fibers and the resulting grain count. It assumes the actual rich predecessor relation; it does not derive it from tube shadings.

For actual packets, exact affine fibers of ordinary grid centers cannot be assumed: a thin tube gives approximate, not exact, collinearity. A quantitative oblique-grid/finite-neighbor adapter or a bounded-overlap approximate-fiber version is still needed. The wedge lower bound pays its conditioning loss. This is separate from the finite compatible-selection and deletion argument.

Global row-size lower bounds alone do not imply lower occupancy of every short occupied segment. A possible route uses the already installed ordered-pair relations: condition on a sufficiently fine reference tube parent and a coarser physical point label, then compare with fine physical pair fibers. Together with global row size this gives occupied short-row counts. Nearby finer installed scales can pay a small power instead of assuming uniformity at adaptive grain scales. The required finite geometry and the exact loss still have to be proved.

## Point-scale bookkeeping

WZ's eventual smallest point scale is a=delta_stop^2. The current rank-refined incidence set uses original microcell labels k at mesh delta/2. They are not interchangeable. Either install the selected a-ancestor relation after the rank choice, or keep literal microcells with their original weights and prove an explicit cover-count readback. Every statement of mass, support, vertex cap, and deletion must specify its scale.

All existing fullSource comparisons in this construction have depth 0≤f≤level and physical radius≥64 delta. The mesoscopic stop-square condition places the actual grain point scale in that range. No last-six-depth extension or silent scale renaming is used.

## Recommended next theorem

First formalize the spatial-cube/angular-cell successor-menu cardinality bound above from actual old incidences and the hereditary physical upper. Then feed its ell-fold menu bound and the actual terminal good-tuple count to weighted_good_tuple_family_selection, with J fixed before tau. Next formalize the packet coverage/overlap/reference-mass statement and use the existing additive weighted-layer ledger. This separates the finite combinatorics from the genuinely missing approximate geometric fiber adapter without assuming a rich-core or compatible-candidate certificate.
