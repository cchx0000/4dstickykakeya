# Verified original-source occupied-ancestor regularization

Frozen 2026-10-04. Eleven new modules contain 32 public lemmas/theorems and seven definitions. Every module passes strict official Lean 4.33.1 compilation. The proper-import readback audits all 39 declarations using only `propext`, `Classical.choice`, and `Quot.sound`. `NativeOriginalSlopeCubePacking` is a separately frozen dependency with 14 public proofs and two definitions.

## Exact final endpoint

`NativeCompactOccupiedAncestors.compact_original_occupied_ancestors` fixes a compact ORIGINAL marked family K, then for every zeta>0 constructs delta0>0. Only afterward does it quantify the original finite source D, its size n, and eta. Its assumptions are the existing native original finite input, original lines in K, delta<=delta0, and eta<=zeta/32.

It constructs one original index set R, one common height a, and an original dyadic level satisfying delta=2^(-level). It retains the common-height certificate for this SAME a. On that SAME R it proves:

- nonemptiness and n<=2*#R;
- original total shading mass <= twice the sum of retained original shading volumes;
- delta^zeta times retained ORIGINAL tube volume <= retained original shading mass;
- original retained convex-Wolff counts with constant delta^(-zeta).

The shading mass is the sum over original rows, with multiplicity. The theorem does not assert per-tube density or half-retention of union volume.

The actual occupied fine-cell set is `fineParents D R a level`, the image of ORIGINAL graph parameters under the literal dyadic floor map. `descendants` filters that set by the actual dyadic ancestor label, using integer division by powers of two. At every dyadic scale rho=2^(-ell), every occupied ancestor has fine-cell count between

    delta^zeta*(rho/delta)^3 and delta^(-zeta)*(rho/delta)^3.

These are actual occupied fine-cell counts, not original-label counts renamed as covering counts. No output ancestor profile, shading profile, multiplicity profile, or deletion certificate is assumed.

## Finite deletion reused from the repository

`Theorems/Thm_StickyKakeya4_wz_carrier_pruning.lean`, `exists_terminal_carrier_pruning_with_varying_cells` (around line 2203), maximizes cardinality minus occupied-cell threshold penalties. It produces a terminal original set with no occupied cell below threshold. Deletion is charged by original occupied-cell counts times their thresholds; each original cell is charged at most once.

The same file's `ActiveCarrierPruningLevel` and `active_carrier_ceiling_charge_le_two_mul` omit thresholds below one from the loss ledger. Inactive finest cells need only their retained original point.

`NativeOriginalAncestorPruning.original_parent_pruning` consumes that mechanism on exact `parentLabel D a N i` values. A finite subtype embeds the parent-label alphabet injectively; the tube-to-parent map is generally many-to-one. The returned R consists of original `Fin n` labels, with no replacement of lines or shadings.

## Derived source loss, including fine scales

The earlier frozen `NativeCompactParentRetention.compact_parent_bound` supplies the actual occupied-parent count C_K*delta^(-2eta)*N^3. Constants C_K,L_K are fixed from K before delta and the finite source.

For target delta^etaNew*((1/N)/delta)^3, an active level automatically satisfies delta*L_K*N<=1 once delta^etaNew*L_K^3<=1. This follows from the exact identity

    target*(delta*L_K*N)^3 = delta^etaNew*L_K^3.

Thus the chart-count theorem is never used below its valid radius. `NativeCompactAncestorBudget` derives the full original-label deletion bound

    2*C_K*(number of levels)*delta^(etaNew-2eta-3).

`NativeDyadicPruningCutoff` uses the exact level count 1+(-log delta)/log 2 and the existing logarithmic absorption theorem to construct its cutoff. Source eta<=zeta/16 and genuine tube-volume slack beta=zeta/16 pay for both half tube retention and small removed shading. This numerical condition is produced by a theorem, not left as a caller premise.

## Actual shading and CW preservation

`NativeOriginalPrunedMass` uses the proved marked-unit-tube volume upper constant 32*(pi^2/2). `NativePruningMassBudget` combines that upper bound, the actual number of deleted original labels, original radius-one AD counts, and the genuine original tube-volume lower theorem. It derives the removed shading bound required for half retention.

Half retained tube count changes the original CW inequality by exactly a factor of two. `NativePrunedPowerConstants` absorbs that factor into the requested exponent. The source theorem `NativeCompactAncestorRegularity.compact_original_ancestor_regularization` therefore constructs one R with original-label ancestor AD, density, and CW, using eta<=zeta/16.

## Genuine fine-cell readback

The separately audited `NativeOriginalSlopeCubePacking.native_retained_parent_card_le` supplies the geometric upper constant 5832. At the actual finest scale N*delta=1, each fine cell contains at most 5832 original labels.

`NativeDyadicParentCells.floor_dyadic_ancestor` proves exact nesting using `Int.floor_div_natCast`; negative coordinates and half-open boundaries are included. Its `image_parent_fiber_eq_descendants` identifies the descendant fine-cell set with the image of the corresponding ORIGINAL coarse-parent fiber. Fiber counting then proves

    #fine descendants <= #original labels <= 5832*#fine descendants.

The final endpoint runs the label theorem at zeta/2 and constructs a further cutoff absorbing 5832*delta^(zeta/2). This is why its source condition is eta<=zeta/32. Density and CW are weakened to exponent zeta on the same original R.

## Exact remaining geometry and class boundaries

The fine-cell set is a set of graph-parameter labels. Density and CW in the final theorem concern ORIGINAL R and ORIGINAL physical marked tubes. The theorem does not construct a new physical dyadic tube family with transported shadings, nor return R as a new `IsWangZakharovNativeFiniteInput`. Original retained metric-ball AD lower bounds are not asserted.

Fixed dyadic spatial normalization, padding shortened segments into actual unit marked tubes, reindexing the retained family, and transport of AD/CW/density through those physical maps remain separate geometry. The common height is now available for the exact a used by all parent labels.

A concrete next adapter can restrict to an occupied unit graph parent and subtract its integer slope/intercept labels. Parameters then lie in [0,1)^6, and every dyadic floor label changes by the corresponding integer multiple. To consume this physically, only R intersected with the selected parent should be reindexed; removed original rows must not be silently restored. Further fixed dyadic dilation/padding and any resulting rectangular-grid count conversion need their own actual proofs.

The fixed compact K precedes delta0. These results do not force the unrestricted native near-extremizer sequence into one common compact marked family. The repaired extremal class must be tied to a genuinely proved bounded graph normalization and its rescaling closure. No slice AD power estimates (130)–(135), quotient fiber regularity, or final Kakeya conclusion are claimed here.
