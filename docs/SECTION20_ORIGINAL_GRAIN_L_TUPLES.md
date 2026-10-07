# Original-grain paths for the rank-three terminal branch

2026-10-06. Source: Wang–Zakharov, arXiv:2609.22035v1, Section20.1,
printed pages83–86, equations156–161 and Lemma20.1.

The stable `(3,3)` branch is a legitimate terminal outcome of Proposition18.1.
Its Section20 consumer is still required when `0<kappa<=1`. The following
finite count supplies an original-label part of that consumer; it does not
assume or establish that the whole global configuration has already been
constructed.

## Actual one-arm paths and the grain gain

Let I be the finite relation of actual point–tube incidences. A marked half
path is `(middle, (outer, tube))`, with both original incidences in I.
If H is this finite set, then

    |H| = sum_t degree_I(t)^2,       |I|^2 <= |T(I)| |H|.

Keep an actual grain label on each original point. A one-arm path consists
of two marked halves whose middle points have the same grain label. It
retains all six original labels `(p,p',p_tilde',p'',T,T')`; repeated labels
are permitted. If G is the number of occupied grain labels and J the set
of these paths, Cauchy gives

    |H|^2 <= G |J|,
    |I|^4 <= |T(I)|^2 G |J|.

Thus the gain over an ordinary two-tube walk is the actual reduction from
the number of points to the number of grains. No fixed mass fraction in
each grain, pointwise minimum degree, or conditioned probability law is
used. Geometry must ensure that the chosen grain label really encodes the
same height and quotient coordinate before this relation is called a
physical grain.

## Original L-tuples and the exact remaining count

Give each path the key

    (start point, middle height, terminal height,
     moved-point spatial cell, terminal-tube direction cell).

Pairs with the same key are constructed as a finite set of actual paths.
Every pair retains both original incidence paths and all five literal key
equalities. Let B be the number of occupied keys and L this collision set.
The second collision count yields

    |I|^8 <= |T(I)|^4 G^2 B |L|.

Both inequalities and the original-label membership/readback are proved
in `NativeGrainOneArmCount`. All13 declarations passed strict compilation
and independent import/axiom checks on2026-10-06; receipt
`import-batch-20261006T2302` uses only the foundational axioms.

The earlier `GrainJumpArmCount` already proves the related lower count
under a uniform lower population in each grain. The new formulation uses
the exact occupied grain count without that lower-population premise and
specifies the Section20 collision key and its original-label readback.
This is a counting-interface extension, not a new proof of the remaining
geometric step in Lemma20.1.

## Contact-error geometry checked separately

The five declarations in `NativeVLContactIdentity` now prove the exact
V cancellation157 and the two-arm terminal cancellation161 from their
actual horizontal and vertical contact errors. All time factors and the
norm of the actual matrix field remain explicit. Their independent import
receipt is `import-batch-20261006T2307`.

`NativeLTupleCommonCloud` then derives the common moved-point cloud from
the Lemma20.1 small-variation premise, the same original root and the same
intermediate height. Moving within each actual grain keeps its quotient
coordinate. With contact error delta, moved x-gap at most tau, field norm
at most1, `8 delta<=tau`, and the explicit small-variation budget, the
two moved spatial points are within `2 tau` in the product norm. Its four
declarations passed independent import in `import-batch-20261006T2312`.

The remaining native join must use the actual coordinate-frame bound to
convert this product norm to the physical source cube, and choose the
prepared angular query at that true radius. The newly verified literal
Reference cube theorem bounds all terminal parents over that physical
cloud, which is the needed direction-key estimate. No intersection lower
bound for two independently selected direction clouds is necessary.

The geometric step still needed for the paper's precise Lemma20.1 bound
is control of B. For a fixed start, intermediate height and moved x-cell,
the V identity157 and the small slope-variation premise should place all
actual moved points in one bounded physical tau-cloud. The current-source
coarse angular estimate must then bound the terminal direction cells in
that cloud. This cannot be replaced by the angular count at one arbitrary
point, or by an unverified average intersection of two direction sets.

With a genuine common-cloud bound, the expected key estimate is the
number of starts times two height counts times the spatial-cell count
times the actual local direction-cell count. Substitution gives the
paper's grain amplification. This geometric key estimate, time-separated
subfamilies if later requested, and the Section20.2/20.3 contradiction
are not claimed by the finite Cauchy result.
