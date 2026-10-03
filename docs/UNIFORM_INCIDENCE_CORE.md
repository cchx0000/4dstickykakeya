# Uniform cores on the same actual incidence parent

Date: 2026-10-03. The finite and integer-weighted theorems below are
Lean-checked. They are an intermediate construction, not the missing
small-hairbrush estimate or a proof of the original final theorem.

## 1. Actual subsets and unchanged weights

Let A be a nonempty finite set of actual occurrences. For each of d
neighborhood types i and each occurrence x, let R_i(x) be a finite
neighborhood containing x. Fix an integer Q>=2 and suppose |A|<=Q^L.
There are nonempty C subset B subset A such that

    |A| <= ((L+1)^d)^(dL+1) |C|,
    |B intersect R_i(y)| < Q |B intersect R_i(x)|
       for every x in C, y in B, and every i.

Both sides of every comparison use the SAME retained parent B. No
individual neighborhood is renormalized. Occurrence coordinates and their
physical witnesses are retained by restriction.

The weighted endpoint replaces every count by the sum of one fixed positive
integer weight w on A, assumes sum_A w<=Q^L, and keeps exactly those weights
in the retention and local comparisons. It does not claim arbitrary real
weights without an atom-floor argument.

## 2. Constructive finite descent

Quantize the current local counts by floor(log_Q), clipped to {0,...,L}.
There are at most P=(L+1)^d profiles. A largest profile class retains at
least 1/P of the current cardinality or original integer weight.

Restriction can only decrease every local count. Thus the next retained
profile is coordinatewise below the previous one. If different, the sum
of its d integer coordinates strictly decreases. This sum is initially at
most dL. At a stationary step, the next large class C attains the previous
profile, whereas all current-parent values on B are bounded above by it.
The logarithmic-bin bounds give the displayed Q comparison. At most dL+1
largest-class selections account for the explicit retention factor.

This is a finite descent of actual counts. It does not use a bounded
product of favorable scalar density multipliers or discard a replenishment
term from a filtration identity.

## 3. Intended geometric use and its limits

A finite source/time/angle incidence configuration supplies such
neighborhoods by its actual geometric rectangles. For a fixed finite
macroscopic scale list, choose Q on the order of delta^(-epsilon), with L
large enough to bound the original total count. Then d and L are fixed
before delta tends to zero, so the displayed retention factor is a fixed
constant and can eventually be absorbed in a small power of delta.

This is the finite-profile mechanism behind the regularization in
[Wang--Zakharov, Proposition 5.1 and Section 4](https://arxiv.org/pdf/2609.22035).
The module proves the subset construction and comparisons directly; it
does not invoke their theorem or add an axiom.

It is useful because a local comparison now concerns one retained parent,
instead of separately normalized tiny witness pieces. However it does NOT
imply that the common maximum is a large cap density, that the retained
source is a product law, or that a physical heavy bush contracts to a
sufficiently small direction cap. A later restriction can destroy the
proved uniformity. The number of neighborhood types must also be included
in the cost: enumerating every fine time or center is not a constant-cost
application.

The original geometric problem still needs a construction that uses this
uniformity to force a genuine gain or a supported Frostman escape. The
multiscale extremality and grain arguments in the cited paper are additional
mathematics, not consequences silently incorporated into this module.

## 4. Verification

The module is `Theorems/Thm_StickyKakeya4_uniform_incidence_core.lean`.
Its eleven theorem readbacks, source hash, and exact commands are recorded
in `verification/uniform-incidence-core-checkpoint.json` and the associated
strict/build/axiom logs. No source or statement of the final theorem is
changed.
