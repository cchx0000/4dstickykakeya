# A whole-parent heavy-bush restart from actual front deficit

Date: 2026-10-03. The geometric argument and its non-hereditary exhaustion
have been independently checked. The two modules have passed strict Lean
compilation and standard-only axiom readback. This is a new original-data input,
not a completed cap-contraction or main-theorem proof.

A subsequent [common-time strengthening](COMMON_TIME_HEAVY_FAMILIES.md)
now fixes one actual witness time before every later request. The original
varying-time theorem and its verification below remain unchanged.

## 1. Fixed source, coefficient, and actual times

Let `sigma` be one fixed nonzero finite source on bounded slopes, let `b`
be its measurable intercept, and let `J=[u,v]` have positive length.
Assume every original trajectory

    (b(a)+t a,t),   t in J,

lies in the original compact front `K`, for sigma-almost every `a`.
Suppose

    dim_H K<1+beta,       0<beta<3.

Write `p=sigma(univ)`. For every fixed finite `A>=0`, every dyadic scale
cutoff `N`, and every `target<p`, there is a finite source-disjoint family
of measurable positive sets `H_i` with

    sigma(union_i H_i)>target,
    H_i subset {a: |b(a)+t_i a-y_i|<=R_i},
    t_i in J,
    R_i=2*2^(-n_i),       n_i>=N,
    sigma(H_i)>A p R_i^beta.                              (1)

The same sigma, b, J, and beta are chosen before A, N, and target. In
particular one may retain more than half the original parent, or any fixed
fraction below one. There is also a countable disjoint family exhausting
sigma up to a null remainder, with the same coefficient on every piece.

No cardinality bound, common output radius, uniform fraction per extraction
round, or source-piece mass lower bound independent of its radius is asserted.

## 2. Why every positive remainder still has the same coefficient

Fix an arbitrary positive measurable remainder `S` and restrict the
original source to `lambda=sigma|S`. Its actual front is still supported
on K. The coefficient `C=A p` remains fixed; it is not replaced by
`A lambda(univ)` or divided by a new success probability.

The checked rooted-heavy recurrence applies to this finite measure:
for product-almost every original `(a,t)` and every finite coefficient,
arbitrarily fine dyadic radii have spatial bush mass above that coefficient
times the radius to the beta power. Apply it with coefficient `C*2^beta`.
The transverse radius in that recurrence is `2*2^(-n)` for the unit-bounded
slope source, so the factor `2^beta` gives exactly the bound in (1).
The actual time lies in J. Intersecting the selected bush with S yields
an eligible source set H, and

    lambda(bush)=sigma(H)>C R^beta.

The lower bound is thus on the output's own original sigma mass.

An equivalent direct Hausdorff-cover argument makes the role of the
dimension deficit transparent. Cover K by finitely many open balls of
radii r_i with arbitrarily small `sum r_i^(beta+1)`. Each ball receives
at most `2r_i` units of actual time. If every corresponding spatial bush
at each actual time had lambda-mass at most `C r_i^beta`, their total
source-time mass would be at most `2C sum r_i^(beta+1)`, contradicting
the positive original mass `lambda(univ)*|J|`.

This extraction needs neither packing nor a direction-density estimate.
Those hypotheses remain important in the subsequent angular geometry.

## 3. Exhaustion without destroying heaviness

The predicate in (1) is not hereditary under arbitrary source restriction.
Consequently an overlapping countable cover cannot be disjointified by
subtracting earlier pieces: the resulting set could lose its lower mass
bound. The construction explicitly avoids that step.

Consider families of measurable positive eligible sets which are pairwise
disjoint. A union of a chain is again such a family, so a maximal family
exists. S-finiteness makes its positive measurable members countable.
If its uncovered source had positive mass, the extraction in Section 2
would provide another disjoint eligible set, contradicting maximality.
Thus the family exhausts sigma. All selected sets are kept intact.

Finite truncation follows from the countable sum of their measures: every
threshold strictly below `sigma(univ)` is exceeded by a finite subfamily.
Again no piece is trimmed, so every lower bound in (1) survives.

The generic `disjoint_positive_exhaustion` module proves this argument for
arbitrary quantitative eligibility; it does not require a fixed retained
fraction or closure under restriction.

## 4. Application to the original sticky datum

The original compact valid full-direction datum constructs one positive
bounded-density slope source and one common marked slab of length `3/8`.
A strict dimension deficit gives one exponent `0<beta<3` with
`dim_H(unitFront)<1+beta`. Applying Sections 1--3 gives the original-data
endpoint

    sticky_deficit_exists_whole_parent_heavy_bush_families.

Its source is literal original data. Every requested coefficient and cutoff
is handled on that same source, and all witness times stay inside its actual
marked slab. No new geometric certificate, energy estimate, or regularity
hypothesis is added to the main target.

## 5. What is repaired, and what remains

This supplies a whole-parent physical-bush family with nearly complete
source mass, at arbitrarily fine requested cutoffs. It removes the initial
old-graph extraction factor M and the need to improve a fixed old collision
error merely to create those fresh source witnesses.

The generic extraction also applies to a finite old-occurrence source
marginal. Pulling source cuts back to that occurrence preserves its old
neighbor and all marks. This observation does not improve any inherited
old-edge residual or align its collision time with the fresh witness.

Physical bush radii R_i are not direction-cap radii T_i. Summing (1) can
control the physical-radius beta-content, but it does not control
`sum T_i^3`, the antichain capacity envelope, or a paid old-edge estimate.
A wide angular bush can meet (1). Turning this input into a whole-parent
direction-density increment still requires a genuine radius/mass comparison
or a supported Frostman escape.

The original cap-return results identified in
`CAPACITY_ENVELOPE_AND_WITNESS_POOLING.md` give lower angular-radius locks,
not the upper comparison required for that next implication. A fixed
positive bush also has fixed physical error; freezing its mass does not
permit sending that error to zero in a Frostman-limit argument.

## 6. Verification

The `disjoint_positive_exhaustion` module contributes three declarations,
and `whole_parent_heavy_bush` contributes six. All nine passed source
compilation and import readback with `-DautoImplicit=false -DwarningAsError=true`.
Every readback uses only `propext`, `Classical.choice`, and `Quot.sound`.

The targeted Lake build passed 8,757 jobs, including the restored existing
rooted-heavy dependencies. It replays existing warnings in older modules;
the new source files pass the warning-as-error checks. Exact hashes and
commands are in `verification/whole-parent-heavy-bush-checkpoint.json`
and the corresponding strict, build, and axiom logs.

The previous 187 module hashes are unchanged. This is not a fresh full
default build of the 189 project modules at that checkpoint. The original main theorem
and its existing WZ project-axiom dependency remain unchanged.
