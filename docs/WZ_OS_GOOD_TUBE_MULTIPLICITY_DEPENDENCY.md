# The precise good-tube nonconcentration obligation

Date: 2026-10-04. This audit starts from the proved original third-query
family, not from a desired scalar regularity certificate.

## Finding

The scalar nonconcentration in OS's good-tube construction does not
follow from its weighted tube selection alone. The proof first removes
local high-multiplicity points using an already available projection
theorem. That is a genuine additional premise at this stage.

The exact dependency is: the inductive `Projection(s,sigma,t)` premise
feeds Theorem 4.19; that gives (4.50), used in the deletion (4.51).
Lemma 4.73 then uses the resulting local exclusion at an actual original
point to count coarse discs along the chosen tube. Corollary 4.83 turns
this into the scalar B interval profile. Proposition 4.15 obtains the
induction's initial input from Bourgain's positive projection gain.
[OS Sections 4.2–4.10](https://arxiv.org/html/2301.10199v4).

Thus the printed good-tube step is part of an improvement of an existing
positive projection theorem. It cannot silently serve as a proof of
the first positive gain in our weaker Bourgain route.

## Exact missing input

Fix the original point dimension t, direction exponent s, and a slice
exponent sigma satisfying

    (t-s)/2 < sigma < t/2.

One first needs positive epsilon0 and Delta0, chosen before the data,
such that at every mesh Delta<=Delta0, for every original
`(Delta,t,Delta^(-epsilon0))`-regular measure and every original
`(Delta,s,Delta^(-epsilon0))` direction source, some direction has
high-multiplicity mass at most `Delta^epsilon0` at threshold
`Delta^(-sigma)`.

Here high multiplicity counts occupied cells of the thickened ORIGINAL
support along the line through the original point. Regularity includes
both its point-mass law and its two-scale local occupied-cell law.

The local consequence used by the scalar extraction is stronger than a
single global fiber bound: outside a small exceptional point mass, every
admissible pair `delta<=r<=R<=8` with `r/R<=delta^eta` has original local
line multiplicity below `4(R/r)^sigma`. At the good-tube scale
`Delta=sqrt(delta)`, applying this with scales `8Delta,8R` gives the
coarse-disc upper count of order `(R/Delta)^sigma`. The original point
used for this application lies in the actual retained set K0.

Our currently proved Kaufman input has projection exponent
`min(s,t,1)`. Converting it to a global slice exponent gives at best
`t-min(s,t,1)`, with the displayed density/mesh losses. For the relevant
small-s case `s<=t/2`, this is at least t/2. It does not supply the
strictly smaller sigma needed above. Retaining dense original queries
or rewriting their coordinates does not change this exponent.

## What the actual third-query family does imply

There is a constructive global LOWER multiplicity consequence, which
is useful but has the opposite role from the missing local upper bound.
If `Q subset P`, `|Q|>=q|P|`, and its literal projected delta-floor image
has at most `K sqrt(|P|)` cells, discard query fibers smaller than
`|Q|/(2 |image|)`. Their total original mass is at most half of Q.

The remaining R consists of whole original Q fibers and satisfies

    |R| >= (q/2)|P|,
    |{x in R: floor_delta pi(x)=floor_delta pi(p)}|
       >= q sqrt(|P|)/(2K), for every p in R.

The same fiber is exactly the corresponding original Q fiber. Since
R lies in Q and Q lies in P, every selected point therefore lies in an
actual original projection strip containing at least that many original
P points. The scalar projection is evaluated on the original points;
no resampling or projected lower-bound certificate is introduced.

`OriginalGlobalProjectionMultiplicity.lean` proves this caller by reusing
the existing `BackwardFiberGrains.dense_class_retains_half`, including
the exact original-fiber identity. This gives the global-rich part of
the desired construction. It does not assert that the surviving points
avoid any local high-multiplicity sets.

## Why the missing local property cannot be inferred from two projections

The exact diagnostic `test_cartesian_marginal_profile.py` uses
`delta=N^(-2)` and the N by N product consisting of N macroscopically
spaced x-values and N delta-spaced y-values in an interval of length
1/N. It verifies the planar dyadic 1-regularity inequality at every
pair of dyadic scales. An invertible shear makes its two coordinate
alphabets into two bounded-slope projection alphabets of size N.

The small scalar marginal is entirely concentrated at scale 1/N, so a
half-dimensional normalized scalar profile needs constant at least
sqrt(N). Correspondingly, a rich fiber can have N occupied fine cells
inside length 1/N, while the desired half-dimensional local bound is
only order sqrt(N). This directly tests the unsupported local exclusion.

The same diagnostic verifies that the middle projection occupies N²/2
cells. Thus this example is not a counterexample to the entire many-third-
query hypothesis; rather, it shows exactly which extra information a
future proof must exploit. The current third-query family preserves
that information and all original witnesses.

## First unproved implication

From the actual many-direction query/graph family, construct surviving
original point mass and directions with the local occupied-fiber upper
bounds above, or establish an independent discretized-ring reduction
that does not require those bounds. The OS good-tube proof obtains them
from an earlier positive projection theorem, so importing just its
conclusion here would be circular for the first gain.

No original scalar Frostman law, approximate-ring closure, or A.3 gain
has been inserted as an assumption or claimed by this audit.
