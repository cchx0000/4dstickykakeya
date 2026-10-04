# Independent finite route toward a positive A.3 gain

Date: 2026-10-04. This is a proof decomposition, not an assumed expansion
engine. The installed-source search and candidate statement readback are
recorded separately. No A.1 or A.3 conclusion may be used as an input.

## The two exact targets

The robust projection target needed for this weaker route is:

For fixed `0<t<2` and `0<s<=1`, choose `eta>0`, `epsilon>0`, and `n0`
before the finite data. For `delta=2^(-n)`, `n>=n0`, let P be a nonempty
delta-separated original planar subset of a fixed unit box, with
cardinality `delta^(-t)` (or a separately justified tolerance around that
cardinality), and normalized point nonconcentration at every radius
between delta and one. Let E be a nonempty separated original direction
set with normalized s-Frostman constant at most `delta^(-epsilon)`.
The required conclusion is an actual direction subset of at least half
the original direction mass such that, for each selected direction,
EVERY original `Q subset P` of cardinality at least `delta^epsilon |P|`
has at least `delta^(-eta) sqrt(|P|)` occupied projected delta-cells.
The point nonconcentration exponent may be any fixed positive exponent;
on regular pieces the available exponent is t. Constants for slope
charts and floor cells must be paid in epsilon.

For comparison, the separated-real GKZ 1.1′ input is one actual finite
`A subset [1,2]`, delta-separated, of cardinality `delta^(-sigma)`, with
`0<sigma<1` and interval count at most `C |I|^sigma |A|` for every
interval of length at least delta. It produces growth of the sum of
the delta-covering numbers of `A+A` and `A*A`, by a factor
`C^(-O(1)) delta^(-c)` for any
`c<sigma(1-sigma)/(4(7+3sigma))`.
[GKZ, Theorem 1.1′](https://arxiv.org/html/1804.02475).

These are not interchangeable theorem types. GKZ has one scalar carrier,
matched mass and nonconcentration exponents, and no varying dense query
or prescribed direction set. A ring-to-projection reduction must produce
that carrier and retain the original point and direction weights.

## What the OS proof actually needs

OS starts its regular-projection induction with Bourgain's robust gain
(Proposition 4.15). Its stronger inductive improvement uses robust scalar
ABC (Theorem 1.7): `0<beta<=alpha<1`, `gamma>alpha-beta`, separated scalar
A,B,C, `|A|<=delta^(-alpha)`, original beta/gamma interval profiles, and
one coefficient working for every graph of density `delta^chi`.
[OS Section 4](https://arxiv.org/html/2301.10199v4).

Here is the exact matching calculation at the end of that construction.
At fine scale `delta=Delta^2`, original A lies in an interval of length
Delta and is delta-separated. Rescale only this coordinate:
`Anew=A/Delta`. It is Delta-separated, as is the actual vertical B carrier.
Writing `sigma` for the slice multiplicity exponent gives

    alpha=t-sigma+zeta0,
    beta=sigma-zeta0,
    gamma=s-zeta0.

The strict gap is `gamma-(alpha-beta)=s-t+2sigma-3zeta0`. Choosing zeta0
inside that gap, and zeta sufficiently smaller, gives the scalar ABC
parameter range. The original graphs after this coordinate rescaling
have density at least `Delta^(27zeta)` and actual projected cover at most
`Delta^(-9zeta)|Anew|`. The vertical source's local interval profile can
be weakened to beta; large-radius counts follow from its total original
population. This is a concrete match after those geometric objects have
been constructed.

Our current shading regularization does not construct these OS objects.
The radial worker confirmed that its actual occupied-cell selection gives
normalized point profiles, but no local two-scale regular pieces, good
Delta-tube, or vertical B fibers. Those remain additional deductions.

Two elementary normalization details also remain explicit. Separated
original real sets can be rounded at a smaller fixed mesh with bounded
projection error; separation alone is not literal grid membership.
A coefficient source in [0,1] must be restricted away from zero before
using a theorem stated for [1,2]. Its original interval profile allows
an actual dyadic annulus selection; writing that annulus as [h,2h], send
`c` to `c/h` and B to `hB`, use mesh `h Delta`, and charge the finer-cover
loss `O(1/h)`. Translating the coefficient while leaving A×B fixed would
be invalid.

## Installed proof inventory

The inspected pins are mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
(8311 Lean sources) and LeanFormalizations
`dd46c17a2a034d7bfa0df02e7f77834d35592864` (166 Lean sources).
No suitable discretized real sum-product, Bourgain projection, or robust
scalar ABC expansion declaration was located. See
`InstalledDiscretizedExpansionSearch.json` for the exact search scope,
patterns and candidate hashes.

The genuine installed tools were checked by their types:

- `Finset.balog_szemeredi_gowers_asymmetric_explicit` requires equal
  source cardinalities and additive energy; it returns large subsets
  with a small difference set, not growth under multiplication
- mathlib's Pluennecke-Ruzsa inequalities control finite additive
  sum/difference sets; their role is to propagate already known bounds
- our `AsymmetricDyadicAbsorption.original_real_dyadic_bsg` removes the
  equal-cardinality obstruction for original separated real sources,
  but still requires actual near energy and returns upper sumset bounds
- our original labeled energy-bin caller handles genuine values and
  original multiplicities; it is a valid bridge into BSG, not a growth
  theorem
- LeanFormalizations' Szemeredi-Trotter interfaces count exact point-line
  membership. They have additional crossing/planarity hypotheses, and
  the inspected canonical-component source still contains an open
  per-step geometric proof. Even a completed exact-incidence theorem
  would need a genuine thick-incidence transfer here

The four usable additive candidates have a fresh imported type/axiom
readback in `InstalledExpansionCandidateReadback.strict.log`. This adds
no new public proofs. A direct transfer from exact product cardinality
to delta-covering number can lose an entire factor delta inverse, since
products of delta-grid values lie on a delta-squared grid. Such a loss
would overwhelm the desired small gain.

## First concrete missing finite reduction

Work with original planar P, mesh delta, and projections
`pi_lam(x,y)=x-lam*y`. Pick original slopes lam0,lam1 with
`h<=|lam0-lam1|`, `0<h<=1`, and `|lam0|<=1`.
Map each original point to

    code(p)=(floor(pi_lam0(p)/delta),floor(pi_lam1(p)/delta)).

If two original points have the same code, both projection differences
have magnitude below delta. Solving the two scalar linear equations
gives native distance at most `3delta/h`. Original delta-separation
therefore bounds each actual code fiber by

    D=(6/h+2)^2.

Consequently the literal graph of code pairs has at least `|P|/D`
edges. If each original projected cover has at most `K sqrt(|P|)` cells,
the graph density is at least `1/(D K^2)`. Each scalar alphabet also has
at least `sqrt(|P|)/(D K)` elements. This is the concrete reason the
half-dimension counterassumption permits a dense Cartesian reduction.

For any third original slope lam, solve its projection as a linear
combination of the first two. Replacing their exact values by their
floor representatives causes error at most
`delta (|lam1-lam|+|lam-lam0|)/|lam1-lam0|`.
Every image graph edge retains an actual original point witness, and
every original subquery maps to an actual subgraph with the same fiber
bound. Thus its small original projection transfers to a literal
restricted scalar linear image with an explicitly enlarged floor cover.
No post-quotient density or near energy is supplied as a premise.

This is the first implementation target. It is followed by a separate
selection argument choosing two transverse directions while retaining
enough of the direction-dependent original queries. One must not
replace all those queries by a fixed common set without proving its
mass. Original weighted second/third moments and the direction interval
profile are appropriate tools for that selection.

## Constructive decomposition after that reduction

This is a dependency estimate, not a claim that the remaining statements
are already proved or a fixed schedule.

1. Finish original two-projection coding, transversality selection, and
   the bounded perturbation of every other projection. These are finite
   geometry and counting modules; current packing, original graph and
   collision engines supply much of the machinery
2. Extract nearly balanced scalar sources from the resulting dense
   Cartesian graph, using the actual original near energy and existing
   BSG. Prove their interval profiles from the selected regular source,
   retaining the density losses
3. Establish the actual ring-to-projection implication. Many small
   restricted scalar linear images must force a single nonconcentrated
   scalar set with both small additive and multiplicative covering
   numbers. BSG alone does not give the multiplicative conclusion.
   This is a separate substantive proof, especially with sparse
   prescribed coefficients and direction-dependent queries
4. Prove a genuine discretized ring engine. A tractable independent
   target is GKZ 1.1′: original multiscale additive regularization;
   covering versions of Ruzsa/Pluennecke with actual refinements;
   popular overlaps of dilates; small-denominator-aware mixed-sum
   bounds; a finite ratio-set dense/gap dichotomy; the two collision
   estimates; and positive exponent absorption. The current library
   supports the additive algebra, not these geometric conclusions
5. If the ring engine uses matched cardinality/profile exponents,
   prove the needed regularization or more general nonconcentration
   variant. Choosing an exponent from the source cardinality does not
   establish its interval profile
6. Produce robust projection with uniform quantifiers and a positive
   margin on a fixed compact range of local dimensions. Use a proved
   finite parameter selection or explicit constants; do not infer a
   uniform positive infimum from pointwise existence
7. To reach the native A.3 contradiction, construct actual regular
   pieces and the incidence-preserving product over scales. The
   critical-width cap must force a positive amount of useful branching
   away from dimensions zero and two. Combine a baseline estimate on
   the other pieces with the weak positive projection margin on these
   useful pieces, retaining the original shadings and weights

This weaker plan avoids the optimal scalar ABC theorem only if steps
3–7 are genuinely proved. It also avoids using our unproved all-scale
A.1 theorem. It does not assert that the single-set GKZ theorem alone
already implies the needed robust projection statement.
