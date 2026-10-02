# Genuine independent flags can reroute the aggregate cross-cap graph

Date: 2026-10-02. Status: a source-level geometric reduction with an independently
formalizable probability component. It does not prove cross-cap payment or
termination of the remaining physical-bush alternative.

## 1. The actual conditional law is available at both original endpoints

The source's `cor:v080-conditional-flag-normal-cap` defines

    kappa_z(df) = N_flag(z)^(-1) w_f(z) dLambda(y,f),
    w_f(z) = 1_{A_{p,q,omega}}(z) h(p,z) h(q,z).

It is a probability law on the fixed coarse layer `G_*`, and its closed normal
caps satisfy

    kappa_z{f: dist(n_f,n)<=theta} <= K theta

with one finite coarse constant `K`. Its physical base is the normalized
occurrence marginal `mu_hat_*`, not automatically unweighted Lebesgue measure.
On the fixed dyadic coarse layer those bases are comparable by fixed constants.

The support condition `w_f(z)>0` means that the sampled flag is an actual old
contact/phase packet containing the same physical endpoint `z`. It is not an
arbitrary normal assigned to a point. In particular the old/new comparison in
`lem:v078-old-flag-new-cycle-polarization` has its required same-endpoint old
packet incidence whenever such a fresh flag is used.

The source's `lem:v081-lossless-conditional-flag-tensor` explicitly permits
independent samples from these genuine laws at every physical endpoint. If a
current occurrence also retains correlated origin flags, old times, routing
labels, or the original neighbor, preserve all those coordinates and append the
fresh samples. Do not replace their conditional law by the fresh law.

This construction must not be used after moving an endpoint outside the fixed
coarse layer without separately supplying the corresponding genuine flag law.
For a root-preserving exit measure dominated by the root product on `G_* x G_*`,
both original endpoints remain in the layer.

## 2. Separation is an exact conditional probability gain

Let `Gamma` be any finite original occurrence measure, with fixed physical
endpoint maps `z(omega), zeta(omega)`. Add two conditionally independent flags
with law

    kappa_{z(omega)}(df) kappa_{zeta(omega)}(df').

For every original occurrence and every fixed first flag, the probability
that the second normal is within distance `theta` of the first is at most
`K theta`. Integrating over the first flag and then the occurrence gives a
stronger statement than a total-mass bound:

    marginal_of_close_flag_part <= (K theta) Gamma,
    marginal_of_far_flag_part   >= (1-K theta) Gamma.

The inequalities are measures on the whole original occurrence space, so all
inherited coordinates are preserved. Choose one fixed positive coarse
`theta` with `K theta<=1/4`. At least three quarters of every original
occurrence survives the separated-normal cut. No endpoint mass or tree-node
normalization enters this calculation.

The cap condition is closed (`<=theta`); its complementary separated event is
strict (`>theta`). This convention is useful for the compact-cell step below.

## 3. Fixed cells remove the tiny-node mass problem

Suppose the aggregated physical exit law, after integrating its existing
labels, is

    dGamma_r(z,zeta) = g_r(z,zeta) dmu(z) dmu(zeta),
    0<=g_r<=h_r<=1,

where `mu` is the fixed normalized coarse physical marginal and every positive
edge of `h_r` has the required actual scale-`r` physical collision witness.
The fresh decorated vertex measure is the fixed probability

    dnu(z,f)=dmu(z) dkappa_z(f).

Partition the compact projective normal space into finitely many Borel cells
of diameter at most `theta/8`, with compact closures of the same diameter.
For every cell pair containing normals at distance greater than `theta`, the
two compact closures are at distance at least `3theta/4`. Sum over those
separated cell pairs. By section 2 their cross-graph masses total at least
`(3/4) Gamma_r(univ)`.

There are only a fixed finite number `N^2` of pairs. Therefore one separated
pair has cross mass at least

    3 Gamma_r(univ)/(4 N^2).

Each positive-mass cell restriction `nu_i` is a fixed measure, independent of
`r`. After deleting null cells, the minimum of the finitely many positive cell
masses is a fixed positive number. Hence the lower endpoint-mass hypothesis
in Proposition 8.48 can be met on these aggregate coarse restrictions. If a
single pair is needed along a sequence, finite pigeonholing gives one after
passing to a subsequence.

This construction differs from trying to apply Proposition 8.48 separately
to arbitrarily small direction-cap tree nodes. It also does not infer normal
separation from separation of direction caps.

## 4. The designated-flag version of Proposition 8.48

There is a genuine statement-level distinction. Literal Proposition 8.48 says
that **every retained old polarization normal** on restriction `i` lies in
`N_i`. Existing correlated marks need not satisfy that condition after the
fresh extension. Thus its literal hypothesis has not been established.

The proof supports the following weaker hypothesis instead:

- Each decorated vertex of restriction `i` has one **designated genuine old
  flag at that physical vertex**, whose normal belongs to `N_i`
- All additional inherited marks remain attached, with no restriction on
  their normals
- The two `N_i` are compact and positively separated; the remaining physical,
  endpoint-mass, and quantitative routing hypotheses of Proposition 8.48 hold

Under these hypotheses its same routing conclusion follows, with the same
kinds of constants and alternatives.

Proof. Normalize the two fixed endpoint measures and form the symmetric
bipartite graph. The two Cauchy--Schwarz steps produce alternating four-cycles
as in the source. On a determinant-small, non-line cycle, the new polarization
cannot be close to both separated compact normal sets. At least one vertex's
designated old flag is therefore transverse to that new polarization. Rotate
that vertex to the decorated free endpoint (at most a factor four). Its old
packet actually contains this endpoint by section 1; the new packet contains
the same endpoint by the physical cycle routing. The source's pointwise
old/new polarization comparison applies. Additional inherited flags cannot
invalidate either incidence and are integrated as probability marks. The
close-anchor, horizontal-line, and determinant-nondegenerate physical-bush
outputs are unchanged. QED at the same source-level status as the geometric
lemmas invoked by Proposition 8.48.

This designated-flag formulation must be proved explicitly in a formal
implementation. A probability-only fresh-flag theorem does not by itself
establish the old/new geometric packet comparison, its weighted payment, or
this generalized routing theorem.

## 5. What this reduction does and does not buy

The reduction shows that an excessive aggregate old-endpoint cross graph can
be given genuine separated old polarizations on fixed positive-mass decorated
restrictions. It bypasses the direction-versus-normal and tiny-node-mass
objections to *entering* the separated-polarization routing.

It still has the physical-bush alternative. That case is produced by the
determinant-nondegenerate part of the Maslov routing and is not excluded by
the fresh normal separation. Moreover the proof extracts four-cycle mass of
order `X_r^4` or a bush at a power of `X_r`; it does not transport all the
original exit occurrence with coefficient one. A conditional-law extension
preserves the input exactly, but subsequent four-cycle extraction is a new,
nonlinear step. Those facts must not be conflated.

A sufficient *termination/charge invariant* for continuing this approach would
have to supply the following at the original root scale `r`:

1. For each active root-occurrence remainder `Gamma'`, lift a measurable
   positive portion of it into the separated-normal route without replacing
   its endpoints or density budget
2. On each physical-bush output, either charge that portion to a root-weighted
   paid measure whose sum is `O(m^2 r^(2-eta))`, or continue it with an explicit
   progress quantity whose available total is finite
3. Retain a coefficient-one joint root budget through every continuation, and
   prove that the total old mass reaching an infinite or uncharged terminal
   continuation is zero or at that same quadratic scale

The existing source-cap diameter is not such a complete invariant: below the
fixed root angular cutoff, all surviving original pairs are cross-cap. Nor
is the scalar edge mass of a newly normalized two-copy graph a progress
quantity: it can equal `1/4` again on every return while the absolute original
exit mass is unchanged.

The radial model in `SEPARATED_BUSH_CROSSCAP_BOUND.md` tests this distinction:
physical re-partitioning can keep the entire old graph alive while producing
arbitrarily small source bushes. Its four-dimensional front correctly permits
a Frostman exit, but source-cap contraction or fresh independent marks alone
do not certify that this exit was reached by the proposed routing. A successful
new proof must use the actual no-Frostman/flag geometry to force one of the
three numbered conclusions, rather than simply relabel the bush return.
