# Asymmetric additive construction on the original sets

This checkpoint proves a finite asymmetric additive-energy construction, then
transfers it to literal separated real input sets. It supplies a substantive
input to the additive portions of the auxiliary WZ volume route. The radial
and Furstenberg expansion inputs are separate.

## Constructed finite chain

Starting with the original energy, the construction forms actual symmetry
sets and actual original difference fibers. A finite slow-growth chain
produces one balanced core using the existing proved balanced BSG theorem in
LeanFormalizations. It does not introduce an asymmetric BSG axiom.

The backward construction selects original X points, retaining the complete
selected original fibers. A rich-translate argument and a maximal disjoint
translate cover then select original Y points. Plünnecke–Ruzsa bounds the
literal iterated sum-difference sets of these same subsets. Neither original
set is replaced by a comparably sized independent sample.

`finite_asymmetric_original_subsets` constructs the chain stage, original
subsets, their retention coefficients and every iterated sumset bound from
the original energy alone. The stage and core are outputs. Explicit checks
bound the balanced growth constant by `K * kappa^58 <= 2^192`.

## Literal real input and quantitative losses

Closed near-collisions at distance at most delta pass through floor rounding
with a factor five. Delta separation retains the exact original cardinality,
including the boundary case. The real output subsets are actual preimages
inside the original input sets. Their real iterated sumsets occupy at most
`2(n+m)+3` floor cells per exact integer sum label.

`original_real_subsets` composes those facts with the finite construction.
It starts with actual separated real X and Y and their approximate difference
energy; no rounding-energy or original-subset certificate is an input.

The native scale budget is also constructed. For energy parameter nu in
`(0,1]` and dyadic mesh level N, the common chain density has a lower bound
of the form `c_J * nu^(2^J+1) / (N+5)`, with fixed chain depth J. Its input
cardinality bounds follow from actual bounded support and separation.
The original retention and growth coefficients have explicit polynomial
bounds in this common density and the J-th root of the sole original-size
ratio. This avoids multiplying an inverse cardinality-ratio loss at every
backward step.

The final native dyadic caller `original_real_dyadic_bsg` now absorbs all
these losses. For every positive epsilon it chooses an integer K and mesh
threshold before nu, uniformly for `0 < nu <= 1`. It returns original subsets
with `nu^K delta^epsilon` retention and every iterated floor-cover bound,
including zero multiplicities. It assumes only actual bounded separated
inputs and the original closed near-difference energy.

This bounded dyadic result does not need the extra `|Y| <= |X|^C` hypothesis.
Consequently the preliminary lower bound in WZ Claim13.8 is unnecessary solely
for entering BSG in this native route. The later dense four-cycle identity
and radial expansion are still required. The scope is sufficiently fine
dyadic scales and `nu <= 1`; a literal all-scale/all-nu version of the printed
lemma is not asserted.

## Verification and remaining route

Twenty-four new modules contain 156 new proved declarations. Their strict
source checks, proper-import axiom readback, full default build, and exact
source hashes are recorded in
`verification/wz-original-asymmetric-checkpoint.json`.
The previous 302 source hashes are unchanged.

The generic finite construction works in an additive commutative group. The
real rounding endpoint in this checkpoint is one-dimensional. Section21's
vector-valued use requires its own planar rounding and covering adapter;
it is not justified by renaming the scalar endpoint.

This is an input to the three-branch route recorded in
[the configuration ledger](WZ_FOUR_DIMENSIONAL_BRANCH_LEDGER.md).
It does not prove Theorem13.5, AppendixA.3, the Section22 radial theorem, or
the final compact marked-family theorem. The final theorem still has the
preexisting `wang_zakharov_published_volume_estimate` dependency.
