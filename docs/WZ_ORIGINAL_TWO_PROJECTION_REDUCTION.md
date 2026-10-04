# Original two-projection Cartesian reduction

All three implementation sources and their combined imported readback
passed strict Lean 4.33.1 checks. There are 23 public theorem/lemma
declarations. Definitions are excluded. This is a genuine finite reduction
toward the independent Bourgain route; it proves no projection gain or
sum-product expansion.

Let P be the actual delta-separated planar source, and choose two original
slopes lambda0,lambda1 with `h<=|lambda1-lambda0|`, `0<h<=1`, and absolute
slope values at most one. Set `D=(6/h+2)^2` and `L=8/h+4`.

The constructed integer graph records the two actual projected floor
cells of each original point. Same-cell projection errors and the literal
inverse linear system locate any code fiber in a native ball of radius
`3delta/h`. Original point packing therefore proves its cardinality is
at most D. No favorable fiber bound is assumed.

For every actual original query `Q subset P`, its graph satisfies

    |Q| <= D |G_Q|.

If both original projected alphabets have at most `K sqrt(|P|)` cells,
the full graph and its alphabets satisfy

    |A| |B| <= D K^2 |G_P|,
    sqrt(|P|) <= D K |A|,
    sqrt(|P|) <= D K |B|.

Thus the density, and both alphabet retentions, are derived from the
actual original population. `original_graph_witness` and
`real_graph_original_witness` preserve one original point per edge.

The real alphabets send each integer label z to `(delta/4)z`. Their
cardinalities are unchanged, they are separated at mesh delta/4, and they
lie in [-1,1] when P lies in the unit box and delta<=1.

For any other original slope lambda define

    u=(lambda1-lambda)/(lambda1-lambda0),
    v=(lambda-lambda0)/(lambda1-lambda0).

Every original query's constructed real graph has

    |floor_(delta/4) {u a+v b : (a,b) in G_Q}|
       <= L |floor_delta pi_lambda(Q)|.

This follows from an actual original witness, the exact linear identity
for the third projection, the two floor errors, and a direct finite
count of perturbed floor cells. Queries may depend on lambda; the same
two-coordinate map is used for all of them.

Finally the canonical finite Cauchy theorem gives, without an energy
premise,

    |Q|^2 <= D^2 L |floor_delta pi_lambda(Q)|
                 * collisions_(delta/4)(G_Q,u a+v b).

The main declarations are:

- `OriginalTwoProjectionCartesian.small_projections_cartesian_density`
- `OriginalTwoProjectionRealGraph.real_query_cover`
- `OriginalTwoProjectionRealGraph.original_query_collision_energy`

The next proof obligations are explicit. Select the two transverse
slopes across the varying original queries while retaining enough
third-direction incidence mass. Apply the scalar BSG machinery to the
resulting actual linear images, accounting for coefficients that may
shrink separation. The unscaled alphabets' separation alone does not
imply separation of uA or vB. One can either preserve whole original
value fibers or restrict the third coefficients and change the mesh
with the corresponding cover loss. Finally, derive a single
nonconcentrated scalar set with small additive and multiplicative
covering numbers. The current BSG statements do not give that last
conclusion by themselves.

`BourgainGKZFiniteRoute.md` records the exact two target statements,
installed theorem search, and the larger constructive decomposition.
