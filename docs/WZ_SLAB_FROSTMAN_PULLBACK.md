# The next explicit Step 2 lemma: affine slabs and physical direction planes

Read-only continuation, 2026-10-03. Source: WZ Definition 17.3, p. 65; Definition 17.4, p. 66; Proposition 18.1, Step 2, pp. 75–76; the stopping construction it invokes is Proposition 18.2, Step 1, p. 68. No repository changes or new Lean proof claimed.

## 1. Exact geometric statement

Let m=ell-1 and n=d-ell. Let F be an n-by-m real matrix and xi in R^n. An actual incident direction witness satisfies

    theta(phi) = (phi, xi + F phi) + e(phi),   |e(phi)| <= e0 delta.

Use the unnormalized graph direction v(phi)=(theta(phi),1). For a unit vector u in R^m and c in R, consider the actual affine slab

    |u dot phi - c| <= r.

Define the linear subspace

    L = {(w, Fw + xi t, t): u dot w = c t}.

The map (w,t) -> (w,Fw+xi t,t) is injective. Its domain has dimension m+1, and the equation u dot w - c t=0 has codimension one because u is nonzero. Therefore L has dimension m=ell-1.

For a point in the slab, let

    phi_star = phi - (u dot phi-c)u.

Then (phi_star,F phi_star+xi,1) belongs to L and

    distance(v(phi),L) <= sqrt(1+||F||op^2) r + e0 delta.

This is an explicit witness for the distance bound; no closest-subspace projection theorem is needed. The offset xi cancels from the estimate. If F has entries bounded by one, sqrt(1+nm) is a sufficient coefficient.

Normalizing v to a unit direction cannot increase this bound because |v|>=1 and L is linear. If the physical tube axis only passes within C delta of the incident point p, the entire bounded-length tube is contained in a C'(r+delta)-neighborhood of the affine (ell-1)-plane p+L. Thus this applies to the actual tube-plane neighborhoods used in the stopping construction, after a dimensional constant enlargement.

## 2. Original-to-final counting is explicit

Let Phi be the FINAL finite projected direction set at one physical point, with an actual witness map Phi -> T_ref into a SAME-MESH reference tube family. Suppose each tube is selected by at most J projected points, and

    |T_ref| <= D |Phi|.

The bounded witness multiplicity J is geometric: for delta-grid or delta-separated Phi, all preimages of one actual tube lie in an e0 delta-ball around its first m direction coordinates. Grid/packing gives a dimensional bound depending only on m and e0. It is not assumed to be one unless the actual map is injective.

Assume the stopping construction supplies, for every physical (ell-1)-plane Sigma and delta<=v<=rho_cut,

    #{T in T_ref: T lies in N_v(Sigma)} <= A0 v^gamma |T_ref|.

Then for delta<=r<=rho_cut/C', the geometric inclusion above gives

    |Phi intersect slab_r| <= J D A0 (C' r)^gamma |Phi|.

For r>rho_cut/C', the trivial bound gives the same form with constant (C'/rho_cut)^gamma. Thus Phi is slab-Frostman with the explicit constant

    max(J D A0 (C')^gamma, (C'/rho_cut)^gamma).

The ratio D must be proved on the actual final set. For example, same-mesh reference point degree <=A delta^(-kappa) and final projected cardinality >=A'^(-1)delta^(-kappa) give D<=AA'. The earlier combined point/phase partitions can provide these bounds. This argument does not transport a fine-mesh tube count directly into a rescaled coarse-mesh direction count.

## 3. Four-dimensional simplification

In d=4 there are only two possible directional ranks.

- If ell=2, Phi lies in one dimension. Its kappa-AD upper bound and total lower cardinality already imply slab-Frostman: an interval of radius r has relative population at most C K^2 r^kappa. One may take any positive gamma<=min(kappa,1/2), weakened further to match the available tube Katz–Tao exponent. No plane-stopping descent is needed.
- If ell=3, Phi lies in two dimensions. If the small-exponent line-concentration test never triggers, section 2 turns the stopping nonconcentration into the required slab-Frostman bound.
- If that test triggers, an actual affine line in Phi maps by section 1 to a physical 2-plane of directions. Retaining those actual incidences is the input to a rank-two reconstruction. The rank-one case must still be excluded by the extremal multiplicity argument.

Containment in a plane survives an invertible affine rescaling pointwise. It does NOT automatically survive taking the union of several fine points at one coarse point: their planes can differ. The compatible actual-tuple/plane selection must be applied before the coarse incidence image, with its conditioning and thickening losses recorded. The previously constructed compatible plane fields supply the relevant mechanism; an arbitrary coarse image cannot be declared rank two.

## 4. Remaining construction after this lemma

The direct affine-slab pullback is a complete small geometric lemma suitable for a Lean caller. It does not itself prove the entire stopping/reconstruction step.

For the ell=3 to ell=2 branch, the genuinely remaining native caller must preserve the existing k=3 horizontal-grain structure while rebuilding the smaller directional rank. Arbitrary angular or shading cuts can destroy its lower populations. The appropriate proof uses the ORIGINAL higher-grain labels together with phase, spatial-cell and time labels in the SAME final refinement, then derives lower distinct-cell populations with the actual coarse incidence inverse-image bounds. The old upper tube Katz–Tao profile is inherited; its lower AD/product structure must be rebuilt, not presumed hereditary.

The stopping scale cutoff rho_cut and all rank thresholds are chosen before the arbitrarily fine delta. Hence the fixed factor rho_cut^(-gamma) can be absorbed in the final delta-loss. If a rescaling destroys a nonconcentration condition, one must repeat the stopping test on the new SAME-MESH configuration; it cannot be asserted invariant under anisotropic scaling without proof. In dimension four, the terminal rank-two case then has the automatic one-dimensional slab bound described above.

This remains part of the universal auxiliary finite-volume route. It does not replace the original occurrence graph or establish the manuscript's hereditary cap charge.
