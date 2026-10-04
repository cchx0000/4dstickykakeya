# Actual original-ancestor continuation of Lemma 19.2

This is a finite target and implementation ledger. It does not assert that the native Definition 17.2/17.4 configuration has been constructed or that the main theorem has been proved.

## Literal scales and endpoint set

The source uses delta^(1/3) <= rho <= 1 and rho^2 <= sigma <= rho. The finite counting stage uses r=rho^2>0, delta<=r<=sigma, bounded original heights |z|<=1, and original bounded graph-tube segments |t|<=1. Keep sigma on the actual nested parameter grid when using the original dyadic carrier AD lower law.

For a=1 or2 and b=3-a, take the EXACT original deterministic core states reached at depth at most a. Their representatives are genuine original incident points at the unchanged root height z. Let Qr be the occupied r-grid count of their actual first a coordinates, as in OriginalWPhysicalGrowth.scalarCells/planarCells.

The actual sigma-grid count satisfies Qr <= (sigma/r+2)^a Qsigma <= (3sigma/r)^a Qsigma. This is a cover argument over original endpoint coordinates: unaligned grids do not provide a single-valued fine-cell to coarse-cell map. Select one actual core endpoint in each occupied sigma cell and its original representative. Injectivity of the sigma-cell labels implies that these original representatives are distinct. Thus n=Qsigma actual points are available, all at the original height, and Qr*rho^(2a) <=3^a*sigma^a*n.

## Original fine-label map and its derived fibers

For every selected original point p, retain its ORIGINAL Phi_p, original terminal tube t_p, a realizing original fine label phi_p, and its own ORIGINAL affine graph intercept xi_p. Define Near_p={phi in Phi_p: ||phi-phi_p||_max<=rho}. Choose an actual incident tube R(p,phi) realizing each original fine label. Its realization error is <=FineErr*delta.

The actual counting map is

    (p,phi) |-> A_sigma(R(p,phi)),       phi in Near_p.

Here A_sigma(t) is the half-open six-coordinate floor label of the ORIGINAL graph-tube intercept and slope, not a label manufactured from physical box overlap. Full original reference carrier fibers are T_Q={t in T_reference:A_sigma(t)=Q}.

If two tubes have the same A_sigma label, every slope and intercept coordinate differs by at most sigma. Therefore every realizer point p at height z with |z|<=1 and incidence error <=IncErr*delta obeys

    ||x(p) - [base_x(t_Q)+z*u(t_Q)]||_max <= (2+IncErr)*sigma.

Because selected point sigma labels are injective, one ancestor can involve at most

    Cpos=(6+2*IncErr)^a

selected points. At a fixed selected point, every original fine label in one ancestor obeys

    ||phi-u(t_Q)||_max <= (1+FineErr)*sigma.

An upper ball law on the ORIGINAL Phi_p at that radius bounds this direction fiber by Cdir. No upper Frostman/AD law is imposed on the coarse union, and no lower population is asserted after arbitrary restriction. The direct finite map count is

    n*Lrho <= #occupied_ancestors*Cpos*Cdir,

where Lrho is the lower population of each actual Near_p.

For Euclidean original kappa-AD constant KPhi, one valid max-norm ledger is

    Lrho >= KPhi^(-1)*(rho/delta)^kappa,
    Cdir <= KPhi*[2*sqrt(a)*(1+FineErr)*sigma/delta]^kappa.

The factor 2 moves a nonempty ball center to an actual fine label. For radii beyond one, use the original bounded fine population. This factor is fixed when errors and a are fixed; keeping it explicit avoids an implicit norm conversion.

## Full ancestor-fiber physical containment

At EACH p keep its own xi_p. The original terminal tube and each original realizer satisfy

    v(t_p)-xi_p-F(z)u(t_p)=O(DirErr*delta),
    v(R)-xi_p-F(z)u(R)=O(DirErr*delta).

Subtracting gives normal direction gap <=2*DirErr*delta. Different selected points need not have comparable xi. Replacing them by a common coarse xi_q would only give O(rho) and is invalid when sigma<<rho.

The rho-near original fine labels give a tangent slope gap Tang*rho with Tang=1+2*FineErr. Every original fine tube in the same actual sigma parameter cell as R lies in p's adapted box at any dilation

    L >= max(2,
             3+IncErr+2*Tang,
             (1+A)*(3+IncErr)+4*DirErr),

where ||F(z)||<=A. This is proved directly from bounded graph segments and the actual parameter gaps. In particular the ENTIRE original carrier fiber is contained, including tubes not retained in the W core and tubes not incident to p.

The new OriginalWAdaptedBoxes adapter supplies Claim19.3 directly for original deterministic successors and fixed original representatives. It uses E=max(DirErr,2*IncErr); a representative can replace the actual terminal point in its second leg because both remain incident to the original tube at the exact same old height. Hence paths of length a put these endpoint boxes in the root box at dilation Ccomparison^a*L. No physical-overlap implication about slopes is used.

## Exact original-reference CW ledger

Suppose every occupied original ancestor has at least Lcarrier original tubes, and the original global family has Ntotal tubes. The disjoint actual carrier fibers give

    #occupied_ancestors*Lcarrier <= #original_fine_tubes_in_root_box
      <= CW*Vol(root_box)*Ntotal.

For the actual determinant-one adapted root box,

    Vol(root_box) = (2*Lroot)^4*rho^a*sigma^b = Cvol*rho^a*sigma^b.

If the original dyadic carrier AD lower law and global family upper bound give

    sigma^3 <= Kcarrier*Lcarrier*delta^3,
    Ntotal*delta^3 <= Kglobal,

then sigma^3*Ntotal <=Kcarrier*Kglobal*Lcarrier. Combining the three ACTUAL counts and cancelling positive factors yields

    Qr*rho^a*Lrho <=
      3^a*Cpos*Cdir*Cvol*Kcarrier*Kglobal*CW.

Thus, with Qr>=Q*rho^(-a),

    CW >= Q*(rho/sigma)^kappa /
      [3^a*Cpos*Cvol*Kcarrier*Kglobal*KPhi^2*
       (2*sqrt(a)*(1+FineErr))^kappa].

All rho/sigma powers cancel except the required kappa power. This directly uses the original fine family; no thickened-family CW transfer is assumed.

## Remaining native callers and scope

The source configuration construction still must provide the original per-point fine-label realization maps, fine AD bounds, dyadic full reference carrier lower bounds, bounded parameter/global count, and cluster/F direction geometry. Local AD through radius1 alone does not bound an arbitrarily disconnected global parameter family. Likewise carrier-ball AD alone does not give a lower population in every occupied dyadic grid cell; use the original dyadic law or separately construct populated clusters.

The finite raw W→box adapter, ancestor saturation geometry, occupied-cell selection, actual pair→ancestor map, and reference-fiber count are being checked as isolated modules. The actual convexity/volume identity is owned separately. Final native assembly must connect the selected original endpoint witnesses, retained terminal fine labels, their at-most-a original W paths, the primitive original AD laws, and that literal box measure theorem. No theorem here takes the desired final box-density/CW lower inequality as a hypothesis.
