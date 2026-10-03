# Appendix A.3 caller: from original point mass to genuine coarse shadings

This note supplies a constructive finite normalization for the use of WZ Theorem A.3 on pp. 110–111. The positive-power Furstenberg expansion in A.3 remains unproved here. The construction preserves original point witnesses and does not assume that arbitrary restrictions inherit lower AD.

## 1. Why an actual selection is necessary

Appendix A derives a Frostman estimate for the original finite point mass of Y(T), then invokes A.3 at the coarser mesh h=delta_bar. A bound for that point mass does not automatically give the same normalized bound for the distinct occupied h-cells: their original populations may differ. The uniformity of the ambient P bounds how many original points can lie in one h-bin, but alone does not make every occupied Y(T)-bin equally populated.

The following deterministic selection resolves the conversion on a genuine thin graph tube. It uses the one-dimensional longitudinal order of its actual coarse bins.

## 2. Exact cumulative-mass selection

Let a finite ordered sequence of coarse longitudinal bins have nonnegative integer populations w_i, with total W>0 and w_i<=M, where M is a positive integer. Empty bins may be included. Write S_j=sum_(i<j) w_i and define

    e_i = floor(S_(i+1)/M) − floor(S_i/M).

Since 0<=w_i<=M, each e_i belongs to {0,1}. Select bin i exactly when e_i=1. Such a bin is occupied, so choose one ORIGINAL point in it. The number selected is exactly floor(W/M). For any consecutive range of bins i in [a,b), telescoping gives

    #selected in [a,b)
       = floor(S_b/M)−floor(S_a/M)
       <= (S_b−S_a)/M+1.                                 (S1)

No point sampling distribution or new mass is introduced. If W/M>=2, then at least W/(2M) bins are selected.

Choose the heaviest of the three residue classes of the ORIGINAL longitudinal bin index modulo 3. The resulting selected original points are h-separated in the longitudinal coordinate: indices differ by at least three, while each bin has length h. Their total N obeys

    N >= W/(6M).                                         (S2)

The upper interval bound (S1) still holds after this restriction. Negative bin indices are harmless; use the ordered interval containing all occupied bins and the original integer residues.

## 3. Actual Frostman transfer on the thin tube

Assume all original points lie in a bounded-slope h-tube on a common unit slab. For every longitudinal interval of radius r>=h, suppose their ORIGINAL population is at most

    K r^s W,       0<s<=1, K>=1.                          (S3)

Suppose also W/M>=6h^(−s). Then the selected h-separated original set above is an (h,s,13K)-set, up to the fixed constants needed to pass between a longitudinal interval and a physical ball.

For a longitudinal interval of radius r, all bins containing its selected points are contained in its h-enlargement, an interval of radius at most 2r. Equations (S1) and (S3) give at most

    K(2r)^s W/M+1 <= 12K r^s N+1

selected points. By (S2) and W/M>=6h^(−s), one has N>=h^(−s), so the last 1 is at most r^s N. Hence the bound is at most 13K r^s N. A physical ball projects into a longitudinal interval of no greater radius. Conversely, to derive (S3) from a physical point-mass Frostman estimate, a length-O(r) segment of a bounded-slope h-tube lies in a fixed enlargement of an r-ball, yielding only a dimensional factor in K.

The bin population upper bound M is itself geometric. One longitudinal h-bin of a bounded-slope h-tube is covered by C_d balls of radius C_d h. Therefore the ambient point Frostman bound at that actual scale gives

    M <= C_d K_P h^t |P|,

with a ceiling and a harmless fixed enlargement. It is not an assumed equal-population property of the shading.

If literal cubical shadings are needed, move each selected original point to its h-grid cell center and retain the original label. The modulo-three spacing leaves separation at least h after this rounding. The movement is O_d(h), so a fixed thickening of the original tube contains the new cells. The corresponding fixed parameter-grid multiplicities must be divided out explicitly.

## 4. Checking the population threshold in Appendix A

Use the source's notation on pp. 108–111:

    r = delta^(2eta/t),
    sigma = min(t,1)−gamma0,
    a = t−sigma > 0,
    tau0 = delta^(2eta'/a),
    h = delta_bar comparable to C r^(−1) rho,
    m >= c delta^(−(zeta−gamma0)) rho^sigma |P|.

The actual graph pruning gives W=|Y(T)|>=c tau0^2 m. The point Frostman input gives M<=C K_P h^t |P|, with K_P=delta^(−eta). Thus

    W/M >= c tau0^2 K_P^(−1)
               delta^(−(zeta−gamma0)) r^t rho^(−a).       (S4)

Set s_bar=min(a,1), exactly as in the source. Since s_bar<=a and t<=2, multiplying the right side of (S4) by h^s_bar gives the lower bound

    c tau0^2 K_P^(−1)
               delta^(−(zeta−gamma0)) r^2.               (S5)

All comparison constants are fixed. After substituting r and tau0, the power of delta in (S5) is

    4eta'/a + eta + 4eta/t − (zeta−gamma0).

The source chooses eta'=C1 eta and then eta sufficiently small relative to t,a,zeta,gamma0. Make the displayed exponent strictly negative and choose delta last. Then (S5)>=6, proving the required W/M>=6h^(−s_bar). In particular the additive one-point errors in the deterministic rounding are legitimately absorbed; they are not dismissed as a generic subpower loss.

The source's annular bound (232) supplies (S3) with its explicit subpower constant. The selection therefore constructs genuine separated h-shadings with cardinality at least a fixed multiple of tau0^2 m/M and with the same type of Frostman loss. This is the precise coarse-shading conversion needed before the positive-power A.3 estimate.

## 5. Further A.3 input normalization and the remaining theorem

The thickened tube family in Appendix A has a stated multiplicity bounded by a power of r^(−1). Select one actual tube in each occupied h-parameter cell; the loss is that derived multiplicity. The single-scale nonconcentration denominator and the new value w=h sqrt(#T) must be recalculated for the selected family. Since w decreases after selection, the old larger-width upper bound applies, while the denominator loses the same multiplicity factor. This is absorbed by reducing the spacing exponent only after its explicit power is compared with the source's chi.

The separated shadings constructed above may have unequal cardinalities. A dyadic population class retains a logarithmic fraction of tubes. Within that class, thinning each shading to the common lower cardinality costs at most a factor two in its normalized Frostman bound. This produces the comparable actual cardinal N used by A.3. The spacing bound is again normalized by the retained tube population, with the logarithmic loss recorded.

These steps establish actual finite inputs; they do not prove the A.3 expansion

    |union Y(T)|_h >= c h^(−s_bar u_bar/8) N sqrt(#T).

The remaining proof is the genuine planar Furstenberg improvement. The WZ citation points to Orponen–Shmerkin arXiv:2301.10199v4, Theorem 5.61, and its dual formulation. Its multiscale factorization and intermediate-branching estimates must be proved, or replaced by a proved weaker estimate on these actual families. A bare tuple of spacing and shading bounds must not be installed as a final expansion axiom.
