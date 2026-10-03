# Step 3: a dense grid fiber forces slope consistency

Read-only mathematical derivation, 2026-10-03. Source: WZ Proposition 18.1, Step 3, printed p. 76, following equation (145). No repository changes or new Lean compilation claimed.

## 1. The actual approximate double representation

Fix one actual height, one lower grain, and write horizontal coordinates as

    (x,u,v) in R^a x R^b x R^n,
    a=ell'-1>=1, b=k-ell'>=0, n=d-k>=1.

Let its lower-grain coordinate set X be a subset of the delta-grid in [-1,1]^a, with

    #X >= lambda delta^(-a),   0<lambda<=1.

The lower representation is, up to its recorded O(delta) point error,

    (x, c+A x, d+B x).

The higher representation says that each of these actual points has an actual higher-quotient witness y_x in Y with normal residual

    v - C x - F u = y_x + O(delta).

Here A=f_1^dagger, B=f_2^dagger, C=f_j1 and F=f_j2. All matrix entries have an explicit fixed bound. There is no assumption that the points fill an interval or an open piece of either plane.

Substitution gives

    y_x = q + D x + e_x,
    q=d-Fc,
    D=B-C-FA,
    |e_x|_infinity <= E delta.                                 (1)

For example, if every block of the lower point error is at most e_L delta and the higher normal residual is at most e_H delta, then

    E <= e_H + e_L(1+a max|C_ij|+b max|F_ij|).

If the higher representation itself is specified by coordinatewise point error rather than its normal residual, first multiply that error by the bounded row-sum factor 1+a max|C_ij|+b max|F_ij|. Thus E is explicit and contains every error from the TWO actual approximate representations. The exact first-coordinate version can omit the a max|C_ij| term, but it is unnecessary to do so.

Assume the ACTUAL set Y obeys the source tube Katz–Tao bound

    |Y intersect T|_rho <= K (tau/rho)^(1-gamma)

for delta<=rho<=tau<=1, 0<gamma<=1 and K>=1. Counts are occupied rho-grid cells, as in the source. The witnesses y_x belong to Y itself; closeness to an unspecified quotient certificate is not enough.

## 2. Freeze a genuine coordinate fiber

Fix a column j of D, and let v_j be that column, with b_j=|v_j|_infinity. Choose a row attaining b_j if b_j>0. Since the other a-1 input coordinates each have at most 3/delta grid values, an actual fixed tuple of those coordinates leaves a scalar fiber of cardinality

    m >= 3^(-(a-1)) lambda/delta.                               (2)

Every member of this fiber is x=x_fixed+delta n e_j for a DISTINCT integer n. Absorb D x_fixed into q. Along this fiber (1) becomes

    y_n=q_j+delta n v_j+e_n,   |e_n|_infinity<=E delta.           (3)

This is a direct finite pigeonhole on original grid points. For a merely delta-separated X, the same argument uses fixed delta-bins in the other coordinates and a dimensional packing factor; their varying contribution adds at most a bounded-matrix multiple of delta to E. The grid version is the smallest formal target and matches the constructed slice coordinates.

## 3. Exact span and output-cell multiplicity

Let n_min,n_max be the extreme scalar indices. Integer spacing gives n_max-n_min>=m-1. In the row attaining b_j, the actual quotient witnesses therefore satisfy

    diameter of their coordinate values
        >= b_j delta(m-1)-2E delta.                            (4)

When the right side is substantial, this supplies a genuine lower output span of order lambda b_j. It does not assert that any intermediate output values occur. If that right side is small, b_j is already at most a constant times E delta/lambda, which is within the eventual bound. The proof below needs only cell counts and works without splitting according to (4).

Choose a dyadic H with

    H >= max(1,E,B0),   H <= 2 max(1,E,B0),

where B0 is a fixed upper bound for all b_j, and put rho=H delta. If rho>=1, the desired slope estimate is immediate from b_j<=B0, after a fixed factor. Otherwise rho is an admissible source scale. If b_j<=rho, it is again already small enough, so suppose b_j>rho.

Two witnesses y_n,y_m in the SAME output rho-grid cell have a coordinate difference at most rho. Equation (3) in the maximizing row gives

    b_j delta |n-m| <= rho+2E delta <= 3rho.

Thus the integer indices in one output cell form a set of diameter at most 3rho/(b_j delta). Its cardinality is at most

    1+3rho/(b_j delta) <= 4rho/(b_j delta),                     (5)

because H>=B0>=b_j. Combining (2) and (5), the actual output image occupies at least

    c_a lambda b_j/rho                                        (6)

DISTINCT rho-cells. This explicitly accounts for all duplicate quotient witnesses and approximate-image collisions. No output injectivity is assumed.

## 4. Compare with the genuine tube profile

All witnesses in (3) lie within E delta<=rho of the segment q_j+v_j[-1,1]. For b_j>rho it is contained in a C_n rho-wide, C_n b_j-long tube. Fixed changes of width and grid scale cost only dimensional covering factors.

If C_n b_j>1, split the bounded-length segment into a fixed number O_(n,B0)(1) of pieces of length at most one; enlarge any very short piece to length rho. Since b_j>rho, each resulting length is at most a dimensional multiple of b_j. The source bound, summed over this fixed cover, yields

    number of occupied rho-cells <= C_(n,B0) K (b_j/rho)^(1-gamma).   (7)

This treats the long-tube endpoint without applying the source KT hypothesis at an inadmissible length greater than one. The case of a fixed width enlargement crossing the top scale is handled by the same bounded cover or the already trivial b_j=O(rho) branch.

Comparison of (6) and (7) gives

    (b_j/rho)^gamma <= C_(a,n,B0) K/lambda.

Therefore EVERY column obeys the determinant-free estimate

    |D|_infinity <= C_(a,n,B0) (1+E+B0) delta
                            * (C_(a,n,B0) K/lambda)^(1/gamma). (8)

The constants can be enlarged to cover b_j=0, b_j<=rho and rho>=1. There is no full-interval assumption. A determinant or a well-conditioned frame is not used.

The direct count at rho=H delta avoids an unnecessary factor H^n from first counting delta-cells and then coarsening the output. Even if E is a recorded subpower error constant rather than a fixed constant, it appears linearly outside the 1/gamma power in this bound.

## 5. Source exponent and the four-dimensional cases

If lambda>=delta^(c_1 eta), K<=delta^(-c_2 eta), and E<=C delta^(-c_3 eta), (8), with fixed constants absorbed after choosing delta small, gives

    |D|_infinity <= delta^(1-C eta/gamma),                      (9)

where 0<gamma<=1 and C records the actual input exponents. Choose eta/gamma small enough that the exponent remains, for example, at least 1/2. This is the power-separated thickening required by the source, rather than an unquantified small-error assertion. If the ACTUAL density is instead lambda=delta^(A eta/epsilon_j), the exact loss is (A eta/epsilon_j+B eta)/gamma, plus any explicit point-error exponent. When only gamma>=epsilon_j is known, this can cost eta/epsilon_j^2. Choose the parameter hierarchy smaller accordingly; do not remove that denominator by renaming eta. The source p. 76 also prints inconsistent shorthand for the grain dimension and the KT exponent, so use the actual count lambda delta^(-a) and the actual deficit gamma in (8).

For d=4, ell'=2 and k=3, all blocks A,B,C,F and D are scalar and a=n=1. No coordinate-fiber pigeonhole is needed: the whole lower grain is the scalar fiber. For ell'=k=3, D has two scalar columns; apply the same one-coordinate argument twice, fixing the other actual grid coordinate. The empty middle block b=0 causes no problem.

## 6. Explicit correction making the two planes consistent

The small-matrix estimate also gives an actual correction map. At a fixed height, keep A,C,F and replace B by

    B_corrected=C+FA.

For each old lower-grain offset pair (c,d), set q=d-Fc. Choose an output mesh Delta at least a sufficiently large constant times delta+|D|. Quantize x,c,q at a fixed finer fraction of Delta, obtaining x_hat,c_hat,q_hat. Define

    p_hat=(x_hat,
           c_hat+A x_hat,
           q_hat+C x_hat+F(c_hat+A x_hat)).                    (10)

Then its LOWER representation is exact, with offset

    (c_hat, q_hat+F c_hat)

and slope (A,C+FA). Its HIGHER representation is exact, with horizontal coordinate

    (x_hat,c_hat+A x_hat)

and quotient q_hat. Thus the consistency identity holds algebraically at every new point.

The map moves each actual old point by at most C Delta, using (1), (9), bounded matrices and bounded old x. A finer quantization plus a fixed residue color gives movement at most the declared output tolerance and Delta-separation, exactly as in the alignment quantizer. The triangular form gives separation directly: if two quantized parameter triples first differ in x, then in c, or then in q, the corresponding first, middle, or last physical block differs by at least the lattice step.

The new q_hat values are within C Delta of the actual old higher quotient witnesses. Conversely each active old higher quotient has a point and therefore a nearby new q_hat. This provides actual bounded-displacement maps for transporting coarse quotient counts, with bounded grid fibers. It does not make arbitrary independently projected sets equal.

The lower corrected field differs from the old lower field by at most C Delta. At working radii r>=Delta its dyadic Lipschitz bound therefore changes by only a fixed constant. No Lipschitz bound on the higher field is required. If the literal coefficient range [-1,1] is needed, a fixed bounded coordinate normalization, or the already permitted bounded auxiliary graph class, absorbs the small coefficient enlargement.

This construction fixes the TWO approximate representations simultaneously. Its remaining native assembly must retain quantitative point/grain counts under coarse-image collisions, one common old-height choice, tube coarsening, and the final combined refinement. Those counts are supplied from original grain/phase/height menus; they are not consequences of the algebraic identity alone. Since Delta/delta is only a subpower factor from (9), its polynomial grid-fiber losses fit the source's enlarged eta/gamma budget. A second arbitrary later pruning must not be asserted to preserve both lower populations.

## 7. Smallest formal target

The next implementable geometric theorem is the scalar grid-image bound (3)–(8): actual integer input indices, actual Y witnesses with a quantified error, an actual interval/tube KT cover bound, and a constructed occupied-cell image with its proved inverse-fiber count. In the d=4 ell'=2,k=3 case it proves the entire nontrivial slope discrepancy estimate. The block substitution (1) is elementary finite matrix algebra, and (10) supplies the explicit correction rather than an assumed consistency certificate.
