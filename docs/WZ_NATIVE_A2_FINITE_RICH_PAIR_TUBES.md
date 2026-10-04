# Native Appendix A.2: finite original-pair tubes

Primary source: WZ printed pp.106–107, Lemma A.2 and (210)–(212). This note treats the native range 0<epsilon1<1/8, 0<t<=2. Appendix A.3's independent positive-power gain is not assumed or proved here.

## 1. Literal finite source geometry

Let P be a nonempty finite subset of [-1,1]^2. For each ordered distinct pair (p,q) in P^2, set

    M=max(|q_x-p_x|,|q_y-p_y|)>0,
    n(p,q)=(-(q_y-p_y)/M,(q_x-p_x)/M),
    c(p,q)=n(p,q) dot p.

The normal is derived from the ACTUAL original pair direction, has infinity norm one, and its line contains p and q exactly. Define the bounded-source strip support

    S_i(w)={z in P: |n_i dot z-c_i|<=w}.

If z is within coordinate distance Delta of a genuine point on the original pair line, then z belongs to S_i(2Delta), since each normal coefficient has magnitude at most one. In particular a physical Euclidean Delta-tube is covered by this normalized strip. This fixed factor two must be included when returning to the paper's physical tube scale.

Only the finite candidate family {(p,q) in P^2:p!=q} is needed. No uncountable collection of all continuous tubes is selected.

## 2. Select representatives using ACTUAL common P-points

Keep the actual rich candidates with |S_i(w)|>=lambda|P|. Define two labels i,j to be compatible if all p,q in S_i(w) intersect S_j(w) have infinity distance at most rho. This relation is symmetric in the tube labels.

Choose an inclusion-maximal finite compatible subfamily F. The constructor proves:

* F consists of original rich pair-tube labels
* all distinct chosen supports have the stated common-point diameter bound
* for every omitted rich label i, there is j in F and two ORIGINAL points p,q in S_i(w) intersect S_j(w), with infinity distance greater than rho

This strengthens the source's choice of long continuous intersections: maximality itself supplies the two actual point witnesses needed for the geometric argument.

If the original metric profile bounds every rho-ball centered at a point of P by epsilon|P|, every distinct chosen overlap has cardinal at most epsilon|P|. For a nonempty overlap choose one of its actual points as center; the diameter condition puts all remaining common points in its ORIGINAL rho-ball. Empty overlaps cost zero. No AD lower bound is inherited through a restriction.

## 3. Rich-family cardinality, with the diagonal kept exactly

Let N=|F|, M=|P| and I=sum_(i in F)|S_i(w)|. Original incidence Cauchy and the actual pairwise support count give

    I^2 <= M I + epsilon M^2 N^2,
    lambda M N <= I.

The diagonal in the second moment is I, not NM. If 0<=epsilon<=lambda^2/2, then

    I^2 <= M I + I^2/2,
    I<=2M,                   lambda N<=2.

These estimates include N=0. Their finite proof constructs and counts the original support incidences; no numerical incidence bound is supplied as a certificate.

## 4. Exact planar strip bounds

For normalized normals n=(a,b), n'=(c,d), write D=ad-bc. Every coefficient has magnitude at most one. If p and q are in both width-w strips, then actual residual subtraction gives

    |D| |q_x-p_x|<=4w,       |D| |q_y-p_y|<=4w.

Thus a genuine overlap witness with infinity distance>rho gives

    |D|<=4w/rho.

If |D|>=theta>0 instead, the entire common support lies in the point-centered infinity ball of radius 4w/theta about any actual common point.

For the containment step, let p be one actual common point, let z belong to the first strip, and suppose both lie in the original square. A coefficient of n has magnitude one. If |a|=1, use the exact identity

    a R'(z)=c(R(z)-R(p))+D(z_y-p_y)+a R'(p).

If |b|=1, use its x-coordinate analogue. Since |z_x-p_x|,|z_y-p_y|<=2, this proves

    |R'(z)|<=3w+2|D|.

Combining with a long-overlap witness, for 0<rho<=1,

    |R'(z)|<=11w/rho.

The bound is explicitly width/separation. The simplification to a constant times rho is valid only after substituting the native w=2rho^2, giving width 22rho. The finite bounded source domain is responsible for the factor two in the residual identity. No conditioning, angle-center substitution, or full-interval hypothesis is used.

The verified native strip caller constructs F and its representative for each rich candidate, derives the overlap cap from ORIGINAL ball counts, and proves both I<=2|P| and lambda|F|<=2. It then proves the 11w/rho containment for every original point of the candidate support.

## 5. Use ONLY selected representatives in the transverse count

Put W=11w/rho and thicken each SELECTED representative line to width W. Define P_tr as the actual points in P lying in two such thick strips whose normalized determinant has magnitude at least theta.

For each pair of selected labels, the intersection lies in an actual ball of radius R=4W/theta. If the ORIGINAL R-ball profile is at most zeta|P|, finite union counting gives

    |P_tr| <= zeta|P| N^2 <= 4 zeta|P|/lambda^2.

This uses the family F, of controlled cardinality, throughout. The source text after (211) says that the widened family corresponds to all of T0; taken literally this would not justify its |T|^2 bound in (212). The actual construction here widens only the selected representative family, and assigns every rich candidate to one of those representatives.

For p outside P_tr, either no widened representative contains p, in which case no rich candidate passes through p, or choose one actual active representative j0. Every other active representative j has |det(n_j,n_j0)|<theta. Applying the same one-common-point residual identity at width W shows that all its original points lie in the single j0-strip of residual width

    B=3W+2theta.

Therefore every rich partner q of p lies in that same B-strip. The original two-ends profile controls this whole original point set; no conditional or coarse-union Frostman assertion is inferred.

Remove transverse rows, the partners in the root strip, and the diagonal. The resulting actual G subset P^2 consists of distinct pairs whose physical thin pair tube has fewer than lambda|P| original points.

## 6. Native exponents and every query radius

Take

    theta0=delta^epsilon1,
    rho0=theta0^2,
    physical Delta0=theta0^4,
    w=2Delta0,
    W=22rho0,
    theta=theta0/8,
    R=4W/theta=704theta0,
    lambda=delta^chi.

Assume theta0<=1/1408. Then R<=1/2 and rho0<=1/2, while

    B=3W+2theta=66theta0^2+theta0/4 <= theta0/2.

A normalized strip of residual width B has physical full perpendicular width at most theta0, because the Euclidean norm of its normal is at least one. Its intersection with [-1,1]^2 is covered by four unit-length tubes: the longitudinal coordinate of an original point lies in [-2,2], partitioned into four closed unit intervals. Thus the original two-ends assumption at physical width theta0 gives at most 4delta^epsilon2|P| partners in each nontransverse row.

For infinity balls of radius r<=1/2, use the ORIGINAL Euclidean Frostman bound at radius 2r. Since t<=2, the resulting constant is at most 4delta^(-chi). The required radii rho0 and R are both at least delta when epsilon1<1/8. The same conversion at r=delta bounds the diagonal fraction by 4delta^(t-chi), once delta<=1/2. No ball count is queried below the original delta mesh or above the allowed unit radius.

The rich overlap parameter is

    epsilon=4delta^(-chi)rho0^t.

The absorption condition epsilon<=lambda^2/2 follows from

    8delta^(2t epsilon1-3chi)<=1.

The transverse fraction is at most

    16*704^2 delta^(t epsilon1-3chi).

Consequently the total bad-pair fraction, including the actual diagonal, is at most

    16*704^2 delta^(t epsilon1-3chi)
        +4delta^epsilon2+4delta^(t-chi).

If 0<chi<=t epsilon1/12, this is bounded by delta^q, q=min(t epsilon1/2,epsilon2/2), for sufficiently small delta depending only on t,epsilon1,epsilon2. The threshold can be chosen UNIFORMLY in chi: it suffices, in addition to theta0<=1/1408, to impose

    delta^(7t epsilon1/4)<=1/8,
    delta^(t epsilon1/4)<=1/(48*704^2),
    delta^(epsilon2/2)<=1/12,
    delta^(t/2)<=1/12.

These are explicit finite conditions with positive exponents. They imply the native Lemma A.2 conclusion and match the later A.1 order: t,epsilon1,zeta fixed first; chi chosen as a fixed sufficiently small multiple of t epsilon1; delta last, uniformly for smaller positive chi.

## 7. Native source caller is now formally assembled

`NativeA2WeakRadialCaller.native_weak_radial_graph` derives the actual graph from the ORIGINAL Euclidean ball Frostman profile and the ORIGINAL physical unit-tube two-ends profile. Its conclusion counts `physicalPairTube Pts (delta^(4*eps1)) (p,q)`, the original points lying at Euclidean distance at most that radius from the genuine affine line through the original ordered pair. Every retained pair is distinct. No intermediate ball-cap, representative-family, incidence, graph-cardinality, or strip-containment certificate is a caller hypothesis.

`NativeA2WeakRadialCaller.exists_uniform_native_weak_radial_graph_threshold` proves the native quantifier order: for fixed `0<t<=2`, `0<eps1<1/8`, `eps2>0`, there is one positive threshold `d`, independent of `chi`, such that every `0<delta<=d` and `0<chi<=t*eps1/12` works. The resulting graph has cardinality at least `(1-delta^min(t*eps1/2,eps2/2))*|P|^2` and every retained physical pair tube has strictly fewer than `delta^chi*|P|` original points.

The complete A.2 source chain has 48 proved declarations across 16 modules:

- `PlanarStripIntersection`: 7
- `FiniteCommonPointTubeRepresentatives`: 2
- `RichFamilyIncidenceBound`: 4
- `NativeRichStripRepresentatives`: 2
- `OriginalPairStripGeometry`: 5
- `NativeRichPairTubeFamily`: 1
- `TransverseOriginalStripPoints`: 4
- `OriginalPairRowCut`: 1
- `NativeWeakRadialPairGraph`: 1
- `FourUnitTubeBandCover`: 3
- `PlanarFrostmanBallConversion`: 4
- `PhysicalWeakRadialPairGraph`: 1
- `NativeA2PowerBudget`: 4
- `NativeA2ParameterIdentities`: 4
- `OriginalPhysicalPairTube`: 3
- `NativeA2WeakRadialCaller`: 2

All module source files are in `/tmp`, with no repository edits. The first twelve modules and 35 proofs were recovered with prior strict source and independent imported axiom readback logs. The final four modules and thirteen proofs strict-compiled on restored official Lean4.33.1, `-j1 -DautoImplicit=false -DwarningAsError=true`. The aggregate imported readback is `/tmp/NativeA2CompleteReadback.lean`; its final validation status is recorded in `/tmp/WZ_NATIVE_A2_VERIFICATION_MANIFEST.json`.

This result covers the native epsilon range used by Theorem A.1. It does not claim the literal arbitrary-positive-eps1 extension of Lemma A.2. The later A.1 application at (214) requests a fixed `C0` dilation; a separately packaged fixed-dilation adapter is not included here. Theorem A.3's positive-power Furstenberg gain remains independent and unproved by this work, so this does not complete Theorem A.1 or the final sticky Kakeya theorem.

Primary source rechecked through official arXiv: https://arxiv.org/pdf/2609.22035, printed pp.106–108. The physical tube and original graph conclusions match Lemma A.2 in the native parameter range. The representative-only widening and original point-witness selection above make the finite implementation explicit without relying on the wording issue after (211).
