# WZ Step 6: actual slice grids and AD counts

Handwritten mathematical audit, 2026-10-03. Source: Wang–Zakharov, supplied arXiv:2609.22035 PDF, Proposition 18.2, Step 6, printed pp. 72–74, equations (127)–(140). No repository edits or new final-theorem hypotheses are made.

The concrete next geometric lemma is an **injective shear-floor map of actual cubical vertices**, followed by the **dense lattice-fiber quotient AD lemma**. Both have short exact proofs below. The slice AD estimate preceding them can be derived on the SAME final incidence set from actual phase/time partitions, rather than inherited through arbitrary shading cuts.

This is the alternate universal finite-volume route. All original labels, targets and weights remain attached to their images. An auxiliary slice-grid point may move within an explicitly bounded neighborhood of its original target. This does not prove the manuscript's old-root/cross-cap charge.

## 1. Check the correct grain scale before rescaling

Write epsilon=delta_ell and tau=sqrt(epsilon), as in the source's final rescaling. Restrict to a coarse T_tau and apply

    F(x,t)=((x-b_0-a_0 t)/tau,t).

The horizontal unit-scale fibers come from the grain level Delta_j=tau, with thickness Delta_j^2=tau^2, NOT solely from the finest level Delta_J≈epsilon. A tau-long, tau^2-thick grain becomes horizontally unit-long and tau-thick; its time length remains tau. The later text preceding (127) explicitly uses Delta_j=delta_tilde=tau.

A grain containing at least gamma tau^(-ell) distinct tau^2-grid cells maps into at least gamma tau^(-(ell−1)) distinct tau-grid cells, because the previously proved affine rescaling grid map has fiber at most 1/tau. A literal dyadic tau-spatial cube has one tau-time interval. A maximal-net/Voronoi localization only has diameter O(tau) and can meet C_time=O_d(1) such bins. In that case include the actual tau-time-bin label in the class partition below; only after that split do the new cells belong to one horizontal time slice.

Restriction to a particular T_tau must be accounted for before making that assertion. Use the fixed partition label (old grain, T_tau ancestor) in the terminal simultaneous uniform refinement. At most A tau^(-kappa) coarse ancestors can shade the old tau-cube. The fine point multiplicity inside one ancestor is at most A tau^(-kappa). Thus the extra class-count factor and the conditional point-multiplicity denominator cancel, up to the tracked factors A and the uniformity loss, when original class mass is converted to distinct old points. This is the valid caller; arbitrary coarse-tube restriction does not preserve a grain population.

### Exact original-weight / distinct-cell cancellation

Let P be the reference set of DISTINCT old tau^2-grid cells. Suppose the constructed grain-class count is

    N_g <= |P| / (gamma tau^(-ell)).

Let m_0 be a lower bound on original total incidence weight at each reference point, so W>=m_0|P|. Let the eventual final retained mass be at least r_keep W. Let D_tau bound the number of coarse T_tau ancestors meeting a grain's O(tau)-localization, and F_tau bound original incidence weight at one old physical cell WITHIN one such ancestor. The grain/time/ancestor partition has at most

    C_time D_tau N_g

classes. Final partition uniformity with comparison K_g gives every occupied class mass at least

    r_keep m_0 gamma tau^(-ell)/(K_g C_time D_tau).

At one old physical cell, at most F_tau of that original mass belongs to the fixed ancestor. Therefore each occupied class contains at least

    r_keep m_0 gamma tau^(-ell)/(K_g C_time D_tau F_tau)

distinct OLD cells. The matched estimates are

    m_0 >= A^(-1)tau^(-2kappa),
    D_tau <= C_d A tau^(-kappa),
    F_tau <= A tau^(-kappa).

Their powers cancel exactly, leaving at least

    c_d r_keep gamma/(K_g A^3) tau^(-ell)

old cells. The affine rescaling grid fiber bound 1/tau then gives at least

    c_d r_keep gamma/(K_g A^3) tau^(-(ell−1))

DISTINCT new tau-cells. Original incidence weight itself is never divided or changed; division is solely the justified conversion from weighted labels to distinct physical vertices. If labels are finer than tau^2, use their actual image under the pair map (tau^2 physical cell, tau^2 phase tube). Include that pair map as a partition in the terminal uniform call. Its occupied fibers have a common mass up to the explicit uniformity factor, which multiplies both m_0 and F_tau and cancels; absorb the comparison factor into A. This is the required fine-label/coarse-incidence conversion, not an identification of their cardinalities. The actual native geometric packet starts with unit geometric incidence weights.

For the final quantized horizontal fibers, include instead or additionally the label (T_tau, time bin, b), where b is the map (1). A grain/time/ancestor class has at most C_b=O_d(F)(1) possible b-values, so there are at most C_b C_time D_tau N_g such classes. One new grid vertex receives weight at most F_tau/tau, by the old-to-new grid fiber bound, and the shear-floor map adds no collision. Partition uniformity therefore gives EVERY occupied new fiber at least

    lambda_f tau^(-(ell−1)),
    lambda_f >= c_d r_keep gamma/(K_b C_b A^3).

This obtains its population on the SAME final labels as the phase/time uniformity used below. It does not depend on choosing a heavy b-bin afterward.

The resulting grain is approximately horizontal over its one tau-time interval. Indeed a fine tube in T_tau has direction O(tau)-close to the central direction, and is in the original stopping plane up to error O(tau^2). The chosen witness plane differs from that stopping plane by O(tau^2/a), where a is the tuple wedge threshold. If a>=c tau, its central-direction error is O(tau). After F, normal drift over a tau-time interval is O(tau). The hierarchy a=epsilon^v with v<1/2 supplies this range for sufficiently small epsilon. Record this condition rather than treating an arbitrary ell-plane as horizontal after rescaling.

## 2. Exact shear-floor slice map

Let k=ell−1, n=d−ell. Fix tau>0 and a time-bin center z. The actual old horizontal vertices have a common translated cubical grid:

    x=x_0+tau i,  y=y_0+tau j,  i in Z^k, j in Z^n.

Choose the fixed horizontal graph chart from finitely many COORDINATE projection charts, using a largest nonzero minor; a coordinate permutation then gives ||f_z||<=C_d and preserves the lattice. An arbitrary orthogonal rotation would require regridding first and would not preserve exact pre-rotation lattice injectivity. The chosen chart supplies a matrix f_z:R^k->R^n. Define coordinatewise

    b(x,y,z) = tau floor((y-f_z x)/tau),
    Q(x,y,z) = (x, b(x,y,z)+f_z x, z).                         (1)

Do not quantize x or z again. They are already actual common-grid coordinates.

### Movement, injectivity and weights

The floor inequality gives, in every normal coordinate,

    -tau < Q_y-y <= 0.

Thus movement is less than tau in sup norm, or sqrt(n)tau in Euclidean norm. This bound does not depend on f_z.

The map is injective on the old grid vertices. Equal outputs give equal x and z. At that fixed x,z,

    floor((y_0+tau j-f_z x)/tau)
       = j + floor((y_0-f_z x)/tau),

so equality recovers the original integer vector j. This identity handles negative indices and points exactly on grid boundaries. Distinct output vertices are still tau-separated in sup norm: different x or z differ by at least tau, and with equal x,z the normal coordinates differ by a nonzero tau-integer vector.

For an original occurrence space Omega with point map p:Omega->old vertices, use Q∘p and retain Omega itself. The point-map fibers are unchanged because Q is injective; every original weight, tube mark and target remains on its original label. This is stronger than merely bounding duplicate vertices.

The image has the exact form

    Ahat_z = {(x,b+f_z x): b in Y_z, x in X_(b,z)}.

Here Y_z and X_(b,z) are explicitly the finite images/fibers of (1), not a product-decomposition assumption. The shear bound ||f_z||<=F is still needed for comparing quotient boxes to physical balls. It comes from the prior fixed, well-conditioned graph chart.

### Physical target accounting

The original vertex lies in its original tau-cube and the new vertex moves by less than tau in normal coordinates. Thus the new represented points lie in a fixed enlargement of the original cubes, and in fixed-enlargement original tubes. A union of original tau-cubes expands to at most C_d times as many tau-cubes. If the original labels represent finer actual target points, include their already recorded distance to the old cell center. No shading is declared dense outside these represented original labels.

Keep endpoints rather than truncating the image to the old coordinate box. It lies in a fixed enlargement of that box. A fixed dyadic normalization can later restore the chosen bounded chart. Truncating could discard all boundary labels and is unnecessary.

## 3. Bounded movement preserves a proved slice AD estimate

Let A_z be the old distinct horizontal tau-grid vertices and suppose it is (tau,t,K)-AD, with 0<=t<=d−1, in a fixed bounded box. The map (1) is injective and moves each point at most sqrt(n)tau. Therefore, for r>=C_d tau,

    #A_z∩B(a,r−C_d tau)
       <= #Q(A_z)∩B(Q(a),r)
       <= #A_z∩B(a,r+C_d tau).

For tau<=r<C_d tau, use nonemptiness for the lower bound and tau-grid packing for the upper bound. At the large endpoint r≈1, cover the fixed ambient box by finitely many unit balls rather than requesting AD outside its stated range. It follows that Q(A_z) is (tau,t,C_d K)-AD, with a fixed factor depending on the norm convention and bounded box.

There is no weight/cardinality confusion: injectivity preserves the number of distinct old vertices exactly, while original label weights remain separate on those vertices. The next section derives the needed old-slice AD estimate on the final labels themselves.

## 4. Finite same-final-set statement for slice AD

Put D=d−1 and 0<=kappa<=D, t=D−kappa. Work in the actual normalized tau-tube configuration AFTER the already proved geometric closure/rescaling adapters. Let T be the original finite tube backbone, N=|T|. Empty shadings are allowed. Let I be the FINAL set of actual tube/grid-cell incidences; each geometric pair occurs once. The actual packet has unit geometric weights. Any additional original marks or weights remain attached to these pairs and are not substituted for distinct incidence counts.

A point p has horizontal grid coordinate a(p) and tau-time-bin z(p). Let c_r(T) be the actual r-phase ancestor for each working radius r in [tau,1]. The following quantities are actual finite images/fibers:

    point degree d(p) = #{T:(p,T) in I};
    phase/point degree d_r(p,R) = #{T:(p,T) in I, c_r(T)=R};
    H_r(R,z) = #{(p,T) in I: c_r(T)=R, z(p)=z}.

The already constructed bounds used here are:

(a) Aggregate density: |I|>=lambda N/tau.

(b) Carrier AD, with constant K: at most C K N(tau/r)^D occupied r-phase cells, and at most C K(r/tau)^D fine tubes in each such cell.

(c) Matched point multiplicities on this final set:

    A^(-1)tau^(-kappa) <= d(p) <= A tau^(-kappa)

at every occupied point, and

    d_r(p,R) <= A(r/tau)^kappa.

(d) At most C A r^(-kappa) r-phase ancestors shade any physical r-cube. A horizontal r-ball in a fixed tau-time bin meets only C_d such physical cubes.

(e) Self-uniformity, on the SAME final I, of the equivalence relation

    (p,T) ~ (p',T') iff c_r(T)=c_r(T') and z(p)=z(p').

Its comparison factor is K_H.

Conditions (c)–(d) are the concrete pointwise/conditional forms of the earlier common multiplicity estimates (111)–(113), after their finite uniformity adapters. They do not follow from metric carrier AD alone. They are not the desired slice-AD conclusion in another notation.

### The phase/time lower count is constructed

The time window has at most C/tau bins. From (b), the image of the phase/time map has cardinality at most

    C K N(tau/r)^D / tau.

Apply `partition_richness_of_self_uniform` to that map and the actual final incidence set. Conditions (a),(e) give, for EVERY occupied phase/time class,

    H_r(R,z) >= c lambda/(K K_H) (r/tau)^D.                    (2)

In particular, no individual coarse tube shading density or occupied dyadic-cell lower population is assumed as a new premise.

### Lower slice count

At an occupied point p, (c) implies that at least A^(-2)r^(-kappa) distinct r-phase ancestors occur among its incident tubes. For each such ancestor, every incidence in its phase/time class lies within horizontal distance C_d r of p: graph parameters in one r-phase cell differ by O(r), and the physical heights are in the same tau-bin with tau<=r.

The distinct ancestors give disjoint incidence classes. Use (2), sum those incidences, and divide by the upper point degree A tau^(-kappa). This gives

    # {q:z(q)=z(p), |a(q)-a(p)|<=C_d r}
       >= c lambda/(K K_H A^3) (r/tau)^(D−kappa).             (3)

The denominator is the number of incident fine tubes at one spatial cell, not the number of old labels with arbitrary multiplicity.

### Upper slice count

At most C A r^(-kappa) r-ancestors meet the horizontal r-ball, by (d). Each contains at most C K(r/tau)^D fine tubes. One bounded-slope tau-tube visits at most C_d grid cells in a fixed tau-time bin. Thus the number of local incidences is at most

    C_d A K r^(-kappa)(r/tau)^D.

Divide by the lower point degree A^(-1)tau^(-kappa):

    # {q:z(q)=z(p), |a(q)-a(p)|<=r}
       <= C_d A^2 K (r/tau)^(D−kappa).                       (4)

Using a nearby smaller working radius in (3) gives lower counts in the requested r-ball. If all dyadic scales are available, only fixed factors occur. For a finite lacunary list with maximum successive ratio R_mesh, the resulting AD constant is bounded by

    K_slice <= C_d R_mesh^D K K_H A^3/lambda.                 (5)

The endpoint tau<=r<C_d R_mesh tau is handled by nonemptiness and the first available upper-scale estimate. The constant is explicit; one must not interpolate across a large mesh gap for free. With R_mesh<=tau^(-u), its additional loss is tau^(-D u).

Equations (3)–(5) prove the actual analogue of (135) on the same final set. They replace the source's more compressed profile ratios (128)–(134) by concrete finite incidence counts.

Also, each tube contributes at most C_d incidences to one tau-time bin. Hence aggregate density directly gives

    # occupied time bins >= c_d lambda/tau.

This supplies the needed time-set cardinality without assuming it.

## 5. Why the final refinement supplies these hypotheses safely

Prepare all tuple, grid, coarse ancestor, point, time and grain maps before the final simultaneous uniform refinement. Include:

- point fibers, for the final lower point degree;
- every required phase/time map from (e);
- old grain/coarse-ancestor pairs;
- the quantized horizontal-fiber map (z,b) from (1);
- the earlier symmetric relations needed by the common multiplicity/shading arguments.

The fine tube backbone retains its carrier AD bounds. Original conditional and coarse multiplicity upper bounds survive deletion. The point-fiber partition theorem, the original near-extremal multiplicity lower bound, and the tracked total retention give the new final lower point degree; enlarge A explicitly by that retention/uniformity loss. The phase/time lower count is then re-derived by (2) using the FINAL aggregate density lambda.

This is different from transporting a reference slice AD bound through an arbitrary shading cut. All counts in (2)–(4) use the final incidence set.

An old horizontal grain, after the rescaling in section 1, lies within C tau of one affine plane with slope f_z; replacing its slope by the representative f_z changes its normal residual by O(tau). Therefore its points meet at most C_d(F) quantized b-cells. Thus the number of occupied (z,b) fibers is bounded by a fixed multiple of the recorded old grain/coarse-ancestor class count. Include that partition in the same final call to obtain quantitative weight in EVERY occupied new fiber. Divide by the corresponding conditional fine-point multiplicity to obtain the distinct-vertex bound

    |X_(b,z)| >= lambda_f tau^(-k),

with the explicit previously tracked grain, multiplicity and final-uniformity losses in lambda_f. The shear-floor map itself contributes no collision denominator. One must retain the earlier affine-rescaling factor 1/tau when converting tau^2-cells to tau-cells.

No extra uniform-refinement call after these conclusions is harmless automatically. If further finite relations are needed, include them in this same terminal call, or re-establish the population and density bounds with its actual loss.

## 6. Dense-fiber quotient AD: a complete geometric lemma

Let A={(x,y+fx): y in Y, x in X_y} be the explicit output of (1), in a fixed bounded box, with ||f||<=F. Suppose it is (tau,t,K_A)-AD and each occupied fiber satisfies

    |X_y| >= lambda_f tau^(-k).

The x and y coordinates lie on their stated tau-lattices. The shear and inverse shear are bi-Lipschitz with constants depending only on d,F; transfer the AD bounds to the unsheared product coordinates with these explicit fixed factors.

If 0<=k<=t<=d−1, then Y is (tau,t−k,C_(d,F) K_A/lambda_f)-AD.

**Lower bound.** Center an ambient r-ball at an actual (x,y) in A. Its at least K_A^(-1)(r/tau)^t points project into an O_(d,F)(r)-ball about y. One fiber contributes at most C_d(r/tau)^k points because x is on a tau-lattice. Divide. Use a fixed smaller radius for the desired y-ball; handle r≈tau by nonemptiness.

**Upper bound.** For y' in B(y,r), take ALL of its globally dense fiber, contributing at least lambda_f tau^(-k) points. Cover the bounded x-domain by at most C_d r^(-k) boxes of diameter r. Above one such x-box and B(y,r), the unsheared points fit in a fixed multiple of an r-ball centered at an actual point if nonempty. Ambient AD upper counts then give

    lambda_f tau^(-k) # (Y∩B(y,r))
       <= C_(d,F) r^(-k) K_A(r/tau)^t.

Rearranging gives the upper bound. No separate quotient uniformity assumption is used, and no density is asserted for the intersection of a fiber with an arbitrary small x-ball.

For an exact integer-grid statement, take tau=1/N, |x_i|<=N, 1<=R<=N. A fiber contributes at most (2R+1)^k<=3^k R^k locally. Partition the x-domain into at most (3N/R)^k blocks of diameter R; each product with a y-ball of radius R fits a 2R-ball at an actual point. With ambient bounds c R^t and K R^t, the quotient bounds are

    (c/3^k) R^(t−k) <= #Y_ball <= 3^k 2^t (K/lambda_f) R^(t−k).

These are the worker's finite geometric formalization targets.

### Exponent range, including the finite-scale obstruction

If t<k, do not announce a nonnegative (t−k)-AD exponent. One single dense fiber and the ambient upper bound at a fixed radius imply

    lambda_f tau^(-k) <= C_(d,F) K_A tau^(-t),

so

    k−t <= log(C_(d,F) K_A/lambda_f)/log(1/tau).

If K_A<=tau^(-u), lambda_f>=tau^v, this is k−t<=u+v+o(1). A fixed positive gap k−t is impossible once the construction's slack is chosen below that gap. At one finite scale only this quantitative bound is justified. In the universal contradiction argument, kappa is fixed and there are finitely many possible k; choose the input loss below any relevant positive gap, or pass through the finite-dimensional stopping cases explicitly.

## 7. What is already in the repository and what remains genuinely geometric

Read-only inspection of the current repository found:

- `Thm_StickyKakeya4_uniform_grain_partitions.lean:15`, `partition_richness_of_self_uniform`, gives (2) directly after the phase/time image bound; line 66 gives the simultaneous final constructor.
- `Thm_StickyKakeya4_tube_bin_count.lean:88`, `timeBins_card_mul_scale_le`, supplies the C/tau time-bin bound. `spatialBox_card` at 107 and `gridBin_mem_tubeBins` at 111 supply the per-tube per-time-bin spatial-cell bound.
- `Thm_StickyKakeya4_wz_carrier_pruning.lean:353`, `exists_maximal_image_separated_subfamily`, constructs the actual carrier net. Lower-AD populations in disjoint half-radius balls bound its cardinality; each net ball meets only C_d dyadic r-phase cells. This derives the occupied phase-cell estimate in (b). The short quantitative lower-AD/disjoint-ball caller is still needed; `exists_cover_cell_assignment` at 5763 does not supply that cardinality by itself.
- `finite_partition_card_bound_on_cells` at 3426 handles the final finite partition counts; projected/separated local-cell counting appears at 5479ff. Those tools do not by themselves establish tube geometry or the matched-multiplicity bounds.
- The certified affine grid-rescaling and incidence-bin-transfer modules supply the earlier 1/tau mapping-fiber bound. It must not be confused with the injective shear-floor map of section 2.

The next new formal lemma should therefore be the actual integer shear-floor grid map, or the integer product-grid quotient count of section 6. The mass pigeonhole in (2) is already covered by a compiled theorem; a new abstract wrapper would not address the geometric gap.

The multitime clause of Definition 17.2(3), concerning the union of Y_z over a coarse height interval at its coarse resolution, is a further caller. Individual Y_z AD bounds do not imply it. At a coarse height interval of size rho, use the actual coarse incidence image and a common slope representative (the compatible field varies by O(rho)); repeat the phase/time and quotient construction at mesh rho. The needed image-fiber counts and represented-target enlargement must be verified on those actual coarse maps, not assumed as a global grains certificate.

## 8. Checks

400 exact-rational shear-floor tests passed, including translated grids, negative indices, variable bounded matrices, and boundary values: all images were injective and all normal movements were less than tau. Another 400 finite dense-fiber quotient tests passed for both t>=k and the finite-slack t<k case. These are independent sanity checks; this note does not claim Lean verification of the full geometric adapter.
