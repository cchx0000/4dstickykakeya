# Native A.1 original graph selection and the exact A.3 boundary

Primary source: Wang–Zakharov, arXiv:2609.22035v1, printed pp.108–112. Local text: `/workspace/scratch/5f2524fd4117/paper-audit/wang-zakharov-2609.22035.txt`. This checkpoint adds independent finite reductions after the frozen55. It does not assume A.3, an incidence gain, or a projection theorem.

## 1. New finite original-input results

The new source chain consists of:

1. `OriginalPhysicalTubeScaleSelection.lean` — physical tube monotonicity; exact original support cardinality bounds; explicit dyadic covering of every radius; selection of an actual maximal physical tube score; selection of one original scale-and-occupancy graph fiber
2. `OriginalDensestTubeControl.lean` — finite menu bounds; control of every larger physical radius, including nondyadic radii; conversion of an actual continuous-radius violation to a large maximal score
3. `NativeRadialDensestGraph.lean` — choice of a dyadic mesh comparable to the arbitrary original delta; native densest original graph construction
4. `OriginalRadialNearDiagonal.lean` — legal original separation-radius query and exact power identity; construction and count of the actual separated original subgraph
5. `NativeRadialScaleConsequences.lean` — the explicit selected-scale bound (217); physical reciprocal-width nonconcentration (220)

There are fourteen proved declarations. Strict source and independent imported verification are recorded in `/tmp/WZ_NATIVE_A1_SELECTION_MANIFEST.json`.

### Near-diagonal removal (215)

For `0<delta<=1`, `0<t`, and `0<=eta<=t/2`, the theorem proves that `r=delta^(2*eta/t)` lies in `[delta,1]` and that `delta^(-eta)*r^t=delta^eta`. From the original point Frostman profile it constructs `H subset G` with every actual endpoint distance at least r and

`|G| <= |H| + delta^eta |P|^2`.

This counts original pairs. All earlier physical tube properties survive by literal subgraph inclusion.

### Exact original densest-scale selection (217)-(220)

The dyadic radii are `q_j=2^(-j)`, `0<=j<=n`. The mesh constructor proves existence of n with `delta<=q_n<=2delta`. Each pair chooses a maximizer of

`score(p,p',q) = #(P intersect physicalPairTube(p,p',q)) / q^sigma`.

The omitted common factor `1/|P|` does not alter a maximizer. All counts use the original P. For a nonempty original graph G in which every pair has an actual violation at some `R in [delta,1]`,

`#(P intersect T_pair(R)) >= delta^(-zeta) R^s |P|`,

the native constructor produces one actual rho in `[delta,1]`, an occupancy index j, and a nonempty original subgraph H with

- `|G| <= (n+1)(1+floor(log_2 |P|)) |H|`
- `m=2^j <= #(P intersect T_pair(rho)) < 2m` for every original pair in H
- `delta^(s-sigma-zeta) rho^sigma |P| <= 2^(sigma+1) m`
- `delta^(s-sigma-zeta) rho^sigma <= 2^sigma`
- For every `rho<=R<=1`, `#(P intersect T_pair(R)) <= 2^(sigma+1) (R/rho)^sigma m`

The scalar consequence for `sigma>0` is

`rho <= 2 delta^((zeta-s+sigma)/sigma)`.

For `s-sigma=gamma`, these give the exact native versions of (217), (219), and (220), with the complete dyadic constants. The reciprocal-width theorem directly proves the same physical count at `R=rho/tau`, `rho<=tau<=1`.

The graph retention keeps the exact `log |P|` factor. Converting that into `O(log(1/delta))` uses the original bounded-domain delta-separation packing bound, not a lower-cardinality or conditional Frostman premise. This conversion is not silently assumed here.

## 2. Earliest independent geometry still unformalized

The first still-unformalized source construction after this checkpoint is Step2's annular tube cover and charge, (221)-(223). It must construct the actual angular rectangles in the annulus, establish bounded overlap, and charge each rich rectangle to original P ball counts. For its partner class S_i it must use an actual original witness pair, endpoint separation at least r, and genuine physical containment in the corresponding wider pair tube before applying the proved (220). The numerical inequalities alone are not a substitute for those objects.

Other independent obligations before the deep theorem are:

- Sum the two endpoint annular exclusions using the actual dyadic scale menu to construct G3; prove (226)-(227) for original P, including the innermost mesh ball
- Construct actual angular representatives and prove bounded physical tube incidence outside the root ball, yielding (228)
- Perform two-sided pruning on the original forward and reverse direction-class maps; count each removed class once and construct a stable G4, rather than selecting a dense row once and assuming reverse degrees remain large
- Construct a finite physical tube cover of the original pair tubes, thicken it from rho to `bar_delta ~ r^(-1) rho`, and prove the claimed `O(r^(-2))` multiplicity; any thinning must keep its original pair assignment
- Construct actual shadings Y(T) from G4; derive both their original-point lower count and their original annular profile, with no inheritance of conditional AD regularity
- Count actual distinct two-step original pairs for the upper tube bound (235); bounded tube multiplicity must be charged when summing these counts
- Construct the physical containment used for (238), and normalize its cap by the actual retained tube-family cardinality

Two radius-boundary details should be kept explicit in the Step2 implementation. When the thick width `r^(-3)*rho` exceeds the annular radius tau, an actual angular cover uses `O(max(1,r^3*tau/rho))` pieces; the smaller expression alone cannot count a nonempty finite cover. The rich-rectangle charge can still use bounded overlap, so this does not require a new gain theorem. Also, the ball radius `2*tau` may exceed one: extend the original profile there with the trivial full-P count, rather than querying a profile stated only up to one. For partner-tube widths exceeding one, combine the trivial full-P bound with the proved original lower occupancy estimate; do not apply the `[rho,1]` maximality theorem outside its range.

These are independent finite/geometry reductions, not applications of A.3. They remain open in this checkpoint. No shaded tube configuration satisfying them is supplied as a premise of a claimed native A.1 theorem.

## 3. The first genuine A.3-dependent assertion

After the preceding geometry and the contradiction hypothesis `|G4|>=delta^eta|P|^2`, the first genuinely deep input is the positive-power union bound in Step4:

`|union_T Y(T)|_(bar_delta) >= c bar_delta^(-s_bar*u_bar/8) N sqrt(M)`,

where M is the actual essentially distinct retained tube count and N is the actual common shading covering-number scale. It is not the construction of the graph, the scale maximization, the annular estimate, or the one-scale spacing cap. This union lower bound is precisely the missing A.3 strength.

The elementary pairwise-overlap endpoint engine in the repository does not furnish it for the native small shading exponent. In particular, when the original point dimension t<=1, the shading exponent below is gamma, which can be arbitrarily small. No argument here replaces this assertion with an assumed gain certificate or an s=1 result.

## 4. Exact parameter and original-scale interface

Distinguish the original point dimension t from the tube-family dimension t_bar:

- `s=min(t,1)`
- `gamma=min(zeta/100,s/2)>0`
- `sigma=s-gamma>0`
- `a=t-sigma>=gamma`
- `s_bar=min(a,1)>=gamma`
- `chi=c0*t*eps1`, fixed before the error parameters
- `eta'=C1*eta`, with C1 fixed from t,zeta
- `r=delta^(2*eta/t)`
- `tau0=delta^(2*eta'/a)`
- `bar_delta` is an actual dyadic thickening comparable to `r^(-1)*rho`
- `M=|T|=bar_delta^(-t_bar)` defines t_bar from the ACTUAL family after any necessary thinning/regularization
- `w=bar_delta*sqrt(M)` must be recomputed if that family changes

The source aims to derive

`delta <= bar_delta <= delta^c`, with fixed `c=c(t,zeta)>0`,

`t_bar in [chi/2, 2-gamma]`,

`u_bar=min(chi/4,gamma/2)>0 <= min(t_bar,2-t_bar)`,

and the original one-scale cap `#T[T_w]<=delta^chi M<=bar_delta^u_bar M`.

The constants, multiplicity losses, and any dyadic regularization losses require slack in these bounds. Removing a fraction of the tubes changes M, t_bar, w, and the normalized cap simultaneously; none should be frozen at its pre-refinement value.

For a fixed tube multiplicity exponent A, the shading Frostman constant before fixed factors is

`r^(-A)*tau0^(-2)*delta^(-eta')`

`= delta^(-[(2A/t)*eta + (4/a+1)*eta'])`.

Writing `alpha=log(bar_delta)/log(delta)`, the scale range gives `c<=alpha<=1`. Thus a delta-loss `delta^(-L*eta')` becomes `bar_delta^(-L*eta'/alpha)`, bounded by `bar_delta^(-L*eta'/c)`. This is the required original-to-working-scale conversion; the sign and the factor 1/c matter.

A future engine must provide A.3's admissible Frostman-loss exponent AND small-scale threshold uniformly over the compact varying t_bar range (with s_bar,u_bar fixed, or over the corresponding compact parameter set). Pointwise positivity of `eta_A3(s_bar,t_bar,u_bar)` alone does not establish a positive uniform infimum.

## 5. Covering-number and uniformity contract

Definition3.1 of the paper defines a finite `(delta,s,C)` set by ORIGINAL point counts in balls. It must not be silently replaced with a normalized coarse-cell Frostman condition. A faithful engine can accept that original count formulation together with actual shading covering numbers. If the eventual deep engine is instead formulated for separated coarse cells, its reduction from weighted original point shadings needs proof.

The lower covering count `|Y(T)|_(bar_delta) >= c tau0^2 m / M_P(bar_delta)` uses an upper population bound for an ORIGINAL P ball/cell. It does not give a lower population in every partially occupied Y(T) cell. Conversely the relation between `|P|`, `|P|_(bar_delta)`, and `M_P(bar_delta)` uses the original global `(delta,delta^(-eta))` uniformity. Neither may be inferred by conditioning P on a tube or on G4.

A.3 also asks for comparable actual shading covering numbers N. Dyadic selection of tube labels by these numbers preserves their original shadings but loses tube mass. The normalized spacing cap and essential-distinctness must be rechecked for that retained family. Arbitrarily taking N cell representatives per shading does not automatically preserve its normalized Frostman profile.

## 6. Quantifier order for the eventual native conclusion

Fix `t,eps1,zeta`, hence gamma,sigma,a,chi and the compact deep-engine parameter range; choose C1 and a sufficiently small internal loss budget; choose its deep-engine losses; then fix small eta and eta'=C1*eta. The final small delta threshold also depends on eps2 and the fixed physical dilation.

For the original statement's uniformity over every smaller supplied eta, fixed constants and logarithms cannot be absorbed via `C<=delta^(-c*eta)` uniformly as eta tends to zero. A clean assembly can select one fixed internal eta_star depending only on the fixed parameters, weaken every original profile with supplied eta<=eta_star/2 to eta_star, run the proof with that fixed budget, and obtain an exceptional-pair power at least eta_star/2. This is stronger than the target supplied-eta power and allows the final delta threshold to depend only on the fixed parameters. The corresponding weakening of original uniformity must also be proved. This observation is an assembly route, not a completed A.1 proof.
