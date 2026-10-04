# Original-point annular charge without angular rectangle covers

This is an independent finite reduction for Wang–Zakharov A.1 Step2, (221)–(223). It uses original point Frostman data, the previously constructed original densest-scale graph, and elementary physical line geometry. It supplies no A.3 incidence gain.

## Actual annular selection

Fix an original root p and its original candidate partners a in the graph G2. Define

    A_a = P intersect physicalTube(p,a,w)
          intersect {q : tau <= EuclideanDistance(p,q) <= 2tau}.

The actual bad row is the set of original partners whose A_a has cardinality at least H. Choose an inclusion-maximal subfamily F whose A_b are pairwise disjoint. This construction reuses the existing finite original-support selector.

The disjoint supports lie in the ORIGINAL ball P intersect B(p,2tau), so

    H |F| <= #(P intersect B(p,2tau)).

Every bad original partner a shares an actual point q of A_a with some A_b, b in F. This includes selected partners because H>0 makes their annular support nonempty. No artificial angular representative or sector center is introduced.

## Physical shared-point geometry

Both original pair lines pass through exactly p. Each physical width-w tube is contained in its original infinity-normalized strip of residual width 2w. The actual shared q satisfies EuclideanDistance(p,q)>=tau, hence boxDistance(p,q)>=tau/2. Original residual subtraction therefore yields

    |det(normal_a,normal_b)| <= 16w/tau.

For any original point v in the candidate width-w tube, the bounded source square gives

    |residual_b(v)| <= 6w + 2|det| <= 38w/tau,

using tau<=1. A proved inverse bridge constructs an actual point on the original representative line: a coefficient of its infinity-normalized normal has absolute value one, so correcting only that coordinate by the residual produces a genuine affine-line point at Euclidean distance exactly |residual|. Thus no extra sqrt(2) loss is needed.

Consequently every bad original partner a lies in the selected representative's actual physical tube of width 38w/tau. This proves the actual row cover and the finite count

    #badPartners <= sum_(b in F) #(P intersect physicalTube(p,b,38w/tau)).

## Use the already-proved original densest profile

The input profile is exactly the all-radius original-point conclusion of the frozen native G2 selection, on rho<=R<=1:

    #(P intersect physicalTube(p,b,R))
      <= 2^(sigma+1) (R/rho)^sigma m.

The same selection and original violation lower bound give

    rho^sigma |P| <= 2^(sigma+1) m.

This clips R>1 by the trivial full-P count and extends the displayed bound to every R>=rho. It does not query Frostman data outside its legal interval and does not condition P on a tube or retained graph.

Take w=r^(-3)rho, with 0<r<=1, 0<=sigma<=1. Then 38w/tau>=rho. The representative physical tube bound, multiplied by the exact disjoint-support charge, gives

    H #badPartners
      <= [2^(sigma+1)(38r^(-3)/tau)^sigma m]
         [delta^(-eta)(2tau)^t |P|].

For the native threshold

    H=delta^(-eta')tau^(t-sigma)m,

the original powers of tau and m cancel exactly. For t<=2 the result is

    #badPartners <= 608 r^(-3sigma) delta^(eta'-eta) |P|.

Here 608=4*38*4 bounds 2^(sigma+1)*38^sigma*2^t. This is stronger than the r^(-4sigma) loss in the source annular estimate. The shared-root construction avoids the extra containment adjustment needed for a generic angular rectangle.

## Closed original-input caller

`NativeOriginalRadialReduction.exists_original_densest_graph_with_annular_control` performs the full independent Step1-to-Step2 assembly. Its input is the original finite P, the actual original violating pair graph G1, original physical radius violations, and the original point Frostman profile. It constructs the dyadic mesh and the original densest G2 bin itself, preserving the exact `(n+1)(1+floor(log_2 |P|))` retention bound and all original pair labels.

The wider-tube profile and full-original-P lower density used above are conclusions of that construction, not hypotheses of this public caller. The caller returns those original density/occupancy estimates and the annular bad-row bound for every original root and legal tau. Earlier original-pair properties pass through its literal G2-subset-G1 conclusion.

## Explicit domain and remaining work

The native endpoint states 0<tau<=1/2 and delta<=2tau, so the queried original ball radius 2tau lies in [delta,1]. This covers the eventually small tau<=tau0 range used for the actual G3 exclusions. It does not claim the same formal endpoint for tau>1/2; that range can use the trivial extension of the original profile beyond radius one if needed.

The original pair graph need not be symmetric. Applying the same construction to the reversed original graph handles the other endpoint. Summing over an actual dyadic scale menu, constructing the two-end exclusion graph, proving its retained off-root tube mass, and the subsequent angular image bound remain further steps.

The separate native class-pruning adapter uses canonical RichWitnessRealCore on tagged forward/reverse copies of original pairs. Both minimum-degree conclusions concern the same final graph. It assumes no geometric bound on the number of angular classes; that still has to come from the original tube incidence argument.

These reductions do not prove A.3, its positive-power union estimate, full A.1, or the final sticky Kakeya theorem. Current compilation and independent imported-axiom status are recorded in the accompanying verification manifest, rather than inferred from this mathematical note.
