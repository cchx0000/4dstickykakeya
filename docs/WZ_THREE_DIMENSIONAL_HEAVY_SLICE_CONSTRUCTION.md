# Original three-dimensional heavy-slice construction

This is a self-contained finite construction for Appendix A.2, Step 1 of Wang–Zakharov, arXiv:2609.22035, printed pp.113–114, particularly (245)–(247). It is an input to the three-dimensional radial theorem used in the (3,2) branch. It does not prove Theorem A.4/22.2 or import the planar radial theorem under a new name.

The five implementation modules contain 19 public proofs. The canonical integration checkpoint records their final strict and proper-import verification status.

## A common actual direction family

For 0<rho<=1, use all six coordinate permutation charts. In each chart take normals (rho*k,rho*l,1), with

    -ceil(3/rho) <= k <= ceil(3/rho),
    0 <= l <= floor(1/rho).

The total number of labels is at most 108/rho². For any distinct p,q in the original bounded cube, choose a largest coordinate of q-p as the first chart coordinate. For every free l, solve the annihilating normal coefficient and round it to the common k-grid. Its magnitude is at most three and its actual pairing with q-p is at most 2rho. The resulting labels are distinct because l is retained. Thus every original pair has at least 1/rho labels in its literal near-orthogonal band.

This proof constructs the labels and normal coefficients. It assumes no spherical net counting theorem, supplied row cap, or geometric incidence certificate.

## Literal original heavy slabs

At each direction label, floor the actual projection value of an original point p. The expanded slab at that grid code consists of original points with projection residual at most 3rho. Every pair in the near-orthogonal band lies together in p's expanded slab.

For a mass threshold H>=0, call such a slab heavy when its original population is at least H. If a band pair has no heavy-slab witness, its second endpoint lies in one light slab determined by its first endpoint. Hence at each direction there are at most H|P| nonheavy ordered pairs. This is derived from the actual source, rather than assumed as a partner cap.

Summing over the constructed direction family and reversing the finite incidence count produces a literal retained subgraph G' of any distinct ordered G subset P×P. It satisfies

    |G| <= |G'| + 216 H|P|/rho.

Every retained original pair has at least 1/(2rho) direction labels carrying a genuine heavy slab through both endpoints. Taking H=rho^(1+eta)|P| gives

    |G| <= |G'| + 216 rho^eta |P|².

All labels and point incidences are explicit finite filters or images of the original source.

## Physical normalization and scope

The normal length is sqrt((rho*k)²+(rho*l)²+1), which is at least one. Dividing the three coefficients by this length gives a proved Euclidean unit normal. Every counted slab is therefore contained in a genuine physical slab of full width 6rho, with the displayed original population and endpoints.

Counts in this checkpoint are of the finite permutation-chart labels. Different charts may represent the same oriented physical direction; no unproved distinct-direction assertion is made. A bounded chart multiplicity conversion is a separate elementary refinement. Subsequent slab two-ends control, slicing regularization, the planar radial input, and the rest of the three-dimensional radial theorem remain open. The project's final volume axiom is unchanged.
