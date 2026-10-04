# Scope of the constant-width angle transfer

The 12-proof Step 2 checkpoint and the additional original ball-profile
proof are frozen separately. This note audits the geometry for the next
tube-family construction; the five transfer declarations are frozen in
WZ_ORIGINAL_BOUNDED_ANGLE_TRANSFER_MANIFEST.json after strict source checks
and independent imported readback with standard axioms only.

Let p,a,b be original points with p!=a and p!=b. Suppose their actual
oriented radial angles at the common root p differ by at most rho. For
original points x in [-1,1]^2 and p in the same box, the intended transfer is

    x in physicalPairTube(P,w,(p,a))
      => x in physicalPairTube(P,4w+8rho,(p,b)).

No lower bound on |p-a| or |p-b| is needed beyond nonzeroness. The same
statement works after swapping either pair's endpoints when necessary;
the angle comparison is always made with the actual common root.

One elementary derivation uses the exact determinant/sine identity already
proved in OriginalRadialSineGeometry. Physical membership yields

    |x-p|_2 * |sin(angle(p,a)-angle(p,x))| <= 2w.

The sine function is 1-Lipschitz, and the fixed source box gives
|x-p|_2<=4. Thus the corresponding quantity for b is at most 2w+4rho.
The original pair's Euclidean norm is at most twice its maximum-coordinate
norm. The normalized original strip residual is therefore at most
4w+8rho. OriginalPairStripPhysicalBridge constructs an actual affine-line
witness at Euclidean distance equal to that residual. This proves a
physical support inclusion while retaining the literal original points.

Taking w=rho gives width 12rho. Applying another such transfer at another
original shared root gives width 56rho. The two transitions must retain
their actual angle comparisons and literal original line labels; membership
in a common finite point support cannot replace those hypotheses.

## Full tubes and parameter cells

The paper uses bounded longitudinal tubes in equation (19), whole-line
dyadic parameter tubes in Definition 3.6, and bounded rho-by-1 tubes in
Section 13.2. It also warns that physical thickening is not automatically
contained in a dyadic ancestor. See the local text at lines 797–816 and
2655–2656, and the [original paper](https://arxiv.org/pdf/2609.22035).

Constant-width containment of full unbounded nonparallel strips is false.
The proved finite-support statement will only concern original P in its
fixed box. It also extends mathematically to a fixed bounded domain, with
the constant adjusted to that domain's diameter, so fixed-length canonical
physical representatives are a suitable eventual model.

There is a second distinction that matters even inside a bounded box:
containment of the finite P-supported tube set does not imply closeness of
the underlying line parameters. Inferring a line's direction from two
contained endpoints separated only by r naturally costs a factor 1/r.
The off-root mass supplies more original points, but does not create a
unit-length segment of the underlying line.

Accordingly, construct cells from each actual original pair line's unit
normal and signed offset, with a finite chart/orientation convention. For
two lines sharing a root p in the fixed box, angle difference <=rho gives
normal difference O(rho) and offset difference O(rho), directly. This
retains genuine line-parameter proximity through two graph-class hops.
It does not require inferring that proximity from a support containment.

Near a dyadic boundary, nearby actual parameters can occupy adjacent cells.
A finite neighbouring-cell cover, suitable shifted grid, or canonical
bounded representative must handle this explicitly. One may then prove
physical containment and bounded multiplicity for the chosen family.
Neither property follows just from naming the rounded cell an ancestor.

The conservative r-factors in the paper remain valid upper bounds when
0<r<=1. Eliminating them in the eventual family construction requires
checking every assignment, chart change, physical containment, and
essential-distinctness statement. The same-root support transfer alone
does not complete that construction or prove A.3.
