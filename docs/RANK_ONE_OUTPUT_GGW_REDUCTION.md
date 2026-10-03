# Rank-one output graphs and a valid external projection interface

Date: 2026-10-03. Handwritten applicability audit; NOT a Lean proof and NOT a
replacement project axiom. The elementary one-channel proof is in the separate
RANK_ONE_BOREL_FEEDBACK_ESCAPE note. Here the scalar nonlinearity may depend
on all three slope coordinates, at the cost of a deep external theorem.

## Concrete cyclic-linear case

Suppose on a positive original source

  b(a)=c+L a+u g(a),

where g is Borel and det[u,Lu,L^2u]!=0. The original slope source has bounded
density and positive mass. Its graph E={(a,g(a))} in R^4 has Hausdorff dimension
at least3, since its projection to slopes has positive three-volume. One may
first take a compact positive-source Lusin restriction to make E compact and
bounded while retaining the actual original front.

Put M(t)=L+tI and define the rank-three map

  Q_t(a,z)=M(t)a+u z.

It has rank3 for EVERY real t. Indeed, if a row h annihilates M(t) and u, then
hL=-th and hu=hLu=hL^2u=0, so h=0 by the displayed Krylov determinant.
An explicit nonzero kernel vector is

  n(t)=(-adj(M(t))u, det(M(t))).

Write det(M(t))=t^3+c_1 t^2+c_2 t+c_3. The standard adjugate identity gives

  adj(M(t))u=t^2u+t(c_1u-Lu)+(L^2u-c_1Lu+c_2u).

Therefore n(t)=C(1,t,t^2,t^3)^T for a fixed invertible 4-by-4 matrix C.
Invertibility follows by comparing the first three coordinates of the first
three coefficient columns with u,Lu,L^2u; the last column is (0,0,0,1).

## Explicit dual osculating curve

Let

  h(t)=(-t^3,3t^2,-3t,1),
  gamma(t)=C^(-T)(-t^4/4,t^3,-3t^2/2,t).

Then gamma'(t)=C^(-T)h(t). The three vectors gamma',gamma'',gamma''' are
orthogonal to n(t): directly, (1,t,t^2,t^3) is orthogonal to h,h',h''.
They are independent, and gamma',gamma'',gamma''',gamma'''' are independent
for every t. Thus gamma is a nondegenerate smooth quartic curve and

  span(gamma',gamma'',gamma''')=n(t)^perp.

Q_t has the same kernel as orthogonal projection to this hyperplane, followed
by an invertible linear output map. Their images of E consequently have the
same Hausdorff dimension at each fixed t.

## Actual applicable external theorem

Gan--Guo--Wang, "A restricted projection problem for fractal sets in R^n",
Theorem1.2, proves dimension preservation for projections to the m-th
osculating planes of a smooth nondegenerate curve:

  https://arxiv.org/pdf/2211.09508

Applying its n=4,m=3 case to gamma gives dim_H Q_t(E)=3 for almost every
actual t in any positive-length bounded interval. These are precisely the
original spatial slices c+Q_t(E). Hausdorff slicing then gives dimension4
for their union in the original compact front.

The theorem is used here only at this literal osculating-plane interface.
It does not apply directly to the original six-to-three scalar pencil.
No Lean formalization of the external theorem is supplied by this note.

## Relation to the existing contact-cycle branch

This broad model needs only two fixed independent affine relations on b-La,
equivalently b(a)-La-c lies in one fixed line span(u) on a positive original
source. It does NOT need g to be a function of one linear coordinate.
The current common-height four-line packet and affine-fibre-mark alternatives
do not provide these positive-source graph relations. A finite packet cannot
be silently promoted to this global source statement. No such geometric
extraction from packing-three is established here.

When det[u,Lu,L^2u]=0, the displayed four-dimensional nondegeneracy fails.
A lower-dimensional Krylov/fiber reduction is plausible, but is not included
as a proved corollary in this audit. The elementary one-channel theorem still
covers g(a)=f(v dot a) for arbitrary L, and the eigenvector-output case can be
handled by a triangular scalar potential argument.
