# Cyclic Fourier parameterization: exact change and remaining structure

Date: 2026-10-03. Handwritten audit. No general cyclic Borel escape is claimed.

Consider the independent PRODUCT REFERENCE on three bounded intervals and

  X_t=(tA_1+f_1(A_2), tA_2+f_2(A_3), tA_3+f_3(A_1)).

The actual source may be dominated by this product; it need not be independent.
For the product reference, after relabeling the three scalar functions, write

  phi_i(alpha,beta)=integral exp[-i(alpha a+beta f_i(a))] da,
  |widehat(mu_t)(xi)|^2=product_i |phi_i(t xi_i,xi_(i-1))|^2.

Indices are cyclic. For each fixed beta, horizontal Plancherel gives a uniform
bound on integral |phi_i(alpha,beta)|^2 d alpha. This is a conditional row norm;
it is not a full independent-frequency bound.

## 1. Exact positive-sector parameterization

In the sector t,xi_1,xi_2,xi_3>0 put

  rho=(xi_1 xi_2 xi_3)^(1/3),
  v_i=t xi_i/xi_(i-1).

Then

  t=(v_1 v_2 v_3)^(1/3),
  xi_1=rho(v_1/v_2)^(1/3),
  xi_2=rho(v_2/v_3)^(1/3),
  xi_3=rho(v_3/v_1)^(1/3),

and the exact Jacobian is

  dt dxi_1 dxi_2 dxi_3 = rho^2/(3t^2) d rho d v_1 d v_2 d v_3.

For example, in logarithmic coordinates, the map from
(log t,log xi_1,log xi_2,log xi_3) to (log v_1,log v_2,log v_3,log rho)
has determinant3. Other nonzero sign sectors have analogous formulas with
absolute values and finitely many fixed signs.

The ith factor becomes phi_i(v_i beta_i,beta_i), but

  beta_i=rho(v_(i-1)/v_i)^(1/3).

Thus changing v_i also changes the SECOND frequency in that factor. The
fixed-beta Plancherel bound cannot simply be applied independently in the
three v_i variables. Degenerate/near-zero frequency sectors also need their
own argument; the nondegenerate sector alone already exhibits this issue.

## 2. A sharp countertest to a row-norm-only inference

For large R and positive beta define

  h_1(beta)=R^3/beta^2,
  h_2(beta)=beta,
  h_3(beta)=R^(3/2)/sqrt(beta),
  H_i(alpha,beta)=1_{|alpha-h_i(beta)|<=1}.

If desired, truncate all beta and alpha to fixed-comparability multiples of R.
Every H_i is bounded by1 and satisfies integral H_i(alpha,beta)d alpha<=2.
Nevertheless

  integral_(t in [1,2], |xi_i|<=C R)
       product_i H_i(t xi_i,xi_(i-1)) dxi dt >= c R.

Indeed the exact three constraints have the two-dimensional solution family

  t in [1,2], xi_3 in [R,2R],
  xi_2=R^3/(t^2 xi_3^2),
  xi_1=R^3/(t xi_3^2).

All three xi_i are comparable to R. For every such (t,xi_3), a sufficiently
small FIXED-width rectangle in (xi_1,xi_2) around this solution satisfies all
three strip inequalities. The derivative of h_3 is bounded by a fixed
constant on the relevant frequency range; all other required variations are
also uniformly bounded. Integrating those rectangles over an interval of
xi_3-length R proves the lower bound.

These H_i are an abstract mixed-row-norm countermodel. They have NOT been
shown to equal squared Fourier transforms of actual graph measures. They
therefore refute only the proposed inference from horizontal Plancherel and
independent slope labels. A successful cyclic proof must exploit genuine
Fourier positive-definiteness/oscillation, graph structure, or sticky packing
in an additional way.

## 3. Elementary real-space baseline

On an actual time interval with |t|>=c>0, the cyclic physical map always has

  sigma(P_t^(-1)(a spatial cube of side r)) <= C D r^2

for a bounded-density source, with no regularity of the f_i. Drop one output
constraint. Fix the remaining free source coordinate, then integrate the two
remaining linear-own-coordinate conditions in directed-tree order; each has
length O(r/|t|). This is a legitimate two-dimensional slice bound. Restoring
the third feedback constraint is precisely the missing dimension; an ordinary
cyclic Holder/Finner inequality does not restore it.

## 4. Separate solved subcase

If two of the f_i are affine, the remaining feedback channel has the form
b(a)=La+u f(v dot a). The independently audited rank-one Borel feedback note
reduces that case to a nonconstant rational time parameter and obtains the
actual supported Frostman escape. This does not settle three arbitrary f_i.
