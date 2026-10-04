# Original A.1 Step 2 continuation

Status: frozen in WZ_NATIVE_A1_STEP2_MANIFEST.json. All five modules and all
12 public proofs passed strict source compilation and independent imported
axiom readback, using only propext, Classical.choice, and Quot.sound. One
private counting helper is also checked and is excluded from the public count.

Use the original P throughout. Let r=delta^(2 eta/t), and take

    C1 = 4 + 12/t,
    eta' = C1 eta,
    a = t-sigma > 0,
    tau0 = delta^(2 eta'/a).

The source restrictions are 0<t<=2, 0<=sigma<=1, sigma<=s, sigma<t,
eta>0, eta<=t/2, and

    (C1+1) eta <= zeta + sigma - s.

The selected densest width rho is a member of the literal menu
{(1/2)^j : j<=n}, with delta<=rho<=1. Define S to consist of those menu
members tau with rho<=tau<=tau0. At each tau, remove the actual original
pairs with at least delta^(-eta') tau^a m original points in their closed
annular support, doing this for both original endpoint orientations.

The two verified finite modules construct this deletion and prove

    |G2| <= |G3| + 1216 |S| r^(-3 sigma) delta^(eta'-eta) |P|^2.

The literal line witness proves invariance under swapping the original
endpoints. No symmetry hypothesis on G2 is imposed. The scale family S is
finite with |S|<=n+1; original distances between rho and tau0 lie in one of
its actual closed annuli.

The remaining parameter calculation uses

    r^(-3 sigma) delta^(eta'-eta) <= delta^(3 eta).

Choosing delta small enough that
1216(n+5) delta^eta<=1 therefore yields deletion at most
delta^(2 eta)|P|^2. The cutoff is chosen before n, using
delta<=(1/2)^n<=2 delta and Mathlib's exponential-versus-power limit.

For an original retained pair, each endpoint-near part of its wide tube is
covered by the original rho-ball and the actual retained annuli. The
densest lower-occupancy inequality implies

    delta^(-eta) rho^t |P| <= 4 delta^eta' m.

Here the only exponent requirement is eta'+eta<=zeta+sigma-s; the factor
rho^(t-sigma)<=1 is retained in the derivation. Also

    delta^(-eta') tau0^a = delta^eta'.

Thus both endpoint balls together contain at most
2(n+5) delta^eta' m of the original rho-tube points. The cutoff
4(n+5) delta^eta'<=1 gives at least m/2 original points outside BOTH closed
tau0-balls. This preserves the actual original source cardinality and the
actual physical rho-neighbourhood.

The drafted closed caller applies the already proved original near-diagonal
deletion before constructing the densest bin. Either the original violating
graph G already has |G|<=delta^eta |P|^2, or it constructs n,rho,j,G3 with
m=2^j, G3 subset G, original endpoint separation at least r, original
occupancy and all-larger-width controls, and the bound

    |G| <= delta^eta |P|^2
           + (n+1)(1+log_2 |P|)(|G3|+delta^(2 eta)|P|^2).

The logarithmic source-cardinality factor is intentionally exact. No
packing assumption was supplied to these original-profile callers, so
log|P| is not silently replaced by log(1/delta).

Further independent work is the angular class population estimate (228),
then composition with the already proved native two-sided class pruning.
The shaded tube geometry and genuine small-s A.3 gain remain separate.
