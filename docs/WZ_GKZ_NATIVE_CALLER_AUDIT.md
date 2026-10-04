# Scalar sum-product engine versus the native projection caller

## The scalar input used by the new engine

The original carrier is a nonempty finite real set A contained in [1,2]. It is delta-separated, has exactly |A| = delta^(-sigma), and 0 < sigma < 1. Its actual original points obey

    |{a in A : |a-z| <= r}| <= K_F r^sigma |A|

for every real center z and delta <= r <= 1. This is the centered-radius convention; an interval-length convention changes the constant by the corresponding fixed power of 2. No projected or quotient certificate replaces these original point counts.

`GKZOriginalSumProductComparison.original_sum_product_comparison` has a strict source pass. It proves, from the actual occupied original sum and product covers bounded by D|A|,

    1 <= 128 C K_F^3 D^40 (s |A| + h^sigma),
    C = 252 * 110592^9,

where s=2^(-m), 2delta <= h <= 1, and delta <= s h^2. The proof includes the case where the original point profile prevents the required distant-pair selection. The popular carrier, both coefficient alternatives, all collision counts, Ruzsa bounds, and signed-dilate covers are constructed from the original source.

The positive-power continuation chooses h=delta^((1-sigma)/(2+sigma)) and a genuine dyadic s between delta/h^2 and twice that value. For delta <= 1/4, this gives the proposed exponent

    c(sigma) = sigma(1-sigma) / [40(2+sigma)] > 0.

The scale-selection and final fortieth-root sources now have strict source passes. `GKZOriginalPositivePower.original_occupied_sum_product_growth` proves the actual occupied sum-plus-product lower bound with exponent c(sigma) and leading constant

    (96768 * 110592^9 * K_F^3)^(-1/40).

The final continuation is now frozen in GKZOriginalPositivePower.manifest.json, including the compact-range uniform exponent. All public declarations have fresh imported standard-axiom audits. The five frozen manifests contain 28 implementation modules and 67 public proofs. This is a weaker quantitative scalar theorem with the same kind of original separated-set premises; it does not claim the printed optimal GKZ exponent.

## What the actual projection alphabet producer exports

`OriginalCartesianQueryFamily.exists_original_cartesian_query_family` constructs two fixed actual projection alphabets A and B from one common original planar carrier. It proves their bounded coordinates and delta/4 separation. For many original third directions, it gives a literal graph G_c contained in A x B with quantitative density, a small occupied image for its actual linear form, coefficients bounded away from zero, and an original point witness for every edge.

Its Frostman hypothesis is on the original direction carrier C. Its conclusion does not contain a scalar interval profile for either alphabet. In particular, no declaration in that interface proves the `ScalarFrostman` premise required above. An affine change to [1,2] preserves cardinality and changes the mesh by a fixed factor, but does not create this missing profile. Approximate cardinality exponents likewise do not create it.

The output graphs G_c may vary with c. Their common alphabets and original witnesses are valuable, but the theorem does not assert one common dense rectangle, nor small sum and product covers of a single scalar set. A later scalar reduction must derive those statements for the same retained original source.

## Tested obstruction to the shortcut

The retained exact diagnostic `cartesian_marginal_profile.results.json` checks N=4,8,16,32 with delta=N^(-2). The original N by N planar product has N macroscopically spaced first coordinates and N delta-spaced second coordinates contained in an interval of length 1/N. It satisfies the dyadic two-scale 1-regularity bound with constant 1 at every pair of tested dyadic scales. An invertible shear makes these two coordinate alphabets into two bounded-slope projection alphabets, each of size N.

The second scalar alphabet is concentrated at radius of order 1/N. A normalized half-dimensional scalar law therefore needs a constant at least of order sqrt(N), despite the planar regularity and the balanced marginal cardinalities.

This tests only the inference from two small projections and ordinary planar regularity. The same diagnostic computes N^2/2 occupied cells in the middle projection. It is not a counterexample to the entire preserved many-third-query hypothesis. A valid continuation must exploit that additional third-direction information.

## Exact remaining obligation

The first missing native step is a source-faithful regularized ABC/Bourgain reduction: from the actual many-direction graph/query family and its original spatial/directional regularity, select an actual scalar carrier with quantitative retention and a genuine interval profile, while deriving the relevant small sum/product covers on that same carrier. The new scalar theorem supplies a contradiction once those original premises have been proved; it does not supply that reduction automatically.

The previously audited OS good-tube shortcut remains unavailable as a proof of the first gain. In [OS Sections 4.2–4.10](https://arxiv.org/html/2301.10199v4), the local multiplicity exclusion used before the scalar profile is obtained from an already available positive projection statement. The dependency is recorded in `OSGoodTubeMultiplicityDependency.md`. The current native single-scale A.2 graph and the proved global rich fibers do not provide that all-scale local upper bound.

No scalar Frostman law has been inferred from marginal size, and no completed robust-projection or A.3 gain is claimed here.
