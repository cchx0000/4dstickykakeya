# Actual angular class populations and pruning

This checkpoint proves the geometric counting content of Appendix A equations (228)–(230) for the repository's literal original-pair tubes and actual `Complex.arg` floor classes. No angular overlap, class-population bound, or favorable representative family is an input.

## Literal geometry

For an original root `p`, partner `q != p`, and original point `v`, the sine of the difference of the two actual secant arguments is related exactly to the original normalized strip residual. If `v` belongs to the actual Euclidean rho-tube of `(p,q)` and its box distance from `p` is at least tau, this gives

`|sin(arg(q-p)-arg(v-p))| <= 2 rho / tau`.

For every difference in `[-2 pi,2 pi]`, rounding to the nearest integer multiple of pi constructs one of the five shifts `k=-2,-1,0,1,2` with angular error at most `(pi/2)*|sin|`. Counting the literal floor bins in those intervals proves that one original point meets at most `50/tau` distinct rho-angle-bin representatives in box distance. The existing Euclidean-to-box inequality gives the actual Euclidean version `100/tau`.

## Original-point double counting

For each occupied angle bin, the proof chooses an actual original partner. Suppose each resulting original tube has at least `m` original points at Euclidean distance at least tau from the root. Double counting their original tube-point incidences gives

`m * #root angle classes <= (100/tau) * |P|`.

Summing on the actual original roots proves

`m * #forward classes <= (100/tau) * |P|^2`.

Exact pair reversal gives the same reverse-class bound. The graph need not be symmetric; the original pair and its physical affine line are preserved.

## The same final rich core

When both endpoint far-mass hypotheses hold, apply the checked two-sided pruning algorithm with `k=tau^2*m`. The actual output `H` is a subset of the original graph, and

`|G| <= |H| + 400*tau*|P|^2`.

Every retained original pair has forward and reverse class populations at least `2*tau^2*m`, both measured in this same final `H`. Here `m` is the actual endpoint far-mass lower bound. For the upstream Step2 output it can be set to half its dyadic tube occupancy; that fixed factor is explicit, not an implicit mass renormalization.

The six implementation modules contain twelve public theorems/lemmas, strictly checked and independently imported with only the standard foundational axioms. Exact hashes and logs are in the matching manifest.

This constructs the angular population and pruning inputs. It does not yet choose a globally controlled family of line-parameter cells, prove their overlap/critical-width spacing, or prove A.3's genuine positive-power gain. Bounded-source support containment and line-parameter proximity remain distinct facts.
