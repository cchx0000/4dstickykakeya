# Original-paper target audit

Audit date: 2026-10-02. Status: source comparison and proof-obligation audit; **not** a certification of the manuscript or a completed Lean proof.

## 1. Authoritative source and unchanged final theorem

The reference is Chenxi Cai, *Sticky Kakeya in R4 as a Contact–Symplectic Incidence Problem*, subtitle *Contact Geometry, Maslov Four-Cycles, and Lossless Edge Flow*.

- [Author's publication page](https://cchx0000.github.io/), which links both versions below
- [PDF, 137 pages](https://cchx0000.github.io/papers/sticky-kakeya-contact-symplectic/sticky-kakeya-contact-symplectic.pdf)
- [LaTeX source](https://cchx0000.github.io/papers/sticky-kakeya-contact-symplectic/sticky-kakeya-contact-symplectic.tex)
- Retrieved PDF SHA-256: `30341e7d51cfdb8905beca1fe569ba1af07d784e63b8342f7db2a9d1ca1a2c73`
- PDF creation metadata: 2026-09-11 23:18:03 +09:00. This is metadata, not an independently verified publication date

Page numbers below are the printed PDF page numbers, which also match the PDF page indices plus one. TeX labels refer to the linked source, as retrieved on the audit date.

**Definition 1.1 and Theorem 1.2, p. 2; TeX label `thm:main`:** the final target remains Hausdorff dimension four for the Euclidean union of marked unit intervals in every compact full-direction family whose unmarked line carrier has packing dimension three.

In repository notation, preserve the mathematical content of:

```text
IsStickyDatum Gamma -> dimH (unitFront Gamma) = 4
```

The use of `packingDim <= 3` in `IsStickyDatum` is compatible with the paper's equality once the full-direction lower bound is established. No extra regularity, finite-scale density, continuation certificate, or Carleson estimate may be added as a new final-theorem hypothesis merely to make a proof compile.

The September 2026 Wang–Zakharov result used by the legacy Lean axiom is a different source. It is not the original manuscript audited here.

## 2. What the original actually uses to close the proof

The source's final route is a **residual-energy/Frostman alternative**, not an unconditional estimate on every arbitrarily thinned tube family.

1. **Proposition 3.1, p. 4**, label `prop:selector`: select a Borel marked graph inside the compact datum, preserve carrier packing dimension three, and retain front containment
2. **Definition 6.26 and Theorem 6.27, pp. 33–34**, labels `thm:v048-residual-frostman-criterion` and its preceding definition: control the weighted collision residual content

   ```text
   Z_rho(mu) = integral_{a != a'}
     1_{s*(a,a') in J+} 1_{|residual(a,a')| <= rho} / |a-a'|
     d sigma(a) d sigma(a')
   ```

   Bounds `Z_rho <= C_eta rho^(2-eta)` yield projected finite energies and then the Hausdorff lower bound by slicing
3. **Lemma 8.56, p. 105**, label `lem:v081-hereditary-markov-exhaustion`: exhaust a uniformly positive-fraction routing rule on every unused submeasure of one occurrence measure
4. **Proposition 9.29, pp. 122–123**, label `thm:v081-cross-generation-edge-flow-conservation`: claim coefficient-one conservation for absolute old-edge occurrences and a terminal cap estimate
5. **Proposition 9.30, pp. 123–124**, label `prop:v081-lossless-cap-saturation`: claim a deterministic cap contraction schedule and sublogarithmic terminal depth
6. **Corollary 9.31, p. 124**, label `cor:v081-maslov-bush-frostman-bridge-closed`: on a fixed coarse layer, obtain either the relative residual bound or front-supported Frostman measures. Under the contradiction hypothesis `dimH K < 4`, the Frostman exit is excluded
7. **Theorem 9.32, p. 124**, label `thm:v081-sticky-kakeya-closure`: sum the residual estimates and invoke Theorem 6.27
8. The final proof on **p. 135** transfers the selector conclusion to the original front

The exact measure support and quantitative hypotheses of these steps remain part of the formalization obligations. A disjunction introduced by classical case splitting does not prove the geometric routing needed to discharge its bad alternative.

## 3. Milestone 6 is stronger than the paper's explicit interface

`PROVE2ME_TARGETS.md` requests both

```text
integral F_R^2 <= C_epsilon delta^(-epsilon) S_R
S_R <= C_epsilon delta^(-epsilon) |U_R|
```

for every fractional restriction. In `Definitions/Def_sticky_kakeya4_core.lean`, `IsFractionalSourceRestriction` permits an arbitrary measurable subset of every original shading. `HasUniformMarkedSourceEstimate` demands the second inequality uniformly over those subsets. The first inequality is not a field of that Lean predicate.

The original's abstract (p. 1), introduction (p. 3), discussion (p. 135), and Appendix B (p. 136) make broad claims about a marked finite-scale extension. However, neither the full PDF nor the linked TeX contains a theorem with the two displayed milestone inequalities and these arbitrary-geometric-shading quantifiers. The heading of §9.7, pp. 125–135, is not such a theorem.

The original's precise restriction objects are instead:

- an ordered edge-occurrence measure, written in (419), p. 107, as a source marginal times an old-neighbor probability kernel
- submeasures of that occurrence measure and measurable partitions of its source/target/time data
- conditional probability extensions retaining marks, as in Lemma 8.56 and Appendix A, pp. 135–136
- fractional source densities which add to at most the parent density under those disjoint partitions

These operations do not by themselves prove a uniform geometric overlap bound after deleting arbitrary portions of all tube shadings.

### Concrete obstruction to the repository's arbitrary-shading target

Consider lines through the origin, with zero affine mark, and a direction-separated delta-net of a fixed three-dimensional direction patch. There are `N` comparable to `delta^(-3)` such lines. Give each line weight one and its full delta-tube shading. The lines are distinct, their direction counts and carrier covering numbers have the required three-dimensional bounds, and root source mass is of constant order.

All their tubes contain the ball `B(0, delta/2)`. Restrict every shading to this common ball. The repository restriction predicate permits this. Then

```text
F_R = N * 1_B
S_R = N * |B|
U_R = B
integral F_R^2 = N^2 * |B|
```

Both milestone inequalities require `N <= C_epsilon delta^(-epsilon)`, which fails, for example for fixed `epsilon = 1` as delta tends to zero.

This is an obstruction to the selected intermediate interface. It does **not** disprove Theorem 1.2: the radial family itself has a four-dimensional unit front. Merely restoring a dense-shading condition on the root does not repair arbitrary thinning, because the original full tubes in this example are already dense.

**Target correction:** do not insist on the false universal shading interface as a necessary milestone. Formalize the paper's actual residual/Frostman alternative, or establish a separately justified corrected finite-scale statement whose restrictions and losses are explicit. Keep Theorem 1.2 unchanged.

## 4. Compactness and measure support: a real source-level mismatch

Proposition 3.1 gives a **Borel** selector. Theorem 9.32 is worded for a **compact** full-direction selector. The final proof on p. 135 applies Theorem 9.32 to the output of Proposition 3.1 without supplying compactness.

A Borel selector of a compact relation need not be compact. In particular, a compact graph over the compact direction sphere would make its single-valued section continuous; measurable selection alone does not imply that continuity.

There is a related support issue in **Theorem 8.10, pp. 81–82**, and **Theorem 8.11, pp. 82–83**. Their weak-limit argument places probability measures on a bounded selector front and concludes that the weak limit is supported on that same front. Boundedness only supplies support in its closure; support in the original set needs closedness or a separate tightness/support argument.

The existing Lean `selector_closure` instead carries a compact `ambient`, assumes `selector` is contained in it, and concludes dimension four for `unitFront ambient`. The same ambient is used in `HasCoherentFiniteScaleSources` and the Frostman reduction.

**Repair proposal for the original main theorem:** retain the original compact marked datum throughout the Borel reduction and all weak limits; conclude support on its compact unit front. This would preserve Theorem 1.2 and avoids claiming the stronger compactness-free selector-front theorem. The geometric routing still needs to be established in that formulation. This audit does not claim the repair has already been proved.

Consequently the old milestone-8 wording, requiring a theorem on every Borel selector without compact ambient data, is stronger than the literal Theorem 9.32. It should not be treated as the authoritative final target merely because it appeared in the milestone document.

## 5. A specific disputed proof step inside the original edge-flow closure

There is a measure-theoretic normalization problem in **Proposition 9.29, p. 123**, equation **(453)**, label `eq:v081-terminal-markov-cap-bound`. The statement calls `f_gamma d sigma` the terminal **source marginal of the old-edge occurrence**, with total mass `p_gamma`. Its proof then uses

```text
M_same <= integral f_gamma(z) 1_gamma(z)
                   [integral 1_gamma(zeta) d sigma(zeta)] d sigma(z)
       <= C p_gamma T_gamma^3
```

The first inequality does not follow from the listed facts `0 <= h <= 1`, bounded base direction density, and source-marginal domination.

### Test of the asserted measure inference

Take a fixed probability measure `sigma` with bounded three-dimensional direction density. Let a cap `E` have mass `a`, where `0 < a < 1`, and put

```text
h(z,zeta) = 1_E(z) * 1_E(zeta)
Gamma = h * (sigma product sigma)
lambda = first_marginal Gamma = a * sigma restricted to E
f = a * 1_E
p = total_mass lambda = a^2
```

This satisfies symmetry, `0 <= h <= 1`, `lambda <= sigma`, fixed inherited endpoint data, and the fractional-source domination for a single piece. Restricting to `E x E` does not change the occurrence. Its within-cap mass is `a^2`, while the displayed integral is `a^3`.

The conditional neighbor kernel from equation (419) is `sigma|E / a`, whose density relative to `sigma` is `1/a`, not at most one. Thus replacing that conditional kernel by the base measure is invalid. Taking shrinking caps makes the loss unbounded even with a fixed base direction-density constant.

**Scope of this test:** it refutes the displayed measure-theoretic inference from those facts. It is not yet a constructed counterexample satisfying every geometric and non-paid-branch hypothesis of the complete bush-return algorithm, nor a disproof of Proposition 9.29 under an additional unrecorded geometric invariant. The distinction matters: some simple physical examples would exit through the Frostman/paid branch.

A sufficient extra estimate would be

```text
kappa_z^gamma(gamma) <= C T_gamma^3
```

for almost every retained source, or an appropriately uniform domination of the retained old-neighbor kernel by the base direction measure. Equation (419) alone gives density `h/d_h`, so such a conclusion cannot be inferred from `h <= 1`. The new transition kernels in Proposition 9.4 have density at most two relative to a normalized bush measure, but they are **not** the inherited old-neighbor kernel, and they are not bounded by the original base measure with a uniform constant.

Alternatively, one could retain a separate selector-level restriction density and prove a joint-measure bound relative to it, with a genuine summable selector-mass budget. This changes the accounting certificate and needs its own proof.

Lemma 8.57, pp. 105–106, proves a valid cap-square estimate for a **product of selector submeasures**. It does not identify a correlated old-edge occurrence with that product. Corollary 9.12, pp. 111–112, gives a different valid aggregate estimate using a bounded-overlap grid and the base selector masses; extending that argument to the entire varying-cap tree requires a demonstrated overlap/accounting invariant.

The requested terminal bound must therefore remain an explicit unresolved obligation until a valid invariant or replacement argument is supplied. It must not be introduced as an axiom or hidden inside an existence certificate presented as a completed proof.

## 6. Further closure checks, not established counterexamples

The following are specific proof obligations for the manuscript-to-Lean translation. They should be tracked separately from the two definite interface mismatches above.

- **Paid and cross-cap budgets.** Proposition 9.1, p. 107, assumes both `M_paid` and `M_cross` are at the quadratic relative target. Proposition 9.29 assigns every old neighbor outside a child cap to `M_cross`, but its telescoping calculation alone gives no such quadratic bound. The fact that this is an aggregate physical graph is not a bound on its mass. A formal proof must identify the precise estimates paying all of those occurrences, including their inherited marks and repeated generations
- **Hereditary routing.** Lemma 8.56 is conditional on a uniform positive-fraction rule for every nonzero remainder. Each geometric use must prove this for the actual remainder, not merely for an initial symmetric product graph or a newly sampled graph
- **Continuation.** Proposition 8.32, pp. 93–94, gives a fixed positive-mass cap either a good-leaf output or arbitrarily fine failures. Corollary 8.35, pp. 94–95, gives arbitrary finite-depth chains and explicitly distinguishes that from synchronized continuous labels. A continuation object with infinite compatible children, time separation, residual decay, and source-mass control must be derived, not just assumed
- **Moving centers and marks.** Theorem 8.11's vector-center inequality (340), p. 82, uses a common physical test point and Reeb time across all components. An estimate for one center cluster does not establish it for freely varying clusters. Lemmas 9.26–9.27, pp. 120–121, provide a concrete three-packet/target-cell partition to formalize, including its exact mass sum
- **Fixed physical thickness versus auxiliary failure scales.** Proposition 9.30 permits nodewise arbitrarily fine auxiliary scales. Appendix B, p. 136, additionally claims a uniform fixed-thickness version. Its hierarchy is not a fully quantified shaded-source theorem. The formalization must specify which geometric estimates survive at the fixed thickness and how all constants are controlled uniformly; it cannot silently identify auxiliary scales with the physical delta

## 7. Recommended verification contract

1. Keep the compact marked main theorem of Definition 1.1/Theorem 1.2 as the final specification
2. Preserve correct collision, Maslov, measurable-selector, and algebraic flow results already proved
3. Label the arbitrary-shading uniform estimate as an invalid target rather than a theorem still awaiting tactics
4. Use a compact-ambient selector interface for the main proof unless a genuinely stronger Borel-selector support theorem is separately proved
5. Formalize the residual/Frostman alternative and a mass-carrying occurrence-tree certificate with all terminal, paid, and cross-cap bounds separately exposed
6. Resolve the conditional-kernel normalization issue before accepting the terminal estimate
7. Rebuild the actual main entry point and inspect its transitive axioms. Standard logical axioms on isolated intermediate declarations do not certify the final theorem
8. Do not report unconditional completion while the final proof still uses `wang_zakharov_published_volume_estimate` or another project-specific replacement axiom

This document supersedes the claim that the eight previous milestone formulations are a verbatim mathematical contract from the original paper. It does not supersede the original final theorem or certify that the remaining original arguments are correct.
