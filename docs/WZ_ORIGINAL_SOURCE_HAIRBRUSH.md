# Complete original-source three-dimensional hairbrush estimate

The canonical 764-module build passed 9,473 jobs with exit 0. Two new modules add eleven public proofs; all fresh imported closures use only foundational axioms. All previous 762 source hashes are unchanged. Cumulative unique checked declarations: 4,374. This completes the local original-source estimate corresponding to Wang--Zakharov equation (253); it does not complete Theorem A.4 or the final four-dimensional theorem.

## Exact original input and conclusion

Let P be a nonempty finite subset of [-1,1]^3, and G an actual subset of P times P without diagonal pairs. Assume

- 0 < delta <= rho <= 1 and eta >= 0;
- 0 < lambda,nu <= 1 and |G| >= lambda |P|^2;
- for every original p in P and delta <= r <= 1, the actual ball count is at most delta^(-eta) r^2 |P|;
- every original pair in G has at least nu rho |P| original points in its actual Euclidean rho-tube;
- N is a natural number with 1 <= 2 rho 2^N.

Write K=delta^(-eta). The public theorem
`OriginalThreeDimensionalSourceHairbrushSlab.exists_original_source_hairbrush_slab`
constructs a Euclidean unit normal n and center c. Its actual original-point slab has half-width

    W = 10^12 K^2 rho / (lambda nu)

and satisfies

    lambda^10 nu^14 |P|
      <= 10^140 K^21 (N+1)^3
         |{p in P : |n dot p-c| <= W}|.

All quantifiers and inequalities above are fields of the proved source-only statement. No transverse brush, overlap bound, two-ends property, shade-density certificate, or desired slab population is an input. In particular, the proof does not invoke the published Wang--Zakharov estimate, a classical hairbrush axiom, or a new Katz--Tao assumption.

## What the proof constructs

The small-radius branch derives its transverse angle and stem radius from the displayed original density and Frostman constants. The original graph supplies a common coordinate chart and an actual transverse brush. One global original cube representative set supplies every rich tube's shading. Each shading is cut outside the same original stem; the proved local shade count pays that deletion.

The true plane pencil partitions whole original tube fibers. Its raw-band overlap bound and the actual finite shade-union inequality select a dense pencil group. Localized point energy then pays that group's original mass, retaining the ambient P normalization. The exact parameter and constant calculation gives the displayed bound. The complementary large-radius branch uses the whole original bounded box, with its width and mass inequalities proved explicitly.

The earlier mathematical derivation is recorded in
[the direct hairbrush proof](WZ_DIRECT_ORIGINAL_HAIRBRUSH_PROOF.md).
The source-only theorem now implements its complete geometric construction.

## Literal finite-slab hypothesis

The second module constructs a genuine orthonormal frame extending any unit normal. Every original point in the bounded box has each frame coordinate at most three in absolute value. The original infinite normal-band population is therefore covered by 49 actual rectangles with unit tangential side lengths and the same normal half-width.

Thus the printed A.4 hypothesis on finite delta^epsilon1 by 1 by 1 slabs supplies a unit-normal band cap with a factor 49 when the half-width is delta^epsilon1/2. This finite covering step is proved, rather than silently replacing finite rectangles by infinite bands.

## Remaining scope

The concentrated-incidence exclusion and subsequent slice-energy/planar reduction are separate consumers. Their original scale, label and mass readbacks remain explicit. The robust weak-profile A.3 gain, fixed-class extremal/configuration assembly and final finite-volume bound still require further work. The original final compact-family theorem is unchanged and its current public route still depends on `wang_zakharov_published_volume_estimate`.
