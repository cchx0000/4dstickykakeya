# Prove2Me proof structure and targets

> **Source-of-truth update (2026-10-02):** The user has designated the original
> manuscript as the final standard. See [ORIGINAL_PAPER_TARGETS.md](ORIGINAL_PAPER_TARGETS.md)
> for exact source references and the current correspondence audit. In particular,
> the arbitrary-shading estimate in milestone 6 below is an overstrong repository
> translation, not a theorem statement found in the paper. The paper's precise
> hereditary object is a marked edge-occurrence measure, and its main closure
> uses a relative residual/Frostman alternative. The historical proposal below
> is retained visibly for comparison, not silently treated as the source theorem.

This file records the earlier proof contract proposed for the formalization. It follows the latest
Prove2Me proposal: one main theorem and eight milestones, together with the
stronger internal interfaces needed to make them form one unconditional chain.

## Main target

For every compact valid full-direction marked line family `Gamma` whose
unmarked line carrier has packing dimension exactly `3`, prove

```text
dim_H(unitFront Gamma) = 4.
```

The target has no fixed discretization scale and no auxiliary regularity
hypothesis. Compactness, validity, full direction, and the packing-dimension
assumption are explicit.

## Latest eight milestones

1. **Exact collision identity** — prove the exact algebraic identity that
   converts the collision of two affine line trajectories into a relation
   among their direction and fibre data.
2. **Matrix-pencil/Maslov incidence** — identify the geometric collision
   condition with the normalized contact--symplectic/Maslov incidence
   condition, retaining the data needed for later finite-scale estimates.
3. **Borel selector reduction** — reduce an arbitrary sticky line family to
   a measurable/Borel selector and then to coherent finite-scale marked
   sources without losing the selector hypotheses. The selected set remains
   inside the original datum, has carrier packing dimension `3`, and its front
   remains inside the original front.
4. **Packing selector to finite-scale sources** — construct one probability
   measure on the selector front and discretize it at every sufficiently small
   radius by normalized shaded, weighted sources. Same-measure, same-radius
   restrictions must localize ball mass, retain the affine fibre mark, and
   preserve a nested carrier tree.
5. **Lossless edge-flow Carleson accounting** — for a finite carrier forest
   whose incoming mass splits with coefficient one into paid mass, terminal
   mass, and child incoming mass, bound total paid plus terminal mass by root
   incoming mass.
6. **Uniform marked source-hereditary finite-scale estimate** — uniformly for
   every admissible shaded, weighted source and every fractional restriction,
   including retained descendants, prove

   ```text
   integral F_R^2 <= C_epsilon delta^(-epsilon) S_R,
   S_R <= C_epsilon delta^(-epsilon) |U_R|.
   ```

   Constants must be independent of the finite carrier tree and the affine
   fibre marks must be retained.
7. **Hereditary finite-scale to Frostman upgrade** — apply milestone 6 to the
   same-radius localized restrictions of milestone 4 to obtain, for every
   `0 < epsilon < 4`,

   ```text
   mu(B(x,r)) <= C_epsilon r^(4-epsilon).
   ```

8. **Borel selector closure** — every Borel valid direction selector with
   carrier packing dimension `3` has unit front of Hausdorff dimension `4`.
   Its proof must use milestones 4, 6, and 7 and the ambient upper bound,
   without reintroducing compactness at this interface.

Milestones 6--8 and the main theorem currently have a legacy route through a
Wang--Zakharov input. Existing Lean declarations with the final names do not by
themselves constitute the desired internal no-WZ closure.

## Intended complete dependency chain

```text
exact collision identity
        |
        v
Maslov incidence equivalence
        |
        v
Borel selector reduction
        |
        v
coherent finite-scale marked sources
        |
        v
lossless weighted Carleson closure
        |
        v
uniform marked source-hereditary finite-scale estimate
        |
        v
Frostman reduction and mass distribution
        |
        v
selector closure
        |
        v
dim_H K = 4
```

The contact--symplectic structure is essential: it supplies the exact
collision/Maslov routing and the return obstruction used to rule out a
noncollapsed infinite coherent branch.

## Milestone 6 interface

The qualitative selector theorem is not by itself a sufficiently strong
input. The formalization aims at the uniform estimate

```text
|U(V, Y; Q_fib)| >= delta^{o(1)} * sum_{V in V} |Y(V)|.
```

Here `V` is the retained carrier family, `Y(V)` is its shading/source mass,
`Q_fib` records the affine fibre mark, and `U` is the corresponding union.
The Lean interface must encode all four stability requirements:

1. weighted and shaded sources are allowed;
2. the estimate is hereditary under every retained descendant or source
   restriction used by the stopping-time argument;
3. the affine fibre mark is preserved rather than quotiented away;
4. constants are uniform for carrier trees that vary with `delta`.

The relevant present interfaces include
`Thm_StickyKakeya4_uniform_marked_source_hereditary_finite_scale`,
`Thm_StickyKakeya4_hereditary_finite_scale_to_frostman`, and
`Thm_StickyKakeya4_frostman_mass_distribution`.

## Current no-WZ front

The following pieces have been added to prevent the boundary argument from
silently assuming its conclusion.

- `Thm_StickyKakeya4_common_height_collision_time_routing` gives a truthful
  alternative between an analytic collision-time packet and an affine
  three-packet. Collision time and affine fibre mark remain distinct.
- `Thm_StickyKakeya4_collision_time_coherent_motion` packages a
  `CommonHeightAnalyticFourCyclePacket`, converts it to the normalized Maslov
  packet, obtains a slope-secant lower bound from horizontal noncollapse, and
  derives collision-time motion from the exact identity and residual bounds.
- `Thm_StickyKakeya4_common_height_collision_tower` derives `motionTime` along
  a coherent tower. A uniformly noncollapsed infinite branch maps to the
  existing Maslov return tower and is impossible; a surviving branch must
  exhibit arbitrarily collapsed horizontal coefficient directions.
- `Thm_StickyKakeya4_parametrized_source_return_budget` exposes the upgraded
  milestone-4 boundary route as
  `SourcePointCoherentCollisionTimeOrAffineThreePacketAlternative`.
- `Thm_StickyKakeya4_three_packet_half_mass` and
  `Thm_StickyKakeya4_three_packet_return_carleson` contain the current weighted
  affine-mark half-removal and return ledger.

## Remaining closure gates

The final theorem is considered complete only when all of the following are
formalized and connected in the public dependency graph.

1. Build the coherent infinite continuation required by the boundary branch
   from the finite packet alternatives, with all source mass and marks carried
   through the construction.
2. Charge the arbitrarily horizontally collapsed branch to a
   vector-centre/source-hereditary Carleson estimate, uniformly across scales.
3. Integrate affine three-packet half-removal into the generation-by-generation
   weighted ledger without losing mass or subpower normalization.
4. Deduce the negation of the coherent concentration boundary (or an
   equivalent boundary-elimination theorem) from those two branches.
5. Replace the call to `cover_adapted_wang_zakharov_closure` inside
   `Thm_StickyKakeya4_selector_closure` by the internal boundary-elimination
   theorem.
6. Rebuild `sticky_kakeya_four_dimensional` and perform theorem/axiom readback,
   with no project-specific axioms in its transitive proof term.

## Status rule

The files concerning Wang--Zakharov are retained as a legacy comparison and a
temporary conditional route. In particular,
`Thm_StickyKakeya4_cover_adapted_wang_zakharov_closure` currently declares
`wang_zakharov_published_volume_estimate` as an axiom. The project must not be
described as an unconditional formal proof until the six closure gates above
are discharged and the final theorem's transitive axiom readback confirms it.
