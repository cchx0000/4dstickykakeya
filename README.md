# 4D Sticky Kakeya

Lean 4 formalization of a contact--symplectic approach to the four-dimensional
sticky Kakeya problem.

This repository records the current formalization state. It is **not yet an
unconditional, kernel-checked proof of the final four-dimensional theorem**.
The collision/Maslov/selector infrastructure and substantial parts of the
finite-scale and Frostman chain are present, but the current public
`selector_closure` route still imports a Wang--Zakharov volume estimate through
the project axiom
`wang_zakharov_published_volume_estimate`. The intended endpoint is to remove
that dependency by closing the weighted, source-hereditary Carleson branch
internally.

The latest Prove2Me main target and eight milestones, their dependency graph,
the uniform finite-scale target, and the remaining no-WZ closure gates are recorded in
[PROVE2ME_TARGETS.md](PROVE2ME_TARGETS.md).

## Current formalization

The main no-WZ development now includes:

- exact collision identities and Maslov-incidence conversion;
- Borel/measurable selector reduction and finite-scale source extraction;
- a common-height analytic four-cycle packet whose collision time is derived
  from the geometry rather than identified with the affine fibre mark;
- a coherent common-height collision tower, with the noncollapsed infinite
  branch ruled out through the Maslov return tower;
- a public source-point alternative returning either coherent collision-time
  motion or an affine three-packet;
- weighted affine-mark half-removal and a three-packet return Carleson ledger;
- a uniform marked source-hereditary finite-scale interface and the Frostman
  mass-distribution reduction.

The following recently added targets were compiled successfully in the pinned
Colab environment:

- `Thm_StickyKakeya4_collision_time_coherent_motion`
- `Thm_StickyKakeya4_parametrized_source_return_budget`
- `Thm_StickyKakeya4_common_height_collision_tower`

Their theorem readback used only Lean's standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. This statement is deliberately
limited to those targets; it is not a claim that the full final theorem is
axiom-free.

## Repository layout

- `Definitions/`: common geometric and measure-theoretic definitions.
- `Theorems/`: theorem statements and the evolving dependency chain.
- `Solutions/`: proof entry points corresponding to the Prove2Me milestones.
- `PROVE2ME_TARGETS.md`: proof architecture, status, and closure criteria.

## Reproducing the Lean environment

The repository pins Lean and both external dependencies:

- Lean `v4.33.1` through `lean-toolchain`;
- `mathlib4` at commit `0df444a360eaa60ab8c11dca51a86af692955474`;
- `LeanFormalizations` at commit
  `dd46c17a2a034d7bfa0df02e7f77834d35592864`.

With `elan` and `lake` available:

```bash
lake update
lake build
```

For a focused check of the active no-WZ front:

```bash
lake build Theorems.Thm_StickyKakeya4_collision_time_coherent_motion
lake build Theorems.Thm_StickyKakeya4_common_height_collision_tower
lake build Theorems.Thm_StickyKakeya4_parametrized_source_return_budget
```

## Author

Chenxi Cai — <Chenxi_Cai@live.com>
