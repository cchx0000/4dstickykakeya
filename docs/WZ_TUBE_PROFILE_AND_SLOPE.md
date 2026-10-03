# Genuine tube profiles and derived slope consistency

Verified 2026-10-03. Five new modules add 93 strictly checked proved
declarations, with proper imported readbacks using only standard logical
axioms. The full 259-module default build passes 8,968 jobs. All previous
254 source hashes are unchanged. Cumulative recorded checks: 1,927.

`ActualTubeFootprintProfiles` constructs the finite family of exact traces
of genuine sup-unit segment tubes on the original point set. It retains
actual centers, directions and segment parameters; proves coverage, diameter,
maximizers and both linear and AD profile bounds; and proves whole-cell
expansion has width2rho with the same segment interval. The geometric tube
family and its profile bounds are outputs of these constructions, not new
certificates.

`TubeExpansionCover` constructs explicit bounded menus of translated tubes
for width and length enlargement. Both transfers use the SAME original
source and unchanged point/cell labels. Its local-cell theorem chooses an
actual segment parameter and bounds the local rho-cell image using the
original width-rho/length-r profile. This supplies the capacity used to
convert rich original spines into distinct coarse cells.

`NoisyAffineImageCount` derives output-cell counts from actual translated
integer-lattice samples and noisy affine witnesses. It allows repeated output
values and arbitrary output mesh, proving the fiber cap rather than assuming
it. `ScalarKatzTaoSlopeBound` combines that lower count with actual interval
Katz--Tao bounds on the finite witness set. It derives the slope bound,
including zero/small slopes and the long-interval endpoint. No final slope
or image-count certificate is an input.

`NestedPlaneQuantization` constructs an explicit invertible triangular map
and exact simultaneous lower/higher plane representations. The pointwise
inverse quantizer and the constant-old-grain quantizer have different,
explicit error/retention properties. Original labels survive weighted residue
selection. A fixed bottom-coordinate contraction preserves exact consistency
and coefficient ranges; no matrix entry is clipped.

The [slope derivation](WZ_STEP3_SLOPE_CONSISTENCY.md) and
[inheritance checklist](WZ_STEP3_INHERITANCE_CHECKLIST.md) retain the actual
lower-grain density, Katz--Tao constant and error scale. In particular, the
correction occurs at an enlarged mesh; original lines can be kept, while
AD, coarse-cell coherence and shading reconstruction remain actual native
callers. The complete original-input-to-alignment/configuration theorem is
not yet assembled.

The later finite-volume proof also remains substantial. Proposition17.3's
non-affine branch passes through Lemma20.3 and the nonlinear expansion
Theorem13.5. Those are not consequences of these local constructions and are
not declared as new Lean axioms. The existing main WZ volume axiom remains;
the original final theorem is unchanged and is not yet unconditionally
kernel-checked. Prove2Me authentication/submission remains absent.

[Exact hashes, commands and checks](../verification/wz-tube-slope-checkpoint.json)
