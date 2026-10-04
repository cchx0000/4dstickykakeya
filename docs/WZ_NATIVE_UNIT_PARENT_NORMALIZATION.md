# Actual unit-parent normalization (work in progress)

The frozen NativeCoverADRepresentatives module closes the separate planar representative request: original points in the full square, identical occupied delta-cell image, grid injectivity, and point AD with constant 100 K. Its five proofs and imported audit are complete.

The new geometry continues the fixed-original-compact-source route. It does not modify the native finite input predicate or assert that arbitrary native near-extremizers lie in one fixed compact marked class.

For the original common height a, put m=delta/2 and s=floor(a/m)m. In one actual N=1 parent p, apply the physical map

    t = (x4-s)/16
    yj = (xj-p1j(x4-s)-4p2j)/16.

The actual transformed graph has slope u=oldSlope-p1 in [0,1)^3 and intercept v=(oldShiftedIntercept-p2)/4 in [0,1/4)^3. Its canonical marked line is NativeGraphMarkedLine.ofGraph u v 0. Original marked segment points map to heights of absolute value at most 3/32, inside the genuinely padded unit segment. The padded line has a common slab [-1/4,1/4], direction4>=1/2, and belongs to the fixed compact ball closedBall(0,2) in MarkedLine. The physical map is half-Lipschitz under the derived integer slope-label bound, so original delta-tubes map into padded delta/2-tubes.

The explicit linear determinant is 16^-4=1/65536. Actual affine-image shadings therefore have exactly this volume ratio, both separately and in their union. Original CW pulls back through the actual affine map and has the reciprocal constant 65536. The original/retained tube-count ratio remains visible until a retained-count theorem supplies it.

At every dyadic level N, including the top two, the actual normalized parameter label is

    (z1-N*p1, (z2-N*p2)/4),

with integer division in the second component. Each normalized parameter cube is a union of at most 4^3=64 original parameter cubes; every occupied normalized cube contains an occupied entire original cube. Restriction to one whole original unit parent preserves all occupied finer original fibers exactly.

Dense parent selection is performed within the already retained ORIGINAL R. The strengthened selector uses actual shading-volume and tube-volume sums, so it preserves half the actual average shading/tube-volume density. No unchanged density certificate is inserted.

Remaining geometry is material: affine-image shadings are parallelepipeds, not the literal comparable dyadic cubes required by the current native predicate. Further fixed dyadic contraction is also needed to match tube thickness to the transformed direction-separation scale. The further contraction must put the output thickness below the proved delta/48 direction separation. The fixed factor32 route and actual graph-point cell selection described below retain that margin; their new cubical count, density and union-volume effects remain under construction.

Verification is complete as of 2026-10-04 08:21 UTC. Seven modules contain 45 public lemmas/theorems and 64 audited public declarations (definitions counted separately). Every source strictly compiles with official Lean 4.33.1, -j1, autoImplicit=false and warningAsError=true. NativeUnitParentAssemblyReadback imports all seven modules and audits all 64 declarations; every closure uses only propext, Classical.choice and Quot.sound (one definition uses no axioms). The combined manifest is native_unit_parent_normalization_manifest.json, and the public-proof ledger is native_unit_parent_normalization_public_proofs.json. These seven sources are frozen.

The completed declarations include the actual direction lower bound delta/48. They do not assert separation at the wider padded delta/2 tube scale. NativeDenseNormalizedParent.exists_dense_normalized_parent constructs a whole parent within the original retained R and proves that its actual affine-image shading density is at least 1/33554432 of R's actual original shading/tube-volume ratio. Its numerical ratio is calculated from actual original volumes.

The new-cell source construction remains ongoing: use the existing sharp cell-diameter and marked-segment cell-containment theorems and the existing directionSeparatedWZCellSourceAtScales constructor. A further fixed contraction by 32 gives physical output thickness delta/64 and cubical mesh delta/128, while preserving a margin below the proved direction separation delta/48. This graph-point cell selection must retain the joint original support count and 8-row/28^3 fiber-loss calculations. No transformed native admissible-family theorem, paper K_d closure, or final Kakeya theorem is claimed in this batch.
