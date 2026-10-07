import Theorems.Thm_StickyKakeya4_native_retained_slice_grain_ad

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeParentSliceRelationReadback
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeConditionedPairMenu
open NativeAnisotropicSliceLabels NativeAnisotropicShortRowGeometry SelfUniform

lemma parentEdges_twice {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) :
    parentEdges D a N (parentEdges D a N E p) p=parentEdges D a N E p := by
  simp only [parentEdges,filter_filter,and_self]

/-- The stored parent-local point and column comparisons reconstruct the
literal caller relations on that same parent. This is a readback, with no cut. -/
theorem parent_relations {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ)
    (depth : Fin K → ℕ) (hdepth : ∀j,depth j ≤ NativeSquaredGrainQueries.phaseDepth m)
    (E : Finset (Fin n × Index)) (p : Parent) (Q : ℕ)
    (HP : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => slicePoint D a m p z.2))
    (HC : ∀j,HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^(depth j):ℕ):ℝ))
        (64/((2^m:ℕ):ℝ)) z.2)) :
    ∀j x y,x∈parentEdges D a (2^m) E p → y∈parentEdges D a (2^m) E p →
      degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depth j)
        (parentEdges D a (2^m) E p) x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (sliceRelations D a m depth j)
        (parentEdges D a (2^m) E p) y := by
  let I := parentEdges D a (2^m) E p
  have hpoint : HasUniformFibers I Q
      (NativeParentSliceCallerMenu.pointLabel D a (2^m) (slicePoint D a m)) := by
    have hh : HasUniformFibers I Q (fun z => (p,slicePoint D a m p z.2)) := by
      intro x hx y hy
      simpa only [Prod.mk.injEq,true_and] using HP x hx y hy
    apply uniformity_congr I _ _ Q (fun z hz => ?_) hh
    simp only [NativeParentSliceCallerMenu.pointLabel,(mem_filter.mp hz).2]
  have hclass (j : Fin K) : HasUniformFibers I Q
      (NativeParentSliceCallerMenu.classLabel D a (2^m) (slicePoint D a m)
        (fun _p j => sliceClass m (depth j)) j) := by
    have hh : HasUniformFibers I Q (fun z =>
        (p,columnLabel D a (2^m) p (64/((2^(depth j):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2)) := by
      intro x hx y hy
      simpa only [Prod.mk.injEq,true_and] using HC j x hx y hy
    apply uniformity_congr I _ _ Q (fun z hz => ?_) hh
    simp only [NativeParentSliceCallerMenu.classLabel,(mem_filter.mp hz).2,
      sliceClass_point_eq_column D a m (depth j) (hdepth j) p z.2]
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro j x y hx hy
    simpa only [sliceRelations,NativeParentSliceCallerMenu.relations,Fin.addCases_left,
      unit_degree_eq_fiber] using hpoint x hx y hy
  · intro j x y hx hy
    simpa only [sliceRelations,NativeParentSliceCallerMenu.relations,Fin.addCases_right,
      unit_degree_eq_fiber] using hclass j x hx y hy

end NativeParentSliceRelationReadback
