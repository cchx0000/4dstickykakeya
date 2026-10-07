import Theorems.Thm_StickyKakeya4_native_slab_plane_frame

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeSlabPlanePullback
open Classical Finset StickyKakeya4 NativeHorizontalGrainSlice NativeGrainQuotientInjection
open NativeReferenceXYGridLinear NativeSlabPlaneFrame
open scoped Matrix.Norms.Elementwise

/-- The existing slab graph plane, transported by the actual fixed frame
inverse into the physical Euclidean four-space. -/
def nativePlane (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1))) (c : ℝ) : Submodule ℝ E4 :=
  (SlabPlanePullback.plane (matrixContinuous M) xi u c).map
    (frameEquiv P hP ell hell hell4 hd).symm.toLinearMap

def nativeWitness (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u phi : EuclideanSpace ℝ (Fin (ell-1))) (c : ℝ) : E4 :=
  (frameEquiv P hP ell hell hell4 hd).symm
    (SlabPlanePullback.graphMap (matrixContinuous M) xi (SlabPlanePullback.corrected u c phi,1))

lemma nativePlane_finrank (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1))) (c : ℝ) (hu : ‖u‖=1) :
    Module.finrank ℝ (nativePlane P hP ell hell hell4 hd M xi u c)=ell-1 := by
  rw [nativePlane,LinearEquiv.finrank_map_eq,SlabPlanePullback.plane_finrank _ _ _ _ hu]
  exact finrank_euclideanSpace_fin

lemma nativeWitness_coordinates (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u phi : EuclideanSpace ℝ (Fin (ell-1))) (c : ℝ) :
    let w := nativeWitness P hP ell hell hell4 hd M xi u phi c
    tangentCoordinates P ell hd w=SlabPlanePullback.corrected u c phi ∧
    NativeReferenceXYGridLinear.normalCoordinates P hP ell hell hell4 hd w=
      M.toEuclideanLin (SlabPlanePullback.corrected u c phi)+xi ∧ w (3:Fin 4)=1 := by
  simpa only [nativeWitness,SlabPlanePullback.graphMap_apply,one_smul,matrixContinuous_apply] using
    inverse_coordinates P hP ell hell hell4 hd
      (SlabPlanePullback.graphMap (matrixContinuous M) xi (SlabPlanePullback.corrected u c phi,1))

/-- The native graph residual is exactly the product-coordinate error
needed by the already proved slab pullback. -/
lemma frame_graph_error (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (v : E4) :
    ‖(tangentCoordinates P ell hd v,NativeReferenceXYGridLinear.normalCoordinates P hP ell hell hell4 hd v)-
      (tangentCoordinates P ell hd v,xi+matrixContinuous M (tangentCoordinates P ell hd v))‖=
      ‖quotientMap P hP ell hell hell4 hd M v-xi‖ := by
  simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,matrixContinuous_apply]
  rw [max_eq_right (norm_nonneg _)]
  congr 1
  simp only [quotientMap,LinearMap.sub_apply,LinearMap.comp_apply]
  abel

/-- The fixed inverse graph estimate avoids the extra product-norm loss:
the constructed same-height witness has Euclidean error2r+e. -/
lemma nativeWitness_distance (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1)))
    (c r e : ℝ) (v : E4) (hv : v (3:Fin 4)=1) (hu : ‖u‖=1)
    (hslab : |inner ℝ u (tangentCoordinates P ell hd v)-c| ≤ r)
    (hres : ‖quotientMap P hP ell hell hell4 hd M v-xi‖ ≤ e) :
    dist v (nativeWitness P hP ell hell hell4 hd M xi u (tangentCoordinates P ell hd v) c) ≤ 2*r+e := by
  let w := nativeWitness P hP ell hell hell4 hd M xi u (tangentCoordinates P ell hd v) c
  obtain ⟨hwT,hwN,hw3⟩ := nativeWitness_coordinates P hP ell hell hell4 hd M xi u (tangentCoordinates P ell hd v) c
  change w (3:Fin 4)=1 at hw3
  have hQw : quotientMap P hP ell hell hell4 hd M w=xi := by
    change NativeReferenceXYGridLinear.normalCoordinates P hP ell hell hell4 hd w-M.toEuclideanLin (tangentCoordinates P ell hd w)=xi
    rw [hwT,hwN]
    abel
  have hdiff : v-w∈heightKernel := by
    change (v-w) (3:Fin 4)=0
    simp only [PiLp.sub_apply,hv,hw3,sub_self]
  have hT : ‖tangentCoordinates P ell hd v-tangentCoordinates P ell hd w‖ ≤ r := by
    rw [hwT,←dist_eq_norm,SlabPlanePullback.correction_dist_eq u _ c hu]
    exact hslab
  have hh := horizontal_inverse P hP ell hell hell4 hd M hM hdiff
  rw [map_sub,map_sub,hQw] at hh
  rw [dist_eq_norm]
  linarith only [hh,hT,hres]

/-- A genuine lower-rank Euclidean plane and explicit same-height witness,
constructed from the actual native coordinates by SlabPlanePullback. -/
theorem native_slab_pullback (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell))) (u : EuclideanSpace ℝ (Fin (ell-1)))
    (c r e : ℝ) (v : E4) (hv : v (3:Fin 4)=1) (hu : ‖u‖=1)
    (hslab : |inner ℝ u (tangentCoordinates P ell hd v)-c| ≤ r)
    (hres : ‖quotientMap P hP ell hell hell4 hd M v-xi‖ ≤ e) :
    Module.finrank ℝ (nativePlane P hP ell hell hell4 hd M xi u c)=ell-1 ∧
      nativeWitness P hP ell hell hell4 hd M xi u (tangentCoordinates P ell hd v) c∈nativePlane P hP ell hell hell4 hd M xi u c ∧
      nativeWitness P hP ell hell hell4 hd M xi u (tangentCoordinates P ell hd v) c (3:Fin 4)=1 ∧
      dist v (nativeWitness P hP ell hell hell4 hd M xi u (tangentCoordinates P ell hd v) c) ≤ 2*r+e := by
  have hg := SlabPlanePullback.slab_pullback (matrixContinuous M) xi u (tangentCoordinates P ell hd v) c r e
    (tangentCoordinates P ell hd v,NativeReferenceXYGridLinear.normalCoordinates P hP ell hell hell4 hd v)
    hu hslab (by rw [frame_graph_error]; exact hres)
  refine ⟨nativePlane_finrank P hP ell hell hell4 hd M xi u c hu,?_,
    (nativeWitness_coordinates P hP ell hell hell4 hd M xi u _ c).2.2,
    nativeWitness_distance P hP ell hell hell4 hd M hM xi u c r e v hv hu hslab hres⟩
  exact Submodule.mem_map.mpr ⟨_,hg.2.1,rfl⟩

end NativeSlabPlanePullback
