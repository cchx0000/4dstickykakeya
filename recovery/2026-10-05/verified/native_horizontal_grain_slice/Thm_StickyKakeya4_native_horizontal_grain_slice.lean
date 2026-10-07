import Theorems.Thm_StickyKakeya4_native_preserved_node_planes

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeHorizontalGrainSlice
open Classical StickyKakeya4 NativeDirectionRankDichotomy NativeCompatibleNodeDirections

def heightKernel : Submodule ℝ E4 := LinearMap.ker (EuclideanSpace.projₗ (3:Fin 4))

def sliceSpace (P : Submodule ℝ E4) : Submodule ℝ E4 := P⊓heightKernel

def removeHeight (v x : E4) : E4 := x-x (3:Fin 4) • v

lemma removeHeight_mem_heightKernel {v : E4} (hv : v (3:Fin 4)=1) (x : E4) :
    removeHeight v x∈heightKernel := by
  change (x-x (3:Fin 4) • v) (3:Fin 4)=0
  simp [hv]

lemma removeHeight_mem_slice (P : Submodule ℝ E4) {v x : E4}
    (hvP : v∈P) (hv : v (3:Fin 4)=1) (hx : x∈P) :
    removeHeight v x∈sliceSpace P :=
  ⟨P.sub_mem hx (P.smul_mem _ hvP),removeHeight_mem_heightKernel hv x⟩

lemma removeHeight_sub (v x y : E4) :
    removeHeight v (x-y)=removeHeight v x-removeHeight v y := by
  change x-y-(x (3:Fin 4)-y (3:Fin 4)) • v=
    (x-x (3:Fin 4) • v)-(y-y (3:Fin 4) • v)
  rw [sub_smul]
  abel

lemma removeHeight_norm {v : E4} (hv : ‖v‖ ≤ 2) (x : E4) :
    ‖removeHeight v x‖ ≤ 3*‖x‖ := by
  have hc : ‖x (3:Fin 4)‖ ≤ ‖x‖ := PiLp.norm_apply_le x (3:Fin 4)
  calc
    ‖removeHeight v x‖ ≤ ‖x‖+‖x (3:Fin 4) • v‖ := norm_sub_le _ _
    _ = ‖x‖+‖x (3:Fin 4)‖*‖v‖ := by rw [norm_smul]
    _ ≤ ‖x‖+‖x‖*2 := add_le_add le_rfl (mul_le_mul hc hv (norm_nonneg _) (norm_nonneg _))
    _ = 3*‖x‖ := by ring

/-- A genuine graph direction in the grain plane turns its horizontal
intersection into an actual lower-dimensional affine slab, with constant3. -/
theorem near_horizontal_slice (P : Submodule ℝ E4) {v x : E4} {h : ℝ}
    (hvP : v∈P) (hv : v (3:Fin 4)=1) (hvn : ‖v‖ ≤ 2)
    (hx : Metric.infDist x (P:Set E4) ≤ h) :
    Metric.infDist (removeHeight v x) (sliceSpace P:Set E4) ≤ 3*h := by
  let y := P.starProjection x
  have hy : y∈P := (P.orthogonalProjectionOnto x).property
  have hm := removeHeight_mem_slice P hvP hv hy
  have he : ‖x-y‖ ≤ h := by
    rw [NativeEqualRankPlaneTransfer.projection_residual_eq_infDist]
    exact hx
  calc
    Metric.infDist (removeHeight v x) (sliceSpace P:Set E4) ≤
        dist (removeHeight v x) (removeHeight v y) := Metric.infDist_le_dist_of_mem hm
    _ = ‖removeHeight v (x-y)‖ := by rw [dist_eq_norm,removeHeight_sub]
    _ ≤ 3*‖x-y‖ := removeHeight_norm hvn _
    _ ≤ 3*h := mul_le_mul_of_nonneg_left he (by norm_num)

/-- The center is moved along the actual graph direction to the requested
height. The physical point and its original grain width are unchanged. -/
theorem affine_slice_containment (P : Submodule ℝ E4) {v x c : E4} {s h : ℝ}
    (hvP : v∈P) (hv : v (3:Fin 4)=1) (hvn : ‖v‖ ≤ 2)
    (hheight : x (3:Fin 4)=s) (hx : Metric.infDist (x-c) (P:Set E4) ≤ h) :
    Metric.infDist (x-(c+(s-c (3:Fin 4)) • v)) (sliceSpace P:Set E4) ≤ 3*h := by
  have hh := near_horizontal_slice P hvP hv hvn hx
  have he : removeHeight v (x-c)=x-(c+(s-c (3:Fin 4)) • v) := by
    change x-c-(x (3:Fin 4)-c (3:Fin 4)) • v=_
    rw [hheight]
    abel
  rwa [he] at hh

theorem heightKernel_finrank {v : E4} (hv : v (3:Fin 4)=1) :
    Module.finrank ℝ heightKernel=3 := by
  let f : E4 →ₗ[ℝ] ℝ := EuclideanSpace.projₗ (3:Fin 4)
  have hf : Function.Surjective f := by
    intro t
    refine ⟨t • v,?_⟩
    change (t • v) (3:Fin 4)=t
    simp [hv]
  have hr : LinearMap.range f=⊤ := LinearMap.range_eq_top.mpr hf
  have hd := LinearMap.finrank_range_add_finrank_ker f
  have hn : Module.finrank ℝ E4=4 := by simp [E4]
  rw [hr,finrank_top,CommSemiring.finrank_self,hn] at hd
  change 1+Module.finrank ℝ heightKernel=4 at hd
  omega

theorem sliceSpace_finrank (P : Submodule ℝ E4) {v : E4}
    (hvP : v∈P) (hv : v (3:Fin 4)=1) :
    Module.finrank ℝ (sliceSpace P)+1=Module.finrank ℝ P := by
  have hs : P⊔heightKernel=⊤ := by
    apply top_unique
    intro x _hx
    apply Submodule.mem_sup.mpr
    exact ⟨x (3:Fin 4) • v,P.smul_mem _ hvP,removeHeight v x,
      removeHeight_mem_heightKernel hv x,by dsimp [removeHeight]; abel⟩
  have hd := Submodule.finrank_sup_add_finrank_inf_eq P heightKernel
  have hn : Module.finrank ℝ E4=4 := by simp [E4]
  rw [hs,finrank_top,hn,heightKernel_finrank hv] at hd
  change 4+Module.finrank ℝ (sliceSpace P)=Module.finrank ℝ P+3 at hd
  omega

end NativeHorizontalGrainSlice
