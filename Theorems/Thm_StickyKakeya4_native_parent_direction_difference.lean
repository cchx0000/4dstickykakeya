import Theorems.Thm_StickyKakeya4_native_actual_horizontal_grain_slice

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4800000

noncomputable section
namespace NativeParentDirectionDifference
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeSpatialAngularGeometry
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeOriginalParentSelection
open NativeCompatibleNodeDirections NativeOriginalCoarseTupleMenu NativeOriginalAngularTupleMenu
open NativeSeparatedSpanControl NativeHorizontalGrainSlice

theorem difference_near_submodule (P : Submodule ℝ E4) (x y : E4) (r : ℝ)
    (hx : Metric.infDist x (P:Set E4) ≤ r) (hy : Metric.infDist y (P:Set E4) ≤ r) :
    Metric.infDist (x-y) (P:Set E4) ≤ 2*r := by
  let u := P.starProjection x
  let v := P.starProjection y
  have hu : u∈P := (P.orthogonalProjectionOnto x).property
  have hv : v∈P := (P.orthogonalProjectionOnto y).property
  have hxu : ‖x-u‖ ≤ r := by rw [NativeEqualRankPlaneTransfer.projection_residual_eq_infDist]; exact hx
  have hyv : ‖y-v‖ ≤ r := by rw [NativeEqualRankPlaneTransfer.projection_residual_eq_infDist]; exact hy
  have he : (x-y)-(u-v)=(x-u)-(y-v) := by abel
  calc
    Metric.infDist (x-y) (P:Set E4) ≤ dist (x-y) (u-v) := Metric.infDist_le_dist_of_mem (P.sub_mem hu hv)
    _ = ‖(x-u)-(y-v)‖ := by rw [dist_eq_norm,he]
    _ ≤ ‖x-u‖+‖y-v‖ := norm_sub_le _ _
    _ ≤ 2*r := by linarith

lemma subspace_infDist_smul (P : Submodule ℝ E4) (c : ℝ) (x : E4) :
    Metric.infDist (c • x) (P:Set E4)=|c| * Metric.infDist x (P:Set E4) := by
  rw [←NativeEqualRankPlaneTransfer.projection_residual_eq_infDist,
    ←NativeEqualRankPlaneTransfer.projection_residual_eq_infDist P x,
    map_smul,←smul_sub,norm_smul,Real.norm_eq_abs]

/-- Subtract two actual directions BEFORE the plane transfer. Its cost is
proportional to their actual difference norm, which is small in one parent. -/
theorem incident_difference_near_horizontal {n ell m : ℕ} {D : FiniteScaleSource n} {eta a q r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hr : 0 < r) (hell : 0 < ell)
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor)
    (P : Index → Submodule ℝ E4) (hP : ∀k∈S,Module.finrank ℝ (P k)=ell)
    (hnear : ∀z∈E,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ r)
    (k : Index) (hk : k∈S) (i j : Fin n) (hi : (i,k)∈E) (hj : (j,k)∈E) :
    let Q := spanOf (fun z : Fin n × Index => slopeVector D z.1)
      (List.ofFn (tuple (spatialLabel D (2^m) k)))
    Metric.infDist (slopeVector D i-slopeVector D j) (sliceSpace Q:Set E4) ≤
      6*r+12*(2*r+2/((2^m:ℕ):ℝ))*coefficientCost 2 q ell*‖slopeVector D i-slopeVector D j‖ := by
  intro Q
  let node := spatialLabel D (2^m) k
  let xs : Fin ell → (Fin n × Index) := fun s => (anchor k s,k)
  have hn : node∈nodes D m S := mem_image_of_mem _ hk
  have hchain := (H.1 node hn).2.2.1
  have he : angularTuple D a m (List.ofFn xs)=angularTuple D a m (List.ofFn (tuple node)) := by
    simp only [angularTuple,coarseTuple,List.map_ofFn,Function.comp_def]
    congr 1
    funext s
    exact (H.2.1 k hk s).2
  have hxs : ∀z∈List.ofFn xs,Metric.infDist (slopeVector D z.1) (P k:Set E4) ≤ 2*r := by
    intro z hz
    obtain ⟨s,rfl⟩ := List.mem_ofFn.mp hz
    exact (hnear (anchor k s,k) (H.2.1 k hk s).1).trans (by linarith only [hr])
  have hd := difference_near_submodule (P k) (slopeVector D i) (slopeVector D j) r
    (hnear (i,k) hi) (hnear (j,k) hj)
  have ht := NativeLocalPlanePacketTransfer.matching_chain_plane_transfer h a m
    (pointSet E (point node)) q (2*r) hq (by positivity) ell (P k) (hP k hk)
    (List.ofFn xs) (List.ofFn (tuple node)) he hxs hchain (slopeVector D i-slopeVector D j) hd
  obtain ⟨_hdim,v,hvQ,hvh,hvn⟩ := NativeActualHorizontalGrainSlice.node_graph_direction H hell hq node hn
  have hh := near_horizontal_slice Q hvQ hvh hvn ht
  have hz : removeHeight v (slopeVector D i-slopeVector D j)=slopeVector D i-slopeVector D j := by
    simp only [removeHeight,PiLp.sub_apply,slopeVector_last,sub_self,zero_smul,sub_zero]
  rw [hz] at hh
  nlinarith only [hh]

/-- The original phase-parent bound cancels its rescaling factor on the
plane-gap term. Only the physical error r retains the N-parent multiplier. -/
theorem parent_normalized_horizontal_difference {n ell m : ℕ} {D : FiniteScaleSource n} {eta a q r : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hr : 0 < r) (hell : 0 < ell)
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor)
    (P : Index → Submodule ℝ E4) (hP : ∀k∈S,Module.finrank ℝ (P k)=ell)
    (hnear : ∀z∈E,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ r)
    (k : Index) (hk : k∈S) (i j : Fin n) (hi : (i,k)∈E) (hj : (j,k)∈E)
    (N : ℕ) (hN : 0 < N) (hparent : parentLabel D a N i=parentLabel D a N j) :
    let Q := spanOf (fun z : Fin n × Index => slopeVector D z.1)
      (List.ofFn (tuple (spatialLabel D (2^m) k)))
    Metric.infDist ((N:ℝ) • (slopeVector D i-slopeVector D j)) (sliceSpace Q:Set E4) ≤
      6*(N:ℝ)*r+24*(2*r+2/((2^m:ℕ):ℝ))*coefficientCost 2 q ell := by
  intro Q
  have ht := incident_difference_near_horizontal h hq hr hell H P hP hnear k hk i j hi hj
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hd : ‖slopeVector D i-slopeVector D j‖ ≤ 2/(N:ℝ) := by
    simpa only [dist_eq_norm] using NativeAngularPacketReadback.same_angular_slopeVector_dist
      D a N hN i j (congrArg Prod.fst hparent)
  have hn : (N:ℝ)*‖slopeVector D i-slopeVector D j‖ ≤ 2 := by
    simpa only [mul_comm] using (le_div_iff₀ hNr).mp hd
  have hC := coefficientCost_nonneg (by norm_num : (0:ℝ) ≤ 2) hq ell
  have hscaled := mul_le_mul_of_nonneg_left ht hNr.le
  have hprod := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ 12*(2*r+2/((2^m:ℕ):ℝ))*coefficientCost 2 q ell by positivity)
  rw [subspace_infDist_smul,abs_of_pos hNr]
  nlinarith only [hscaled,hprod]

end NativeParentDirectionDifference
