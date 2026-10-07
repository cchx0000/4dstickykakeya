import Theorems.Thm_StickyKakeya4_native_spatial_shadow_point_menu
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeRawShadowPointComparison
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalCellChartGeometry NativeOriginalPaddedCells
open NativeLocalParentPhysicalMap NativeCoarsePointMultiplicity NativeCoarseShadingCapacity
open NativeSpatialAngularGeometry NativeSpatialShadowPointMenu

/-- Equal actual projected labels confine the literal original cell centers.
The inverse factor512 belongs to the unchanged common physical map. -/
lemma same_shadow_coordinate_close {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N B : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (hmesh : (B:ℝ)*D.thickness/128=32/(N:ℝ))
    (rep : Parent → Fin n) (z w : Fin n × Index)
    (hz : z∈incidences original) (hw : w∈incidences original)
    (hzrep : parentLabel D a N (rep (parentLabel D a N z.1))=parentLabel D a N z.1)
    (hwrep : parentLabel D a N (rep (parentLabel D a N w.1))=parentLabel D a N w.1)
    (hpoint : pointLabel D a N B rep z=pointLabel D a N B rep w) (v : Fin 4) :
    |cellCenter (mesh D) z.2 v-cellCenter (mesh D) w.2 v| ≤ 1024*(64/(N:ℝ)) := by
  have hfz := projected_front_near_physical h original horiginal ha N hN hscale
    z.1 _ z.2 ((mem_incidences original z.1 z.2).mp hz) hzrep v
  have hfw := projected_front_near_physical h original horiginal ha N hN hscale
    w.1 _ w.2 ((mem_incidences original w.1 w.2).mp hw) hwrep v
  unfold pointLabel projectedLabel at hpoint
  rw [hmesh] at hpoint
  have hfront := same_cell_coordinate_close (by positivity : (0:ℝ)<32/(N:ℝ))
    _ _ hpoint v
  have hphysical := (abs_sub_le
    (physicalMap D a 1 (0,0) (cellCenter (mesh D) z.2) v)
    (frontPoint D a (0,0) (rep (parentLabel D a N z.1)) z.2 v)
    (physicalMap D a 1 (0,0) (cellCenter (mesh D) w.2) v)).trans
      (add_le_add (by simpa only [abs_sub_comm] using hfz)
        ((abs_sub_le _ (frontPoint D a (0,0) (rep (parentLabel D a N w.1)) w.2 v) _).trans
          (add_le_add hfront hfw)))
  rw [physicalMap_zero_sub,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)] at hphysical
  simp only [div_eq_mul_inv] at hphysical ⊢
  nlinarith

/-- One actual projected shadow point meets at most2051^4 literal raw
spatial64/N cells. Representatives remain globally fixed; no separation of
the represented directions is needed. -/
theorem shadow_spatial_image_card {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N B : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (hmesh : (B:ℝ)*D.thickness/128=32/(N:ℝ))
    (rep : Parent → Fin n) (F : Finset (Fin n × Index)) (hF : F⊆incidences original)
    (hrep : ∀z∈F,parentLabel D a N (rep (parentLabel D a N z.1))=parentLabel D a N z.1)
    (q : Index) (hpoint : ∀z∈F,pointLabel D a N B rep z=q) :
    (F.image (fun z => spatialLabel D N z.2)).card ≤ 2051^4 := by
  by_cases hne : F.Nonempty
  · obtain ⟨w,hw⟩ := hne
    have hsub : F.image (fun z => spatialLabel D N z.2) ⊆
        integerBox 4 1025 (spatialLabel D N w.2) := by
      intro p hp
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hp
      exact cellIndex_mem_box (by positivity : (0:ℝ)<64/(N:ℝ))
        _ _ 1024 (same_shadow_coordinate_close h original horiginal ha N B hN hscale hmesh
          rep z w (hF hz) (hF hw) (hrep z hz) (hrep w hw)
          ((hpoint z hz).trans (hpoint w hw).symm))
    exact (card_le_card hsub).trans_eq (integerBox_card 4 1025 _)
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

/-- Both occupied point images of any unchanged original incidence set are
comparable by universal constants, in both directions. -/
theorem point_image_card_comparison {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N B : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (hmesh : (B:ℝ)*D.thickness/128=32/(N:ℝ))
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hrep : ∀z∈E,parentLabel D a N (rep (parentLabel D a N z.1))=parentLabel D a N z.1) :
    (E.image (pointLabel D a N B rep)).card ≤
      2401*(E.image (fun z => spatialLabel D N z.2)).card ∧
    (E.image (fun z => spatialLabel D N z.2)).card ≤
      2051^4*(E.image (pointLabel D a N B rep)).card := by
  constructor
  · have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images E
      (pointLabel D a N B rep) (fun z => spatialLabel D N z.2) (2401:ℝ) (by
        intro q _hq
        exact_mod_cast spatial_point_image_card h original horiginal ha N B hN hscale hmesh rep
          (E.filter (fun z => spatialLabel D N z.2=q)) ((filter_subset _ _).trans hE)
          (fun z hz => hrep z (mem_filter.mp hz).1) q (fun _z hz => (mem_filter.mp hz).2))
    exact_mod_cast hh
  · have hh := NativeTangentGridCoarsening.image_card_le_real_mul_of_fiber_images E
      (fun z => spatialLabel D N z.2) (pointLabel D a N B rep) ((2051:ℝ)^4) (by
        intro q _hq
        exact_mod_cast shadow_spatial_image_card h original horiginal ha N B hN hscale hmesh rep
          (E.filter (fun z => pointLabel D a N B rep z=q)) ((filter_subset _ _).trans hE)
          (fun z hz => hrep z (mem_filter.mp hz).1) q (fun _z hz => (mem_filter.mp hz).2))
    exact_mod_cast hh

/-- Source-facing comparison uses the SAME R, dyadic block, representative,
and unchanged subset E that define the existing full shadow source. -/
theorem same_R_point_image_card_comparison {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (hR : ∀z∈E,z.1∈R) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level) :
    let rep := NativeCoarseDirectionThinning.representative h R a (2^m)
    let point := pointLabel D a (2^m) (NativeCoarseDyadicShading.block level m) rep
    (E.image point).card ≤ 2401*(E.image (fun z => spatialLabel D (2^m) z.2)).card ∧
    (E.image (fun z => spatialLabel D (2^m) z.2)).card ≤ 2051^4*(E.image point).card := by
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale hdy hm]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  exact point_image_card_comparison h original horiginal ha (2^m) _ (by positivity) hscale
    (NativeCoarseDyadicShading.block_mesh hdy hm) _ E hE (fun z hz =>
      (NativeCoarseDirectionThinning.representative_spec h R a (2^m)
        (mem_image_of_mem _ (hR z hz))).2)

end NativeRawShadowPointComparison
