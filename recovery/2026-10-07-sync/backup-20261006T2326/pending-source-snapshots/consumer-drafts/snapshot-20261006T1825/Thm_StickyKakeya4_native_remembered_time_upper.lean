/- UNVERIFIED unconditional time support upper for the literal local source. -/
import Theorems.Thm_StickyKakeya4_native_remembered_cell_halo
import Theorems.Thm_StickyKakeya4_native_configured_height_caps

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeRememberedTimeUpper
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeLocalParentCells NativeLocalCellCoherence
open NativeConfiguredTimeCoarsening NativeConfiguredHeightCaps

/-- All retained native local cells have center height in[-1,1]. This uses
the actual intermediate shading, not an assumed output support box. -/
theorem local_center_time_bound {n : ℕ} {C : FiniteScaleSource n} {eta : ℝ}
    (hC : IsWangZakharovNativeFiniteInput C eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (ha : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (hs1 : (N:ℝ)*C.thickness/64 ≤ 1)
    (i : Fin n) (k : Index) (hk : k∈cells i) :
    |cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)) (3:Fin 4)| ≤ 1 := by
  have hd := hC.1.2.1
  have he : 0 < (N:ℝ)*C.thickness/128 := by positivity
  have ho := (NativeOriginalParentPhysicalData.original_cell_bounds hC cells hcells 0 ha
    ((NativeCubicalIncidenceCounts.mem_incidences cells i k).mpr hk)).1
  change |NativeOriginalPaddedCells.oldTime C 0 k| ≤ 1 at ho
  have hf : |frontPoint C 0 N p i k (3:Fin 4)| ≤ 1/128 := by
    rw [frontPoint_height,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 128)]
    exact div_le_div_of_nonneg_right ho (by norm_num)
  have hr := cell_center_coordinate_error he (frontPoint C 0 N p i k) (3:Fin 4)
  change |frontPoint C 0 N p i k (3:Fin 4)-
    cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)) (3:Fin 4)| ≤ _ at hr
  have ht := abs_sub_le
    (cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p (i,k)) (3:Fin 4))
    (frontPoint C 0 N p i k (3:Fin 4)) 0
  rw [sub_zero,sub_zero,abs_sub_comm] at ht
  linarith only [hf,hr,ht,hs1]

/-- The actual integer final time image has at most6/sigma labels. No
height lower bound or equal occupancy of different bins is used. -/
theorem local_time_card {n : ℕ} {C : FiniteScaleSource n} {eta : ℝ}
    (hC : IsWangZakharovNativeFiniteInput C eta) (cells : Fin n → Finset Index)
    (hcells : ∀i,C.shading i=wzCellShading (mesh C) cells i)
    (ha : ∀i,wzGraphTime (C.line i) 0-mark (C.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hN : 0 < N) (p : Parent) (hs1 : (N:ℝ)*C.thickness/64 ≤ 1)
    (E : Finset (Fin n × Index)) (hE : E⊆NativeCubicalIncidenceCounts.incidences cells) :
    ((E.image (fun z => localCellLabel C 0 N p z (3:Fin 4))).card:ℝ) ≤
      6/((N:ℝ)*C.thickness/64) := by
  let sigma : ℝ := (N:ℝ)*C.thickness/64
  have hs : 0 < sigma := by dsimp [sigma]; have hd := hC.1.2.1; positivity
  let H := E.image (fun z => localCellLabel C 0 N p z (3:Fin 4))
  let time := finalTime (256*sigma)
  have htime (z : Fin n × Index) : time (localCellLabel C 0 N p z (3:Fin 4))=
      cellCenter ((N:ℝ)*C.thickness/128) (localCellLabel C 0 N p z) (3:Fin 4) := by
    dsimp [time,finalTime,sigma,cellCenter]
    ring
  have hbox : ∀t∈H.image time,(-1:ℝ) ≤ t ∧ t ≤ -1+2 := by
    intro t ht
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ht
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hj
    rw [htime]
    have hb := local_center_time_bound hC cells hcells ha N hN p hs1 z.1 z.2
      ((NativeCubicalIncidenceCounts.mem_incidences cells _ _).mp (hE hz))
    simpa only [show (-1:ℝ)+2=1 by norm_num] using abs_le.mp hb
  have hcard : (H.image time).card=H.card := by
    apply card_image_of_injective
    intro x y he
    have hm : 256*sigma/512 ≠ 0 := by positivity
    change (256*sigma/512)*((x:ℝ)+1/2)=(256*sigma/512)*((y:ℝ)+1/2) at he
    exact_mod_cast add_right_cancel (mul_left_cancel₀ hm he)
  have hh := unconditional_interval_cap H (256*sigma) (by positivity) (-1) 2 (by norm_num)
  change (((H.image time).filter (fun z => -1≤z ∧ z≤-1+2)).card:ℝ) ≤ _ at hh
  rw [filter_eq_self.mpr hbox,hcard] at hh
  have hm := mul_le_mul_of_nonneg_right hh hs.le
  have he : (2/(256*sigma/512)+2)*sigma=4+2*sigma := by field_simp [hs.ne']; ring
  rw [he] at hm
  apply (le_div_iff₀ hs).mpr
  change sigma ≤ 1 at hs1
  linarith only [hm,hs1]

end NativeRememberedTimeUpper
