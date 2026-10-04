import Theorems.Thm_StickyKakeya4_native_coarse_original_geometry
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeCoarseOriginalHeights
open Classical Finset NativeOriginalSlicePopulation NativeCoarseOriginalIncidences NativeCoarseOriginalGeometry
variable {T : Type*}
/-- The true separation of two distinct integer-grid coordinate centers. -/
theorem integer_center_gap {mesh : ℝ} (hm : 0 < mesh) (a b : ℤ) (hab : a ≠ b) :
    mesh ≤ |mesh*((a:ℝ)+1/2)-mesh*((b:ℝ)+1/2)| := by
  have horder : a+1 ≤ b ∨ b+1 ≤ a := by omega
  rcases horder with h | h
  · have hreal : (a:ℝ)+1 ≤ b := by exact_mod_cast h
    have hh := mul_le_mul_of_nonneg_left hreal hm.le
    have ha := neg_le_abs (mesh*((a:ℝ)+1/2)-mesh*((b:ℝ)+1/2))
    nlinarith only [hh,ha]
  · have hreal : (b:ℝ)+1 ≤ a := by exact_mod_cast h
    have hh := mul_le_mul_of_nonneg_left hreal hm.le
    have ha := le_abs_self (mesh*((a:ℝ)+1/2)-mesh*((b:ℝ)+1/2))
    nlinarith only [hh,ha]
/-- The point-label map is injective into actual physical coordinates. -/
theorem coordinates_injective (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    {R : ℝ} (hR : 0 < R) : Function.Injective (coordinates P R) := by
  have hm : 0 < P.σ/R := div_pos (P.scale_pos hP) hR
  intro c d h
  apply Prod.ext
  · funext j
    have hh := congrArg (fun v : ShearBinFibers.Point => v.1 j) h
    dsimp [coordinates,ShearBinFibers.oldCenter] at hh
    have he : (c.1 j:ℝ)=(d.1 j:ℝ) := by nlinarith only [hh,hm]
    exact_mod_cast he
  · have hh := congrArg Prod.snd h
    dsimp [coordinates,ShearBinFibers.oldCenter] at hh
    have he : (c.2:ℝ)=(d.2:ℝ) := by nlinarith only [hh,hm]
    exact_mod_cast he
/-- Heights are actual coarse-grid heights, hence separated at the SAME
 normalized mesh sigma/R. No representative-height spacing is assumed. -/
theorem actual_heights_separated (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (E : Finset (T × Cell)) {R : ℝ} (hR : 0 < R) :
    ∀ z ∈ heights P E R, ∀ w ∈ heights P E R, z ≠ w → P.σ/R ≤ |z-w| := by
  intro z hz w hw hzw
  obtain ⟨e,_he,rfl⟩ := mem_image.mp hz
  obtain ⟨f,_hf,rfl⟩ := mem_image.mp hw
  have htime : e.1.2 ≠ f.1.2 := by
    intro hh
    apply hzw
    simp only [height,coordinates,ShearBinFibers.oldCenter,hh]
  exact integer_center_gap (div_pos (P.scale_pos hP) hR) e.1.2 f.1.2 htime
/-- The actual height alphabet inherits the proved physical unit box. -/
theorem actual_heights_box (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (E : Finset (T × Cell)) (hE : E ⊆ P.incidences)
    (hoff : ∀ t ∈ IncidenceBinTransfer.usedTubes P.incidences, ∀ j, |P.offset t j| ≤ 1) :
    ∀ z ∈ heights P E (normalization P), |z| ≤ 1 := by
  intro z hz
  obtain ⟨⟨c,t⟩,hc,rfl⟩ := mem_image.mp hz
  exact (normalized_coordinate_box P hP E hE hoff c t hc).1
/-- Restriction to a literal physical height interval, on original image labels. -/
def heightWindow (P : PhysicalRescalingIncidenceTransfer.Data T) (E : Finset (T × Cell))
    (R lo width : ℝ) : Finset (Cell × T) :=
  (incidences P E).filter (fun e => lo ≤ height P R e.1 ∧ height P R e.1 ≤ lo+width)
theorem heightWindow_original_readback (P : PhysicalRescalingIncidenceTransfer.Data T)
    (E : Finset (T × Cell)) (R lo width : ℝ) :
    incidences P (pullback P E (heightWindow P E R lo width))=heightWindow P E R lo width :=
  pullback_image P E _ (filter_subset _ _)
theorem heightWindow_actual_diameter (P : PhysicalRescalingIncidenceTransfer.Data T)
    (E : Finset (T × Cell)) (R lo width : ℝ) :
    ∀ c ∈ TwoTubePathCollisionCount.points (heightWindow P E R lo width),
    ∀ d ∈ TwoTubePathCollisionCount.points (heightWindow P E R lo width),
      |height P R c-height P R d| ≤ width := by
  intro c hc d hd
  obtain ⟨e,he,rfl⟩ := mem_image.mp hc
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hd
  have hce := (mem_filter.mp he).2
  have hdf := (mem_filter.mp hf).2
  exact abs_le.mpr ⟨by linarith only [hce.1,hce.2,hdf.1,hdf.2],
    by linarith only [hce.1,hce.2,hdf.1,hdf.2]⟩
end NativeCoarseOriginalHeights
