import Theorems.Thm_StickyKakeya4_native_actual_offset_menu
import Theorems.Thm_StickyKakeya4_native_height_metric_menu
import Theorems.Thm_StickyKakeya4_native_translated_grain_height_metric
import Theorems.Thm_StickyKakeya4_native_anisotropic_short_row_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeNormalizedOffsetTime
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeLocalParentPhysicalMap NativeSpatialAngularGeometry
open NativeNormalizedCellRelativeMenu NativeHeightMetricMenu NativeTranslatedGrainHeightOverlap
open NativeTranslatedGrainHeightMetric

lemma same_floor_distance {width x y : ℝ} (hw : 0 < width) (h : ⌊x/width⌋=⌊y/width⌋) :
    |x-y| ≤ width := by
  have hxlo := (le_div_iff₀ hw).mp (Int.floor_le (x/width))
  have hxhi := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/width))
  have hylo := (le_div_iff₀ hw).mp (Int.floor_le (y/width))
  have hyhi := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (y/width))
  rw [h] at hxlo hxhi
  exact abs_le.mpr ⟨by linarith only [hxlo,hyhi],by linarith only [hylo,hxhi]⟩

lemma quantized_time_distance {width : ℝ} (hw : 0 < width) (x y : ℝ) :
    |width*(⌊x/width⌋:ℝ)-width*(⌊y/width⌋:ℝ)| ≤ |x-y|+width := by
  have hxlo := (le_div_iff₀ hw).mp (Int.floor_le (x/width))
  have hxhi := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/width))
  have hylo := (le_div_iff₀ hw).mp (Int.floor_le (y/width))
  have hyhi := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (y/width))
  have hdlo := neg_abs_le (x-y)
  have hdhi := le_abs_self (x-y)
  exact abs_le.mpr ⟨by linarith only [hxhi,hylo,hdlo],by linarith only [hxlo,hyhi,hdhi]⟩

/-- The existing parent map contracts time by exactly512, independently
of the parent slope, horizontal scale, and common time translation. -/
lemma physical_cell_time_distance {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N M : ℕ) (hM : 0 < M) (p : Parent) (k l : Index)
    (hcell : physicalCell D a N M p k=physicalCell D a N M p l) :
    |cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4)| ≤ 512*(64/(M:ℝ)) := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hh := congrFun hcell (3:Fin 4)
  change ⌊physicalPoint D a N p k (3:Fin 4)/(64/(M:ℝ))⌋=
    ⌊physicalPoint D a N p l (3:Fin 4)/(64/(M:ℝ))⌋ at hh
  have ht := same_floor_distance (by positivity : (0:ℝ)<64/(M:ℝ)) hh
  change |physicalMap D a N p (cellCenter (mesh D) k) (3:Fin 4)-
    physicalMap D a N p (cellCenter (mesh D) l) (3:Fin 4)| ≤ 64/(M:ℝ) at ht
  rw [NativeAnisotropicShortRowGeometry.chart_height_sub D a N p
    (cellCenter (mesh D) l) (cellCenter (mesh D) k),abs_div] at ht
  rw [abs_of_pos (by norm_num : (0:ℝ)<512)] at ht
  have ht' := (div_le_iff₀ (by norm_num : (0:ℝ)<512)).mp ht
  simpa only [mul_comm] using ht'

/-- Raw F is indexed by actual original spatial-height bins. Their
rounding costs one raw parent-width bin in addition to the physical window. -/
theorem raw_height_window {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N M m : ℕ) (hM : 0 < M) (p : Parent) (k l : Index)
    (hcell : physicalCell D a N M p k=physicalCell D a N M p l) :
    |rawHeightCoordinate m (rawHeight D m k)-rawHeightCoordinate m (rawHeight D m l)| ≤
      512*(64/(M:ℝ))+meshWidth m := by
  have hraw := quantized_time_distance (meshWidth_pos m)
    (cellCenter (mesh D) k (3:Fin 4)) (cellCenter (mesh D) l (3:Fin 4))
  have ht := physical_cell_time_distance D a N M hM p k l hcell
  change |meshWidth m*(⌊cellCenter (mesh D) k (3:Fin 4)/meshWidth m⌋:ℝ)-
    meshWidth m*(⌊cellCenter (mesh D) l (3:Fin 4)/meshWidth m⌋:ℝ)| ≤ _
  exact hraw.trans (by linarith only [ht])

theorem chart_height_window {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N M m : ℕ) (hM : 0 < M) (p : Parent) (k l : Index) (shift : ℝ)
    (hcell : physicalCell D a N M p k=physicalCell D a N M p l) :
    |chartHeightCoordinate m shift (rawHeight D m k)-chartHeightCoordinate m shift (rawHeight D m l)| ≤
      64/(M:ℝ)+meshWidth m/512 := by
  have hh := raw_height_window D a N M m hM p k l hcell
  rw [chartHeightCoordinate_distance m shift] at hh
  linarith only [hh]

/-- The actual translated reference-height centers obey the same window
bound; their label is not identified with the raw height label. -/
theorem translated_height_window {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N M m : ℕ) (hM : 0 < M) (p : Parent) (k l : Index)
    (hcell : physicalCell D a N M p k=physicalCell D a N M p l) :
    |referenceHeight m (translatedHeight D a m k)-referenceHeight m (translatedHeight D a m l)| ≤
      64/(M:ℝ)+meshWidth m/512 := by
  have hraw := quantized_time_distance (meshWidth_pos m)
    (cellCenter (mesh D) k (3:Fin 4)-(shift D a:ℝ)*mesh D)
    (cellCenter (mesh D) l (3:Fin 4)-(shift D a:ℝ)*mesh D)
  rw [sub_sub_sub_cancel_right] at hraw
  have ht := physical_cell_time_distance D a N M hM p k l hcell
  have hbound : |meshWidth m*(translatedHeight D a m k:ℝ)-meshWidth m*(translatedHeight D a m l:ℝ)| ≤
      512*(64/(M:ℝ))+meshWidth m := by
    have hh := hraw.trans (show
      |cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4)|+meshWidth m ≤
        512*(64/(M:ℝ))+meshWidth m from by linarith only [ht])
    simpa only [translatedHeight_readback,meshWidth] using hh
  have he : referenceHeight m (translatedHeight D a m k)-referenceHeight m (translatedHeight D a m l)=
      (meshWidth m*(translatedHeight D a m k:ℝ)-meshWidth m*(translatedHeight D a m l:ℝ))/512 := by
    unfold referenceHeight meshWidth
    ring
  rw [he,abs_div]
  rw [abs_of_pos (by norm_num : (0:ℝ)<512)]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<512)).mpr
  linarith only [hbound]

end NativeNormalizedOffsetTime
