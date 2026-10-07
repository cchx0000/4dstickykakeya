import Theorems.Thm_StickyKakeya4_native_height_window_relations
import Theorems.Thm_StickyKakeya4_native_window_XY_reference_maps

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeHeightWindowBoundary
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeAnisotropicShortRowGeometry NativeAnisotropicColumnCapacity NativeHeightWindowRelations
open NativeWindowXYReferenceMaps

/-- Only the integer height varies inside a fiber of a time-only map. -/
def heightPreimages (T : ℕ) (q : Index) : Finset Index :=
  (Icc ((T:ℤ)*q (3:Fin 4)) ((T:ℤ)*q (3:Fin 4)+T-1)).image
    (fun t => Function.update q (3:Fin 4) t)

lemma heightPreimages_card (T : ℕ) (hT : 0 < T) (q : Index) :
    (heightPreimages T q).card ≤ T := by
  have hc : (Icc ((T:ℤ)*q (3:Fin 4)) ((T:ℤ)*q (3:Fin 4)+T-1)).card=T := by
    have hh : ((Icc ((T:ℤ)*q (3:Fin 4)) ((T:ℤ)*q (3:Fin 4)+T-1)).card:ℤ)=T := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      ring
    exact_mod_cast hh
  exact (card_image_le).trans_eq hc

lemma mem_heightPreimages {T : ℕ} (hT : 0 < T) (q k : Index)
    (he : windowIndex T 1 k=q) : k∈heightPreimages T q := by
  have hTi : (0:ℤ)<T := by exact_mod_cast hT
  have hheight : k (3:Fin 4)/(T:ℤ)=q (3:Fin 4) := by
    simpa only [windowIndex,if_true] using congrFun he (3:Fin 4)
  have hlo := (Int.le_ediv_iff_mul_le hTi).mp hheight.ge
  have hhi := (Int.ediv_lt_iff_lt_mul hTi).mp (show k (3:Fin 4)/(T:ℤ)<q (3:Fin 4)+1 by omega)
  apply mem_image.mpr
  refine ⟨k (3:Fin 4),mem_Icc.mpr ⟨by nlinarith,by nlinarith⟩,?_⟩
  funext v
  by_cases hv : v=(3:Fin 4)
  · simp [hv]
  · have hh : k v=q v := by simpa only [windowIndex,if_neg hv,Nat.cast_one,Int.ediv_one] using congrFun he v
    simpa [hv] using hh.symm

lemma card_le_height_image (T : ℕ) (hT : 0 < T) (S : Finset Index) :
    S.card ≤ T*(S.image (windowIndex T 1)).card := by
  have hm : ∀k∈S,windowIndex T 1 k∈S.image (windowIndex T 1) := fun _ hk => mem_image_of_mem _ hk
  apply card_le_mul_card_image_of_maps_to hm T
  intro q _hq
  exact (card_le_card (show S.filter (fun k => windowIndex T 1 k=q)⊆heightPreimages T q from
    fun k hk => mem_heightPreimages hT q k (mem_filter.mp hk).2)).trans (heightPreimages_card T hT q)

lemma time_map_column {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (f fineTime coarseTime : ℕ) (ht : coarseTime ≤ fineTime) (k : Index) :
    windowIndex (2^(fineTime-coarseTime)) 1
      (columnLabel D a N p (64/((2^f:ℕ):ℝ)) (64/((2^fineTime:ℕ):ℝ)) k)=
      columnLabel D a N p (64/((2^f:ℕ):ℝ)) (64/((2^coarseTime:ℕ):ℝ)) k := by
  have he := coarsen_column D a N p f fineTime f coarseTime le_rfl ht k
  convert he using 1
  funext v
  by_cases hv : v=(3:Fin 4)
  · simp only [windowIndex,coarsen,hv,if_true]
  · simp only [windowIndex,coarsen,if_neg hv,Nat.sub_self,pow_zero,Nat.cast_one,Int.ediv_one]

lemma points_time_image {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f fineTime coarseTime : ℕ)
    (ht : coarseTime ≤ fineTime) (E : Finset (Fin n × Index)) (p : Parent) :
    (points D a m f fineTime E p).image (windowIndex (2^(fineTime-coarseTime)) 1)=
      points D a m f coarseTime E p := by
  simp only [points,image_image,Function.comp_def]
  apply image_congr
  intro z _hz
  exact time_map_column D a (2^m) p f fineTime coarseTime ht z.2

lemma point_count_bounds {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f fineTime coarseTime : ℕ)
    (ht : coarseTime ≤ fineTime) (E : Finset (Fin n × Index)) (p : Parent) :
    (points D a m f coarseTime E p).card ≤ (points D a m f fineTime E p).card ∧
      (points D a m f fineTime E p).card ≤
        2^(fineTime-coarseTime)*(points D a m f coarseTime E p).card := by
  constructor
  · rw [←points_time_image D a m f fineTime coarseTime ht E p]
    exact card_image_le
  · have hh := card_le_height_image (2^(fineTime-coarseTime)) (by positivity) (points D a m f fineTime E p)
    rw [points_time_image D a m f fineTime coarseTime ht E p] at hh
    exact hh

/-- The only H>1 boundary in the prepared normalization has3≤b≤6. Time
coarsening from max(6,b) has at most8 labels per fiber, hence the exact
H-weighted lower transfers without loss and the upper loses at most8. -/
theorem weighted_point_counts_max_six {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f b : ℕ)
    (hb : 3 ≤ b) (E : Finset (Fin n × Index)) (p : Parent) :
    (64/((2^(max 6 b):ℕ):ℝ))*(points D a m f (max 6 b) E p).card ≤
        (64/((2^b:ℕ):ℝ))*(points D a m f b E p).card ∧
      (64/((2^b:ℕ):ℝ))*(points D a m f b E p).card ≤
        8*((64/((2^(max 6 b):ℕ):ℝ))*(points D a m f (max 6 b) E p).card) := by
  have htime : b ≤ max 6 b := le_max_right _ _
  have hT : 2^(max 6 b-b) ≤ (8:ℕ) := by
    have he : max 6 b-b ≤ 3 := by omega
    exact (Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) he).trans_eq (by norm_num)
  obtain ⟨hsmall,hlarge⟩ := point_count_bounds D a m f (max 6 b) b htime E p
  have hsmallR : ((points D a m f b E p).card:ℝ) ≤ (points D a m f (max 6 b) E p).card := by exact_mod_cast hsmall
  have hlargeR : ((points D a m f (max 6 b) E p).card:ℝ) ≤
      ((2^(max 6 b-b):ℕ):ℝ)*(points D a m f b E p).card := by exact_mod_cast hlarge
  have hTR : ((2^(max 6 b-b):ℕ):ℝ) ≤ 8 := by exact_mod_cast hT
  have hheight := dyadic_height_eq b (max 6 b) htime
  constructor
  · rw [hheight]
    calc
      _ ≤ (64/((2^(max 6 b):ℕ):ℝ))*
          (((2^(max 6 b-b):ℕ):ℝ)*(points D a m f b E p).card) :=
        mul_le_mul_of_nonneg_left hlargeR (by positivity)
      _ = _ := by ring
  · rw [hheight]
    calc
      _ ≤ (((2^(max 6 b-b):ℕ):ℝ)*(64/((2^(max 6 b):ℕ):ℝ)))*
          (points D a m f (max 6 b) E p).card := mul_le_mul_of_nonneg_left hsmallR (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hTR
          (show 0 ≤ (64/((2^(max 6 b):ℕ):ℝ))*(points D a m f (max 6 b) E p).card by positivity)
        simpa only [mul_assoc] using hh

end NativeHeightWindowBoundary
