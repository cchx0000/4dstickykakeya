import Theorems.Thm_StickyKakeya4_native_anisotropic_short_row_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeAnisotropicColumnMenus
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeLocalParentPhysicalMap NativeSpatialAngularGeometry
open NativeAnisotropicShortRowGeometry
open scoped BigOperators

lemma columnHalo_symm (s t : ℕ) (x y : Index) (h : x∈columnHalo s t y) :
    y∈columnHalo s t x := by
  apply Fintype.mem_piFinset.mpr
  intro v
  have hh := Fintype.mem_piFinset.mp h v
  simp only [mem_Icc] at hh ⊢
  constructor <;> omega

lemma columnHalo_trans (s t s' t' : ℕ) (x y z : Index)
    (hxy : x∈columnHalo s t y) (hyz : y∈columnHalo s' t' z) :
    x∈columnHalo (s+s') (t+t') z := by
  apply Fintype.mem_piFinset.mpr
  intro v
  have hx := Fintype.mem_piFinset.mp hxy v
  have hy := Fintype.mem_piFinset.mp hyz v
  simp only [mem_Icc] at hx hy ⊢
  split_ifs at hx hy ⊢ <;> push_cast <;> constructor <;> omega

lemma same_floor_width_close {x y width : ℝ} (hw : 0 < width)
    (he : ⌊x/width⌋=⌊y/width⌋) : |x-y| ≤ width := by
  have hxlo := (le_div_iff₀ hw).mp (Int.floor_le (x/width))
  have hxhi := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/width))
  have hylo := (le_div_iff₀ hw).mp (Int.floor_le (y/width))
  have hyhi := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (y/width))
  rw [he] at hxlo hxhi
  exact abs_le.mpr ⟨by nlinarith only [hxlo,hyhi],by nlinarith only [hylo,hxhi]⟩

/-- The independent height coordinate really has raw width H, including the
original chart translation. It is not the isotropic global shadow's height. -/
lemma same_column_height_close {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (p : Parent) (sigma H : ℝ) (hH : 0 < H) (k l : Index)
    (he : columnLabel D a N p sigma H k=columnLabel D a N p sigma H l) :
    |cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4)| ≤ H := by
  have hh := congrFun he (3:Fin 4)
  simp only [columnLabel,chartWidth,if_true] at hh
  have hc := same_floor_width_close (by positivity : (0:ℝ)<H/512) hh
  rw [chart_height_sub,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)] at hc
  linarith only [hc]

/-- In one raw sigma-cube, the existing shear changes horizontal coordinates
by at most four sigma bins and height by at most one H bin when sigma≤H. -/
theorem same_raw_column_mem_halo {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p)
    (H : ℝ) (hH : 0 < H) (hscale : 64/(K:ℝ) ≤ H) (k l : Index)
    (hkl : spatialLabel D K k=spatialLabel D K l) :
    columnLabel D a N p (64/(K:ℝ)) H k∈
      columnHalo 5 2 (columnLabel D a N p (64/(K:ℝ)) H l) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hc := spatial_coordinate_close D K hK k l hkl
  apply Fintype.mem_piFinset.mpr
  intro v
  refine Fin.lastCases ?_ (fun v => ?_) v
  · simp only [columnLabel,chartWidth,show (Fin.last 3:Fin 4)=3 by rfl,if_true]
    apply floor_mem_interval 1
    rw [←sub_div,chart_height_sub,abs_div,abs_of_pos (by positivity : (0:ℝ)<H/512)]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num only [Nat.cast_one,one_mul]
    exact div_le_div_of_nonneg_right ((hc 3).trans hscale) (by norm_num)
  · have hv : v.castSucc≠(3:Fin 4) := Fin.castSucc_ne_last v
    simp only [columnLabel,chartWidth,if_neg hv]
    apply floor_mem_interval 4
    rw [←sub_div,NativeAnisotropicShortRowGeometry.chart_spatial_sub,abs_div,
      abs_of_pos (by positivity : (0:ℝ)<(N:ℝ)*(64/(K:ℝ))/512)]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)]
    apply (div_le_iff₀ (by positivity)).mpr
    have hs := parent_slope_bound h N hN p i hp v
    have h1 : |(N:ℝ)*(cellCenter (mesh D) k v.castSucc-cellCenter (mesh D) l v.castSucc)| ≤
        (N:ℝ)*(64/(K:ℝ)) := by
      rw [abs_mul,abs_of_pos hNr]
      exact mul_le_mul_of_nonneg_left (hc v.castSucc) hNr.le
    have h2 : |(p.1 v:ℝ)*(cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4))| ≤
        3*(N:ℝ)*(64/(K:ℝ)) := by
      rw [abs_mul]
      exact mul_le_mul hs (hc 3) (abs_nonneg _) (by positivity)
    have hh := (abs_sub _ _).trans (add_le_add h1 h2)
    linarith only [hh]

/-- Two original points in one anisotropic column and the same raw height
sigma-bin differ horizontally by at most4sigma before taking integer labels. -/
theorem same_column_same_height_spatial_close {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    (p : Parent) (i : Fin n) (hp : parentLabel D a N i=p)
    (H : ℝ) (k l : Index)
    (hcol : columnLabel D a N p (64/(K:ℝ)) H k=columnLabel D a N p (64/(K:ℝ)) H l)
    (ht : spatialLabel D K k (3:Fin 4)=spatialLabel D K l (3:Fin 4)) (v : Fin 3) :
    |cellCenter (mesh D) k v.castSucc-cellCenter (mesh D) l v.castSucc| ≤ 4*(64/(K:ℝ)) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hσ : (0:ℝ)<64/(K:ℝ) := by positivity
  have ht' := same_floor_width_close hσ ht
  have he := congrFun hcol v.castSucc
  have hv : v.castSucc≠(3:Fin 4) := Fin.castSucc_ne_last v
  simp only [columnLabel,chartWidth,if_neg hv] at he
  have he' := same_floor_width_close (by positivity : (0:ℝ)<(N:ℝ)*(64/(K:ℝ))/512) he
  rw [NativeAnisotropicShortRowGeometry.chart_spatial_sub,abs_div,abs_of_pos (by norm_num : (0:ℝ)<512)] at he'
  have hsp : |(N:ℝ)*(cellCenter (mesh D) k v.castSucc-cellCenter (mesh D) l v.castSucc)-
      (p.1 v:ℝ)*(cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4))| ≤
      (N:ℝ)*(64/(K:ℝ)) := by linarith only [he']
  have hs := parent_slope_bound h N hN p i hp v
  have hm : |(p.1 v:ℝ)*(cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4))| ≤
      3*(N:ℝ)*(64/(K:ℝ)) := by
    rw [abs_mul]
    exact mul_le_mul hs ht' (abs_nonneg _) (by positivity)
  have hh := (abs_add_le
    ((N:ℝ)*(cellCenter (mesh D) k v.castSucc-cellCenter (mesh D) l v.castSucc)-
      (p.1 v:ℝ)*(cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4)))
    ((p.1 v:ℝ)*(cellCenter (mesh D) k (3:Fin 4)-cellCenter (mesh D) l (3:Fin 4)))).trans
      (add_le_add hsp hm)
  rw [sub_add_cancel,abs_mul,abs_of_pos hNr] at hh
  exact (mul_le_mul_iff_right₀ hNr).mp (by nlinarith only [hh])

end NativeAnisotropicColumnMenus
