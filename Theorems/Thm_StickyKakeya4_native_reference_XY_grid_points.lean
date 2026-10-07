import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_linear

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeReferenceXYGridPoints
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeSpatialAngularGeometry NativeSquaredGrainQueries
open NativeOriginalPacketReference NativeAnisotropicShortRowGeometry NativeLocalParentPhysicalMap
open NativePhaseHeightPopulation NativeContractedUnitParent NativeTranslatedGrainHeightOverlap NativeGrainHeightProjectionSource

/-- Original coarse height and squared raw spatial mesh, before normalization. -/
def rho (m : ℕ) : ℝ := 64/((2^m:ℕ):ℝ)
def sigma (m : ℕ) : ℝ := 64/((2^(phaseDepth m):ℕ):ℝ)
/-- Actual fixed XY working mesh. -/
def mu (m : ℕ) : ℝ := rho m/64
/-- Actual reference horizontal mesh after the parent map. -/
def prefMesh (m : ℕ) : ℝ := ((2^m:ℕ):ℝ)*sigma m/512
def heightMesh (m : ℕ) : ℝ := rho m/512

lemma mu_pos (m : ℕ) : 0 < mu m := by unfold mu rho; positivity
lemma rho_pos (m : ℕ) : 0 < rho m := by unfold rho; positivity
lemma sigma_pos (m : ℕ) : 0 < sigma m := by unfold sigma; positivity
lemma prefMesh_pos (m : ℕ) : 0 < prefMesh m := by unfold prefMesh; exact div_pos (mul_pos (by positivity) (sigma_pos m)) (by norm_num)
lemma heightMesh_pos (m : ℕ) : 0 < heightMesh m := div_pos (rho_pos m) (by norm_num)

lemma prefMesh_eq (m : ℕ) (hm : 6 ≤ m) : prefMesh m=8*mu m := by
  unfold prefMesh sigma mu rho
  rw [squared_scale_identity m hm]
  have hN : (((2^m:ℕ):ℝ))≠0 := by positivity
  field_simp
  ring

lemma heightMesh_eq (m : ℕ) : heightMesh m=mu m/8 := by unfold heightMesh mu; ring

lemma mu_phase (m : ℕ) (hm : 6 ≤ m) : mu m=NativeGrainQuotientFibers.physicalMesh m (phaseDepth m)/8 :=
  (phase_working_mesh m hm).symm

/-- Actual physical image of the ORIGINAL microcell center. -/
def oldPoint {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent) (k : Index) : E4 :=
  physicalMap D a (2^m) p (cellCenter (mesh D) k)
/-- Actual physical image of the raw phase vertex containing that SAME center. -/
def rawPoint {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent) (k : Index) : E4 :=
  physicalMap D a (2^m) p (rawVertex D (phaseDepth m) k)

lemma original_phase_rounding {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (k : Index) :
    dist (rawVertex D (phaseDepth m) k) (cellCenter (mesh D) k) ≤ 2*sigma m := by
  have hOld : cellCenter (mesh D) k∈wzDyadicCell (sigma m) (spatialLabel D (2^(phaseDepth m)) k) :=
    mem_wzDyadicCell_index (sigma_pos m) _
  have hRaw := cellCenter_mem (sigma_pos m) (spatialLabel D (2^(phaseDepth m)) k)
  exact (wzDyadicCell_subset_ball_of_mem (sigma_pos m) _ hOld hRaw).le

/-- Uniform physical rounding on ALL reference points; only the actual
parent's slope cube is needed. The error is128 times the fixed XY mesh. -/
theorem physical_rounding {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p) (k : Index) :
    dist (rawPoint D a m p k) (oldPoint D a m p k) ≤ 128*mu m := by
  have hb := baseMap_dist_le (2^m) (by positivity) ((shift D a:ℝ)*mesh D) p
    (parent_slope_bound h (2^m) (by positivity) p i hi) (rawVertex D (phaseDepth m) k) (cellCenter (mesh D) k)
  have hr := original_phase_rounding D m k
  have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : (0:ℝ) ≤ ((2^m:ℕ):ℝ))
  have he : (((2^m:ℕ):ℝ)*(2*sigma m))/64=128*mu m := by
    unfold sigma mu rho
    rw [squared_scale_identity m hm]
    have hN : (((2^m:ℕ):ℝ))≠0 := by positivity
    field_simp
    ring
  unfold rawPoint oldPoint NativeLocalParentPhysicalMap.physicalMap
  rw [contract_dist]
  calc
    _ ≤ (((2^m:ℕ):ℝ)*(2*sigma m))/64 := by nlinarith only [hb,hscaled]
    _ = _ := he

/-- The actual unchanged E2 reference point label. -/
def pref {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent) (k : Index) : Index :=
  columnLabel D a (2^m) p (sigma m) (rho m) k

lemma pref_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent) (k : Index) :
    pref D a m p k (3:Fin 4)=translatedHeight D a m k :=
  column_height_readback D a (2^m) p (sigma m) (rho m) k

lemma pref_spatial {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent) (k : Index) (j : Fin 3) :
    pref D a m p k j.castSucc=⌊oldPoint D a m p k j.castSucc/prefMesh m⌋ := by
  have hj : j.castSucc≠(3:Fin 4) := ne_of_lt (Fin.castSucc_lt_last j)
  simp only [pref,columnLabel,chartWidth,if_neg hj,oldPoint,prefMesh]

lemma pref_height_floor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent) (k : Index) :
    pref D a m p k (3:Fin 4)=⌊oldPoint D a m p k (3:Fin 4)/heightMesh m⌋ := by
  simp only [pref,columnLabel,chartWidth,if_true,oldPoint,heightMesh]

/-- Coarsen only the three horizontal coordinates; height is unchanged. -/
def coarseIndex (R : ℕ) (k : Index) : Index := fun j => if j=(3:Fin 4) then k j else k j/(R:ℤ)

lemma coarseIndex_height (R : ℕ) (k : Index) : coarseIndex R k (3:Fin 4)=k (3:Fin 4) := by simp [coarseIndex]

lemma coarseIndex_spatial (R : ℕ) (k : Index) (j : Fin 3) : coarseIndex R k j.castSucc=k j.castSucc/(R:ℤ) := by
  have hj : j.castSucc≠(3:Fin 4) := ne_of_lt (Fin.castSucc_lt_last j)
  simp only [coarseIndex,if_neg hj]

lemma floor_div_scale (x b : ℝ) (R : ℕ) : ⌊x/b⌋/(R:ℤ)=⌊x/((R:ℝ)*b)⌋ := by
  rw [←Int.floor_div_natCast]
  congr 1
  ring

lemma coarse_pref_spatial {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (R : ℕ) (k : Index) (j : Fin 3) :
    coarseIndex R (pref D a m p k) j.castSucc=⌊oldPoint D a m p k j.castSucc/((R:ℝ)*prefMesh m)⌋ := by
  rw [coarseIndex_spatial,pref_spatial,floor_div_scale]

end NativeReferenceXYGridPoints
