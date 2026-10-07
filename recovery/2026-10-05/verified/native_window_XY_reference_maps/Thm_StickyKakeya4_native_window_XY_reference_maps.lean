import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_support
import Theorems.Thm_StickyKakeya4_native_offset_angular_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeWindowXYReferenceMaps
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeTranslatedGrainHeightMetric NativeTranslatedGrainHeightOverlap NativeSquaredGrainQueries
open NativeAnisotropicShortRowGeometry NativeHorizontalGrainSlice NativeGrainQuotientInjection
open NativeOffsetAngularGeometry
open scoped Matrix.Norms.Elementwise

/-- Coarsen the actual reference height and horizontal coordinates separately. -/
def windowIndex (H R : ℕ) (k : Index) : Index :=
  fun j => if j=(3:Fin 4) then k j/(H:ℤ) else k j/(R:ℤ)

lemma windowIndex_height (H R : ℕ) (k : Index) :
    windowIndex H R k (3:Fin 4)=k (3:Fin 4)/(H:ℤ) := by simp only [windowIndex,if_true]

lemma windowIndex_spatial (H R : ℕ) (k : Index) (j : Fin 3) :
    windowIndex H R k j.castSucc=k j.castSucc/(R:ℤ) := by
  have hj : j.castSucc≠(3:Fin 4) := ne_of_lt (Fin.castSucc_lt_last j)
  simp only [windowIndex,if_neg hj]

lemma window_pref_spatial {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m H R : ℕ)
    (p : Parent) (k : Index) (j : Fin 3) :
    windowIndex H R (pref D a m p k) j.castSucc=
      ⌊oldPoint D a m p k j.castSucc/((R:ℝ)*prefMesh m)⌋ := by
  rw [windowIndex_spatial,pref_spatial,floor_div_scale]

lemma window_pref_height {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m T R : ℕ)
    (p : Parent) (k : Index) :
    windowIndex (8*T) R (pref D a m p k) (3:Fin 4)=
      ⌊oldPoint D a m p k (3:Fin 4)/((T:ℝ)*mu m)⌋ := by
  rw [windowIndex_height,pref_height_floor,floor_div_scale,heightMesh_eq]
  congr 2
  push_cast
  ring

/-- This reference map is literally the original physical column label,
with both its original-space widths retained. -/
lemma window_pref_column {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m H R : ℕ)
    (p : Parent) (k : Index) :
    windowIndex H R (pref D a m p k)=
      columnLabel D a (2^m) p ((R:ℝ)*sigma m) ((H:ℝ)*rho m) k := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [show (Fin.last 3:Fin 4)=3 by rfl,windowIndex_height,pref_height_floor,floor_div_scale]
    simp only [columnLabel,chartWidth,if_true,oldPoint,heightMesh]
    congr 2
    ring
  · rw [window_pref_spatial]
    have hj : j.castSucc≠(3:Fin 4) := ne_of_lt (Fin.castSucc_lt_last j)
    simp only [columnLabel,chartWidth,if_neg hj,oldPoint,prefMesh]
    congr 2
    ring

lemma dyadic_scale_mul (b g : ℕ) (hgb : g ≤ b) :
    ((2^(b-g):ℕ):ℝ)*(64/((2^b:ℕ):ℝ))=64/((2^g:ℕ):ℝ) := by
  have hp : (2^b:ℕ)=2^(b-g)*2^g := by rw [←pow_add,Nat.sub_add_cancel hgb]
  rw [hp]
  push_cast
  have hn : (2:ℝ)^(b-g)≠0 := by positivity
  field_simp

lemma dyadic_height_width (m f : ℕ) (hm : 6 ≤ m) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m) :
    ((8*2^(phaseDepth m-f):ℕ):ℝ)*rho m=64/((2^(f-m+3):ℕ):ℝ) := by
  have he : 3+(phaseDepth m-f)+(f-m+3)=m := by dsimp [phaseDepth] at hfb ⊢; omega
  have hp : (8:ℝ)*((2^(phaseDepth m-f):ℕ):ℝ)*((2^(f-m+3):ℕ):ℝ)=((2^m:ℕ):ℝ) := by
    rw [show (8:ℝ)=((2^3:ℕ):ℝ) by norm_num,←Nat.cast_mul,←Nat.cast_mul,←pow_add,←pow_add,he]
  unfold rho
  push_cast only [Nat.cast_mul,Nat.cast_ofNat]
  rw [←mul_div_assoc]
  apply (div_eq_div_iff (by positivity : ((2^m:ℕ):ℝ)≠0) (by positivity : ((2^(f-m+3):ℕ):ℝ)≠0)).mpr
  nlinarith only [hp]

lemma scheduled_reference_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m f g : ℕ) (hm : 6 ≤ m) (hmf : m ≤ f) (hgf : g ≤ f) (hfb : f ≤ phaseDepth m)
    (p : Parent) (k : Index) :
    windowIndex (8*2^(phaseDepth m-f)) (2^(phaseDepth m-g)) (pref D a m p k)=
      columnLabel D a (2^m) p (64/((2^g:ℕ):ℝ)) (64/((2^(f-m+3):ℕ):ℝ)) k := by
  rw [window_pref_column,dyadic_height_width m f hm hmf hfb]
  congr 1
  exact dyadic_scale_mul (phaseDepth m) g (hgf.trans hfb)

lemma same_integer_window (H : ℕ) (hH : 0 < H) (t u : ℤ) (he : t/(H:ℤ)=u/(H:ℤ)) :
    |(t:ℝ)-u| ≤ (H:ℝ) := by
  apply same_floor_abs (by exact_mod_cast hH)
  rw [Int.floor_div_natCast,Int.floor_div_natCast,Int.floor_intCast,Int.floor_intCast]
  exact he

/-- Exact center-height diameter in one coarsened height bin. This only
compares used heights and never assumes regularity of an unused-height extension. -/
lemma reference_height_window (m T : ℕ) (hT : 0 < T) (t u : ℤ)
    (he : t/((8*T:ℕ):ℤ)=u/((8*T:ℕ):ℤ)) :
    |referenceHeight m t-referenceHeight m u| ≤ (T:ℝ)*mu m := by
  have hh := same_integer_window (8*T) (by omega) t u he
  rw [referenceHeight_distance]
  have hwidth : (64/((2^m:ℕ):ℝ))/512=mu m/8 := by unfold mu rho; ring
  rw [hwidth]
  calc
    _ ≤ (mu m/8)*((8*T:ℕ):ℝ) := mul_le_mul_of_nonneg_left hh (by have := mu_pos m; positivity)
    _ = _ := by push_cast; ring

/-- Inverse comparison for two different actual height matrices. -/
theorem varying_inverse (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M N : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ)) (x y : E4) :
    ‖x-y‖ ≤ 2*‖tangentCoordinates P ell hd x-tangentCoordinates P ell hd y‖+
      ‖quotientMap P hP ell hell hell4 hd M x-quotientMap P hP ell hell hell4 hd N y‖+
      4*‖M-N‖*‖y‖+|x (3:Fin 4)-y (3:Fin 4)| := by
  have he : quotientMap P hP ell hell hell4 hd M (x-y)=
      (quotientMap P hP ell hell hell4 hd M x-quotientMap P hP ell hell hell4 hd N y)+
        (M-N).toEuclideanLin (tangentCoordinates P ell hd y) := by
    simp only [quotientMap,LinearMap.sub_apply,LinearMap.comp_apply,map_sub]
    abel
  have hact := (matrix_action_general ell hell hell4 (M-N) (tangentCoordinates P ell hd y)).trans
    (mul_le_mul_of_nonneg_left (tangent_norm_le P ell hd y) (by positivity : (0:ℝ)≤4*‖M-N‖))
  have hq := norm_add_le (quotientMap P hP ell hell hell4 hd M x-quotientMap P hP ell hell hell4 hd N y)
    ((M-N).toEuclideanLin (tangentCoordinates P ell hd y))
  rw [←he] at hq
  have hh := inverse_norm P hP ell hell hell4 hd M hM (x-y)
  rw [map_sub] at hh
  simp only [PiLp.sub_apply] at hh
  linarith only [hh,hq,hact]

end NativeWindowXYReferenceMaps
