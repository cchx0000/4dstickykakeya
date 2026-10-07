import Theorems.Thm_StickyKakeya4_native_window_XY_reference_maps
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_metric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeWindowXYMetric
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridMetric
open NativeWindowXYReferenceMaps NativeHorizontalGrainSlice NativeGrainQuotientInjection
open NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric NativeOffsetAngularGeometry
open scoped BigOperators Matrix.Norms.Elementwise

lemma old_height_window {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m T : ℕ)
    (hT : 0 < T) (p : Parent) (k l : Index)
    (ht : translatedHeight D a m k/((8*T:ℕ):ℤ)=translatedHeight D a m l/((8*T:ℕ):ℤ)) :
    |oldPoint D a m p k (3:Fin 4)-oldPoint D a m p l (3:Fin 4)| ≤ (T:ℝ)*mu m := by
  have he : windowIndex (8*T) 1 (pref D a m p k) (3:Fin 4)=
      windowIndex (8*T) 1 (pref D a m p l) (3:Fin 4) := by
    simpa only [windowIndex_height,pref_height] using ht
  rw [window_pref_height,window_pref_height] at he
  exact same_floor_abs (mul_pos (by exact_mod_cast hT) (mu_pos m)) he

lemma raw_height_window {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p) (T : ℕ) (hT : 0 < T) (k l : Index)
    (ht : translatedHeight D a m k/((8*T:ℕ):ℤ)=translatedHeight D a m l/((8*T:ℕ):ℤ)) :
    |rawPoint D a m p k (3:Fin 4)-rawPoint D a m p l (3:Fin 4)| ≤ (T:ℝ)*mu m+256*mu m := by
  have hk : |rawPoint D a m p k (3:Fin 4)-oldPoint D a m p k (3:Fin 4)| ≤ 128*mu m := by
    exact (show _ ≤ dist (rawPoint D a m p k) (oldPoint D a m p k) by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (rawPoint D a m p k) (oldPoint D a m p k) (3:Fin 4)).trans
        (physical_rounding h m hm p i hi k)
  have hl : |oldPoint D a m p l (3:Fin 4)-rawPoint D a m p l (3:Fin 4)| ≤ 128*mu m := by
    rw [abs_sub_comm]
    exact (show _ ≤ dist (rawPoint D a m p l) (oldPoint D a m p l) by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (rawPoint D a m p l) (oldPoint D a m p l) (3:Fin 4)).trans
        (physical_rounding h m hm p i hi l)
  have ho := old_height_window D a m T hT p k l ht
  have h1 := abs_sub_le (rawPoint D a m p k (3:Fin 4)) (oldPoint D a m p k (3:Fin 4)) (rawPoint D a m p l (3:Fin 4))
  have h2 := abs_sub_le (oldPoint D a m p k (3:Fin 4)) (oldPoint D a m p l (3:Fin 4)) (rawPoint D a m p l (3:Fin 4))
  linarith only [hk,hl,ho,h1,h2]

/-- Reference cells may contain multiple actual heights; the height width
is bounded by the horizontal scale rather than set equal to a fine height. -/
theorem raw_dist_of_window_pref {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p) (T R : ℕ) (hT : 0 < T) (hTR : T ≤ R)
    (k l : Index) (he : windowIndex (8*T) R (pref D a m p k)=windowIndex (8*T) R (pref D a m p l)) :
    dist (rawPoint D a m p k) (rawPoint D a m p l) ≤ 281*((R:ℝ)*mu m) := by
  have hR : 0 < R := hT.trans_le hTR
  have ht : translatedHeight D a m k/((8*T:ℕ):ℤ)=translatedHeight D a m l/((8*T:ℕ):ℤ) := by
    simpa only [windowIndex_height,pref_height] using congrFun he (3:Fin 4)
  have hsp (j : Fin 3) : |oldPoint D a m p k j.castSucc-oldPoint D a m p l j.castSucc| ≤ (R:ℝ)*prefMesh m := by
    have hh := congrFun he j.castSucc
    rw [window_pref_spatial,window_pref_spatial] at hh
    exact same_floor_abs (mul_pos (by exact_mod_cast hR) (prefMesh_pos m)) hh
  have hv := old_height_window D a m T hT p k l ht
  have hTRr : (T:ℝ) ≤ R := by exact_mod_cast hTR
  have hTRmu := mul_le_mul_of_nonneg_right hTRr (mu_pos m).le
  have hn := euclidean_norm_le_sum (oldPoint D a m p k-oldPoint D a m p l)
  simp only [Fin.sum_univ_four,PiLp.sub_apply] at hn
  have h0 := hsp 0
  have h1 := hsp 1
  have h2 := hsp 2
  rw [prefMesh_eq m hm] at h0 h1 h2
  have hRr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hRmu := mul_le_mul_of_nonneg_right hRr (mu_pos m).le
  have hc := raw_dist_le_old h m hm p i hi k l
  rw [dist_eq_norm (oldPoint D a m p k)] at hc
  change |oldPoint D a m p k (0:Fin 4)-oldPoint D a m p l (0:Fin 4)| ≤ _ at h0
  change |oldPoint D a m p k (1:Fin 4)-oldPoint D a m p l (1:Fin 4)| ≤ _ at h1
  change |oldPoint D a m p k (2:Fin 4)-oldPoint D a m p l (2:Fin 4)| ≤ _ at h2
  nlinarith only [hn,h0,h1,h2,hv,hTRmu,hRmu,hc]

/-- Exact inverse diameter with the actual changing height field. -/
theorem old_dist_of_window_coordinates {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p) (T R : ℕ) (hT : 0 < T) (hTR : T ≤ R)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F G : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (hF : ‖F‖ ≤ (1/4:ℝ)) (L : ℝ) (hL : 0 ≤ L) (hvar : ‖F-G‖ ≤ L*((T:ℝ)*mu m))
    (k l : Index) (hnorm : ‖rawPoint D a m p l‖ ≤ 1)
    (ht : translatedHeight D a m k/((8*T:ℕ):ℤ)=translatedHeight D a m l/((8*T:ℕ):ℤ))
    (hX : ∀j,|tangentCoordinates P ell hd (rawPoint D a m p k) j-
      tangentCoordinates P ell hd (rawPoint D a m p l) j| ≤ (R:ℝ)*mu m)
    (hY : ∀j,|quotientMap P hP ell hell hell4 hd F (rawPoint D a m p k) j-
      quotientMap P hP ell hell hell4 hd G (rawPoint D a m p l) j| ≤ (R:ℝ)*mu m) :
    dist (oldPoint D a m p k) (oldPoint D a m p l) ≤ (519+4*L)*((R:ℝ)*mu m) := by
  have hR : 0 < R := hT.trans_le hTR
  have hx := euclidean_coord_bound
    (tangentCoordinates P ell hd (rawPoint D a m p k)-tangentCoordinates P ell hd (rawPoint D a m p l))
    ((R:ℝ)*mu m) (by simpa only [PiLp.sub_apply] using hX)
  have hy := euclidean_coord_bound
    (quotientMap P hP ell hell hell4 hd F (rawPoint D a m p k)-quotientMap P hP ell hell hell4 hd G (rawPoint D a m p l))
    ((R:ℝ)*mu m) (by simpa only [PiLp.sub_apply] using hY)
  have hTRr : (T:ℝ) ≤ R := by exact_mod_cast hTR
  have hTRmu := mul_le_mul_of_nonneg_right hTRr (mu_pos m).le
  have hRr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hRmu := mul_le_mul_of_nonneg_right hRr (mu_pos m).le
  have hv := mul_le_mul_of_nonneg_left hTRmu hL
  have hprod := mul_le_mul hvar hnorm (norm_nonneg _) (mul_nonneg hL (by have := mu_pos m; positivity))
  have hdim : 2*((ell-1:ℕ):ℝ)+((4-ell:ℕ):ℝ) ≤ 6 := by
    exact_mod_cast (show 2*(ell-1)+(4-ell) ≤ 6 by omega)
  have hdB := mul_le_mul_of_nonneg_right hdim (show 0 ≤ (R:ℝ)*mu m by have := mu_pos m; positivity)
  have hi' := varying_inverse P hP ell hell hell4 hd F G hF (rawPoint D a m p k) (rawPoint D a m p l)
  have ht' := raw_height_window h m hm p i hi T hT k l ht
  have hc := old_dist_le_raw h m hm p i hi k l
  simp only [dist_eq_norm] at hc ⊢
  nlinarith only [hx,hy,hTRmu,hRmu,hv,hprod,hdB,hi',ht',hc]

/-- The source's actual height modulus gives exactly L times the window
width on S. No claim is made about F at unused heights. -/
lemma field_window_variation {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m T : ℕ) (hT : 0 < T)
    {V : Type*} [NormedAddCommGroup V] (F : ℤ → V) (L : ℝ) (hL : 0 ≤ L) (k l : Index)
    (hLip : ‖F (translatedHeight D a m k)-F (translatedHeight D a m l)‖ ≤
      L*|referenceHeight m (translatedHeight D a m k)-referenceHeight m (translatedHeight D a m l)|)
    (ht : translatedHeight D a m k/((8*T:ℕ):ℤ)=translatedHeight D a m l/((8*T:ℕ):ℤ)) :
    ‖F (translatedHeight D a m k)-F (translatedHeight D a m l)‖ ≤ L*((T:ℝ)*mu m) :=
  hLip.trans (mul_le_mul_of_nonneg_left (reference_height_window m T hT _ _ ht) hL)

/-- A single integer radius pays all varying-field grid menus. -/
def menuRadius (L : ℝ) : ℕ := 600+4*⌈L⌉₊

lemma menuRadius_lower (L : ℝ) : 600+4*L ≤ (menuRadius L:ℝ) := by
  have hh := Nat.le_ceil L
  unfold menuRadius
  push_cast
  linarith only [hh]

lemma menu_cost_upper {L : ℝ} (hL : 0 ≤ L) :
    (((2*menuRadius L+1)^3:ℕ):ℝ) ≤ (1209:ℝ)^3*(1+L)^3 := by
  have hh := (Nat.ceil_lt_add_one hL).le
  have hb : ((2*menuRadius L+1:ℕ):ℝ) ≤ 1209*(1+L) := by
    unfold menuRadius
    push_cast
    linarith only [hh,hL]
  push_cast only [Nat.cast_pow]
  calc
    _ ≤ (1209*(1+L))^3 := by gcongr
    _ = _ := by ring

end NativeWindowXYMetric
