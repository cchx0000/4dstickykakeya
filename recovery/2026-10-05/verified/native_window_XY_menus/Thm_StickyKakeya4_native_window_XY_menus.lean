import Theorems.Thm_StickyKakeya4_native_window_XY_metric
import Theorems.Thm_StickyKakeya4_native_window_XY_labels
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_menus

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeWindowXYMenus
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridMenus
open NativeWindowXYReferenceMaps NativeWindowXYMetric NativeWindowXYLabels
open NativeHorizontalGrainSlice NativeGrainQuotientInjection NativeGrainQuotientBins
open NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric NativeOffsetAngularGeometry
open NativeAnisotropicShortRowGeometry
open scoped Matrix.Norms.Elementwise

lemma window_pxy_x {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (H R : ℕ) (k : Index) (j : Fin (ell-1)) :
    (window H R (pxy D a m ell p P hP hell hell4 hd F k)).2.1 j=
      ⌊tangentCoordinates P ell hd (rawPoint D a m p k) j/((R:ℝ)*mu m)⌋ := by
  exact floor_div_scale _ _ R

lemma window_pxy_y {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (H R : ℕ) (k : Index) (j : Fin (4-ell)) :
    (window H R (pxy D a m ell p P hP hell hell4 hd F k)).2.2 j=
      ⌊quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k) j/((R:ℝ)*mu m)⌋ := by
  exact floor_div_scale _ _ R

lemma reference_neighbor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (hm : 6 ≤ m)
    (p : Parent) (T R : ℕ) (hR : 0 < R) (k l : Index) (L : ℝ) (_hL : 0 ≤ L)
    (ht : translatedHeight D a m k/((8*T:ℕ):ℤ)=translatedHeight D a m l/((8*T:ℕ):ℤ))
    (hdist : dist (oldPoint D a m p k) (oldPoint D a m p l) ≤ (519+4*L)*((R:ℝ)*mu m)) :
    windowIndex (8*T) R (pref D a m p k)∈
      columnHalo (menuRadius L) 0 (windowIndex (8*T) R (pref D a m p l)) := by
  apply Fintype.mem_piFinset.mpr
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change windowIndex (8*T) R (pref D a m p k) (3:Fin 4)∈
      Icc (windowIndex (8*T) R (pref D a m p l) (3:Fin 4)-0)
        (windowIndex (8*T) R (pref D a m p l) (3:Fin 4)+0)
    simp only [windowIndex_height,pref_height,ht,sub_zero,add_zero,mem_Icc,le_refl,and_self]
  · have hj : j.castSucc≠(3:Fin 4) := ne_of_lt (Fin.castSucc_lt_last j)
    change windowIndex (8*T) R (pref D a m p k) j.castSucc∈
      Icc (windowIndex (8*T) R (pref D a m p l) j.castSucc-(if j.castSucc=(3:Fin 4) then (0:ℕ) else menuRadius L:ℕ))
        (windowIndex (8*T) R (pref D a m p l) j.castSucc+(if j.castSucc=(3:Fin 4) then (0:ℕ) else menuRadius L:ℕ))
    rw [if_neg hj]
    simp only [window_pref_spatial]
    apply floor_neighbor (mul_pos (by exact_mod_cast hR) (prefMesh_pos m)) (menuRadius L)
    have hc : |oldPoint D a m p k j.castSucc-oldPoint D a m p l j.castSucc| ≤
        dist (oldPoint D a m p k) (oldPoint D a m p l) := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (oldPoint D a m p k) (oldPoint D a m p l) j.castSucc
    have hK := menuRadius_lower L
    have hcoeff : 519+4*L ≤ 8*(menuRadius L:ℝ) := by linarith only [hK,_hL]
    have hmul := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ (R:ℝ)*mu m by have := mu_pos m; positivity)
    rw [prefMesh_eq m hm]
    nlinarith only [hc,hdist,hmul]

/-- Inverse occupied-cell menu on points where the actual height field
has its proved modulus. The unit raw support is discharged by the source caller. -/
theorem inverse_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p) (T R : ℕ) (hT : 0 < T) (hTR : T ≤ R)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (k l : Index) (hF : ‖F (translatedHeight D a m k)‖ ≤ (1/4:ℝ))
    (L : ℝ) (hL : 0 ≤ L) (hnorm : ‖rawPoint D a m p l‖ ≤ 1)
    (hLip : ‖F (translatedHeight D a m k)-F (translatedHeight D a m l)‖ ≤
      L*|referenceHeight m (translatedHeight D a m k)-referenceHeight m (translatedHeight D a m l)|)
    (he : window (8*T) R (pxy D a m ell p P hP hell hell4 hd F k)=
      window (8*T) R (pxy D a m ell p P hP hell hell4 hd F l)) :
    windowIndex (8*T) R (pref D a m p k)∈
      columnHalo (menuRadius L) 0 (windowIndex (8*T) R (pref D a m p l)) := by
  have ht : translatedHeight D a m k/((8*T:ℕ):ℤ)=translatedHeight D a m l/((8*T:ℕ):ℤ) := congrArg Prod.fst he
  have hvar := field_window_variation D a m T hT F L hL k l hLip ht
  have hR : 0 < R := hT.trans_le hTR
  have hwidth : 0 < (R:ℝ)*mu m := mul_pos (by exact_mod_cast hR) (mu_pos m)
  have hX (j : Fin (ell-1)) := congrArg (fun z : NativeReferenceXYGridMaps.XY ell => z.2.1 j) he
  have hY (j : Fin (4-ell)) := congrArg (fun z : NativeReferenceXYGridMaps.XY ell => z.2.2 j) he
  simp only [window_pxy_x] at hX
  simp only [window_pxy_y] at hY
  exact reference_neighbor D a m hm p T R hR k l L hL ht
    (old_dist_of_window_coordinates h m ell hm p i hi T R hT hTR P hP hell hell4 hd
      (F (translatedHeight D a m k)) (F (translatedHeight D a m l)) hF L hL hvar k l hnorm ht
      (fun j => same_floor_abs hwidth (hX j)) (fun j => same_floor_abs hwidth (hY j)))

/-- Forward occupied-cell menu for the same changing field and same fixed
height-window partition. -/
theorem forward_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p) (T R : ℕ) (hT : 0 < T) (hTR : T ≤ R)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (k l : Index) (hF : ‖F (translatedHeight D a m k)‖ ≤ (1/4:ℝ))
    (L : ℝ) (hL : 0 ≤ L) (hnorm : ‖rawPoint D a m p l‖ ≤ 1)
    (hLip : ‖F (translatedHeight D a m k)-F (translatedHeight D a m l)‖ ≤
      L*|referenceHeight m (translatedHeight D a m k)-referenceHeight m (translatedHeight D a m l)|)
    (he : windowIndex (8*T) R (pref D a m p k)=windowIndex (8*T) R (pref D a m p l)) :
    window (8*T) R (pxy D a m ell p P hP hell hell4 hd F k)∈
      xyBox ell (window (8*T) R (pxy D a m ell p P hP hell hell4 hd F l)) (menuRadius L) := by
  have hR : 0 < R := hT.trans_le hTR
  have ht : translatedHeight D a m k/((8*T:ℕ):ℤ)=translatedHeight D a m l/((8*T:ℕ):ℤ) := by
    simpa only [windowIndex_height,pref_height] using congrFun he (3:Fin 4)
  have hvar := field_window_variation D a m T hT F L hL k l hLip ht
  have hraw := raw_dist_of_window_pref h m hm p i hi T R hT hTR k l he
  rw [dist_eq_norm] at hraw
  have hTRr : (T:ℝ) ≤ R := by exact_mod_cast hTR
  have hTW := mul_le_mul_of_nonneg_right hTRr (mu_pos m).le
  have hVW := mul_le_mul_of_nonneg_left hTW hL
  have hprod := mul_le_mul hvar hnorm (norm_nonneg _) (mul_nonneg hL (by have := mu_pos m; positivity))
  have hQ := quotient_difference P hP ell hell hell4 hd
    (F (translatedHeight D a m k)) (F (translatedHeight D a m l)) hF
    (rawPoint D a m p k) (rawPoint D a m p l)
  have hK := menuRadius_lower L
  have hKW := mul_le_mul_of_nonneg_right hK (show 0 ≤ (R:ℝ)*mu m by have := mu_pos m; positivity)
  have hLW := mul_nonneg hL (show 0 ≤ (R:ℝ)*mu m by have := mu_pos m; positivity)
  have hW := mul_pos (by exact_mod_cast hR : (0:ℝ)<R) (mu_pos m)
  apply mem_product.mpr
  refine ⟨mem_singleton.mpr ht,mem_product.mpr ⟨?_,?_⟩⟩
  · apply Fintype.mem_piFinset.mpr
    intro j
    simp only [window_pxy_x]
    apply floor_neighbor hW (menuRadius L)
    have hb := tangent_norm_le P ell hd (rawPoint D a m p k-rawPoint D a m p l)
    have hc := PiLp.norm_apply_le (tangentCoordinates P ell hd (rawPoint D a m p k-rawPoint D a m p l)) j
    simp only [map_sub,PiLp.sub_apply,Real.norm_eq_abs] at hc hb
    nlinarith only [hc,hb,hraw,hKW,hLW,hW]
  · apply Fintype.mem_piFinset.mpr
    intro j
    simp only [window_pxy_y]
    apply floor_neighbor hW (menuRadius L)
    have hc := PiLp.norm_apply_le
      (quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k)-
        quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m l)) (rawPoint D a m p l)) j
    simp only [PiLp.sub_apply,Real.norm_eq_abs] at hc
    nlinarith only [hc,hQ,hraw,hprod,hVW,hKW,hW]

end NativeWindowXYMenus
