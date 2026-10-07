import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_maps

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeReferenceXYGridMetric
open Classical Finset StickyKakeya4 NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeHorizontalGrainSlice NativeGrainQuotientInjection NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeTranslatedGrainHeightOverlap
open scoped BigOperators Matrix.Norms.Elementwise

lemma old_height_gap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (k l : Index) (ht : translatedHeight D a m k=translatedHeight D a m l) :
    |oldPoint D a m p k (3:Fin 4)-oldPoint D a m p l (3:Fin 4)| ≤ mu m/8 := by
  have he : pref D a m p k (3:Fin 4)=pref D a m p l (3:Fin 4) := by rw [pref_height,pref_height,ht]
  rw [pref_height_floor,pref_height_floor] at he
  exact (same_floor_abs (heightMesh_pos m) he).trans_eq (heightMesh_eq m)

lemma old_dist_le_raw {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p) (k l : Index) :
    dist (oldPoint D a m p k) (oldPoint D a m p l) ≤
      dist (rawPoint D a m p k) (rawPoint D a m p l)+256*mu m := by
  have hk := physical_rounding h m hm p i hi k
  have hl := physical_rounding h m hm p i hi l
  have h1 := dist_triangle (oldPoint D a m p k) (rawPoint D a m p k) (oldPoint D a m p l)
  have h2 := dist_triangle (rawPoint D a m p k) (rawPoint D a m p l) (oldPoint D a m p l)
  rw [dist_comm (oldPoint D a m p k) (rawPoint D a m p k)] at h1
  linarith

lemma raw_dist_le_old {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p) (k l : Index) :
    dist (rawPoint D a m p k) (rawPoint D a m p l) ≤
      dist (oldPoint D a m p k) (oldPoint D a m p l)+256*mu m := by
  have hk := physical_rounding h m hm p i hi k
  have hl := physical_rounding h m hm p i hi l
  have h1 := dist_triangle (rawPoint D a m p k) (oldPoint D a m p k) (rawPoint D a m p l)
  have h2 := dist_triangle (oldPoint D a m p k) (oldPoint D a m p l) (rawPoint D a m p l)
  rw [dist_comm (oldPoint D a m p l) (rawPoint D a m p l)] at h2
  linarith

lemma raw_height_gap {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p) (k l : Index)
    (ht : translatedHeight D a m k=translatedHeight D a m l) :
    |rawPoint D a m p k (3:Fin 4)-rawPoint D a m p l (3:Fin 4)| ≤ mu m/8+256*mu m := by
  have hk : |rawPoint D a m p k (3:Fin 4)-oldPoint D a m p k (3:Fin 4)| ≤ 128*mu m := by
    exact (show _ ≤ dist (rawPoint D a m p k) (oldPoint D a m p k) by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (rawPoint D a m p k) (oldPoint D a m p k) (3:Fin 4)).trans
        (physical_rounding h m hm p i hi k)
  have hl : |oldPoint D a m p l (3:Fin 4)-rawPoint D a m p l (3:Fin 4)| ≤ 128*mu m := by
    rw [abs_sub_comm]
    exact (show _ ≤ dist (rawPoint D a m p l) (oldPoint D a m p l) by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (rawPoint D a m p l) (oldPoint D a m p l) (3:Fin 4)).trans
        (physical_rounding h m hm p i hi l)
  have ho := old_height_gap D a m p k l ht
  have h1 := abs_sub_le (rawPoint D a m p k (3:Fin 4)) (oldPoint D a m p k (3:Fin 4)) (rawPoint D a m p l (3:Fin 4))
  have h2 := abs_sub_le (oldPoint D a m p k (3:Fin 4)) (oldPoint D a m p l (3:Fin 4)) (rawPoint D a m p l (3:Fin 4))
  linarith

/-- General inverse comparison on one actual translated-height slice. -/
theorem old_dist_of_coordinate_bounds {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (k l : Index) (ht : translatedHeight D a m k=translatedHeight D a m l)
    (B : ℝ) (hB : 0 ≤ B)
    (hX : ∀j,|tangentCoordinates P ell hd (rawPoint D a m p k) j-
      tangentCoordinates P ell hd (rawPoint D a m p l) j| ≤ B)
    (hY : ∀j,|quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k) j-
      quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m l)) (rawPoint D a m p l) j| ≤ B) :
    dist (oldPoint D a m p k) (oldPoint D a m p l) ≤ 6*B+513*mu m := by
  have hx : ‖tangentCoordinates P ell hd (rawPoint D a m p k-rawPoint D a m p l)‖ ≤ ((ell-1:ℕ):ℝ)*B := by
    apply euclidean_coord_bound
    simpa only [map_sub,PiLp.sub_apply] using hX
  have hy : ‖quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k))
      (rawPoint D a m p k-rawPoint D a m p l)‖ ≤ ((4-ell:ℕ):ℝ)*B := by
    apply euclidean_coord_bound
    simpa only [map_sub,PiLp.sub_apply,←ht] using hY
  have hinv := inverse_norm P hP ell hell hell4 hd (F (translatedHeight D a m k)) (hF _)
    (rawPoint D a m p k-rawPoint D a m p l)
  have hh := raw_height_gap h m hm p i hi k l ht
  have hp := old_dist_le_raw h m hm p i hi k l
  have hdim : 2*((ell-1:ℕ):ℝ)+((4-ell:ℕ):ℝ) ≤ 6 := by
    exact_mod_cast (show 2*(ell-1)+(4-ell) ≤ 6 by omega)
  have hdimB := mul_le_mul_of_nonneg_right hdim hB
  simp only [dist_eq_norm,PiLp.sub_apply] at hp hinv
  have hmu := mu_pos m
  rw [dist_eq_norm]
  nlinarith only [hx,hy,hinv,hh,hp,hdimB,hmu]

/-- One coarse reference cell gives a bounded raw physical diameter. -/
theorem raw_dist_of_coarse_pref {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p) (R : ℕ) (hR : 0 < R) (k l : Index)
    (he : coarseIndex R (pref D a m p k)=coarseIndex R (pref D a m p l)) :
    dist (rawPoint D a m p k) (rawPoint D a m p l) ≤ 281*((R:ℝ)*mu m) := by
  have ht : translatedHeight D a m k=translatedHeight D a m l := by
    have hh := congrFun he (3:Fin 4)
    simpa only [coarseIndex_height,pref_height] using hh
  have hsp (j : Fin 3) : |oldPoint D a m p k j.castSucc-oldPoint D a m p l j.castSucc| ≤ (R:ℝ)*prefMesh m := by
    have hh := congrFun he j.castSucc
    rw [coarse_pref_spatial,coarse_pref_spatial] at hh
    exact same_floor_abs (mul_pos (by exact_mod_cast hR) (prefMesh_pos m)) hh
  have hv := old_height_gap D a m p k l ht
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
  have hmu := mu_pos m
  nlinarith only [hn,h0,h1,h2,hv,hRmu,hc,hmu]

/-- Same coarse XY label has a uniformly bounded inverse reference diameter. -/
theorem old_dist_of_coarse_XY {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (R : ℕ) (hR : 0 < R) (k l : Index)
    (he : coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)=
      coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F l)) :
    dist (oldPoint D a m p k) (oldPoint D a m p l) ≤ 519*((R:ℝ)*mu m) := by
  have ht : translatedHeight D a m k=translatedHeight D a m l := congrArg Prod.fst he
  have hX (j : Fin (ell-1)) := congrArg (fun z : XY ell => z.2.1 j) he
  have hY (j : Fin (4-ell)) := congrArg (fun z : XY ell => z.2.2 j) he
  simp only [coarseXY_x] at hX
  simp only [coarseXY_y] at hY
  have hwidth : 0 < (R:ℝ)*mu m := mul_pos (by exact_mod_cast hR) (mu_pos m)
  have hb := old_dist_of_coordinate_bounds h m ell hm p i hi P hP hell hell4 hd F hF k l ht
    ((R:ℝ)*mu m) hwidth.le
    (fun j => same_floor_abs hwidth (hX j)) (fun j => same_floor_abs hwidth (hY j))
  have hRr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hh := mul_le_mul_of_nonneg_right hRr (mu_pos m).le
  nlinarith only [hb,hh]

end NativeReferenceXYGridMetric
