import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_metric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeReferenceXYGridMenus
open Classical Finset StickyKakeya4 NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeReferenceXYGridMetric NativeHorizontalGrainSlice NativeGrainQuotientInjection
open NativeCommonCubicalMesh NativeOriginalParentSelection NativeTranslatedGrainHeightOverlap
open NativeAnisotropicShortRowGeometry
open scoped BigOperators Matrix.Norms.Elementwise

def vectorBox {d : ℕ} (z : Fin d → ℤ) (K : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun j => Icc (z j-(K:ℤ)) (z j+K))

lemma vectorBox_card {d : ℕ} (z : Fin d → ℤ) (K : ℕ) : (vectorBox z K).card=(2*K+1)^d := by
  have hi (j : Fin d) : (Icc (z j-(K:ℤ)) (z j+K)).card=2*K+1 := by
    have hh : ((Icc (z j-(K:ℤ)) (z j+K)).card:ℤ)=2*(K:ℤ)+1 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp only [vectorBox,Fintype.card_piFinset,hi,prod_const,card_univ,Fintype.card_fin]

/-- The height is fixed; there are exactly three spatial coordinates. -/
def xyBox (ell : ℕ) (z : XY ell) (K : ℕ) : Finset (XY ell) :=
  {z.1} ×ˢ (vectorBox z.2.1 K ×ˢ vectorBox z.2.2 K)

lemma xyBox_card (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (z : XY ell) (K : ℕ) :
    (xyBox ell z K).card=(2*K+1)^3 := by
  simp only [xyBox,card_product,card_singleton,one_mul,vectorBox_card]
  rw [←pow_add]
  congr 1
  omega

lemma coarseIndex_one (k : Index) : coarseIndex 1 k=k := by
  ext j
  simp only [coarseIndex,Int.natCast_one,Int.ediv_one,ite_self]

lemma coarseXY_one (ell : ℕ) (z : XY ell) : coarseXY ell 1 z=z := by
  rcases z with ⟨t,x,y⟩
  simp only [coarseXY,Int.natCast_one,Int.ediv_one]

/-- A genuine physical inverse bound gives a fixed menu of reference
coarse cells at the SAME scale factor and SAME translated height. -/
lemma pref_neighbor_of_old_dist {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (hm : 6 ≤ m)
    (p : Parent) (R : ℕ) (hR : 0 < R) (k l : Index)
    (ht : translatedHeight D a m k=translatedHeight D a m l)
    (hd : dist (oldPoint D a m p k) (oldPoint D a m p l) ≤ 800*((R:ℝ)*mu m)) :
    coarseIndex R (pref D a m p k)∈columnHalo 100 0 (coarseIndex R (pref D a m p l)) := by
  apply Fintype.mem_piFinset.mpr
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change coarseIndex R (pref D a m p k) (3:Fin 4)∈
      Icc (coarseIndex R (pref D a m p l) (3:Fin 4)-0) (coarseIndex R (pref D a m p l) (3:Fin 4)+0)
    simp only [coarseIndex_height,pref_height,ht,sub_zero,add_zero,mem_Icc,le_refl,and_self]
  · have hj : j.castSucc≠(3:Fin 4) := ne_of_lt (Fin.castSucc_lt_last j)
    change coarseIndex R (pref D a m p k) j.castSucc∈
      Icc (coarseIndex R (pref D a m p l) j.castSucc-(if j.castSucc=(3:Fin 4) then (0:ℕ) else 100:ℕ))
        (coarseIndex R (pref D a m p l) j.castSucc+(if j.castSucc=(3:Fin 4) then (0:ℕ) else 100:ℕ))
    rw [if_neg hj]
    simp only [coarse_pref_spatial]
    apply floor_neighbor (mul_pos (by exact_mod_cast hR) (prefMesh_pos m)) 100
    have hh : |oldPoint D a m p k j.castSucc-oldPoint D a m p l j.castSucc| ≤
        dist (oldPoint D a m p k) (oldPoint D a m p l) := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (oldPoint D a m p k) (oldPoint D a m p l) j.castSucc
    rw [prefMesh_eq m hm]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hh,hd]

/-- Inverse menu for a coarse XY fiber, valid on the entire reference set. -/
theorem inverse_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (R : ℕ) (hR : 0 < R) (k l : Index)
    (he : coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)=
      coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F l)) :
    coarseIndex R (pref D a m p k)∈columnHalo 100 0 (coarseIndex R (pref D a m p l)) := by
  have ht : translatedHeight D a m k=translatedHeight D a m l := congrArg Prod.fst he
  apply pref_neighbor_of_old_dist D a m hm p R hR k l ht
  have hh := old_dist_of_coarse_XY h m ell hm p i hi P hP hell hell4 hd F hF R hR k l he
  have hr : (0:ℝ) ≤ (R:ℝ)*mu m := mul_nonneg (Nat.cast_nonneg _) (mu_pos m).le
  nlinarith only [hh,hr]

/-- Forward menu for each actual coarse reference cell. One common F at
its fixed reference height makes all coordinate comparisons linear. -/
theorem forward_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (R : ℕ) (hR : 0 < R) (k l : Index)
    (he : coarseIndex R (pref D a m p k)=coarseIndex R (pref D a m p l)) :
    coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)∈
      xyBox ell (coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F l)) 600 := by
  have ht : translatedHeight D a m k=translatedHeight D a m l := by
    have hh := congrFun he (3:Fin 4)
    simpa only [coarseIndex_height,pref_height] using hh
  have hraw := raw_dist_of_coarse_pref h m hm p i hi R hR k l he
  rw [dist_eq_norm] at hraw
  have hr : (0:ℝ) ≤ (R:ℝ)*mu m := mul_nonneg (Nat.cast_nonneg _) (mu_pos m).le
  have hX (j : Fin (ell-1)) : |tangentCoordinates P ell hd (rawPoint D a m p k) j-
      tangentCoordinates P ell hd (rawPoint D a m p l) j| ≤ 600*((R:ℝ)*mu m) := by
    have hh := tangent_norm_le P ell hd (rawPoint D a m p k-rawPoint D a m p l)
    rw [map_sub] at hh
    have hc := PiLp.norm_apply_le (tangentCoordinates P ell hd (rawPoint D a m p k-rawPoint D a m p l)) j
    simp only [map_sub,PiLp.sub_apply,Real.norm_eq_abs] at hc
    nlinarith only [hc,hh,hraw,hr]
  have hY (j : Fin (4-ell)) :
      |quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k) j-
        quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m l)) (rawPoint D a m p l) j| ≤
          600*((R:ℝ)*mu m) := by
    rw [←ht]
    have hh := quotient_norm_le P hP ell hell hell4 hd (F (translatedHeight D a m k)) (hF _)
      (rawPoint D a m p k-rawPoint D a m p l)
    rw [map_sub] at hh
    have hc := PiLp.norm_apply_le
      (quotientMap P hP ell hell hell4 hd (F (translatedHeight D a m k)) (rawPoint D a m p k-rawPoint D a m p l)) j
    simp only [map_sub,PiLp.sub_apply,Real.norm_eq_abs] at hc
    nlinarith only [hc,hh,hraw,hr]
  apply mem_product.mpr
  refine ⟨mem_singleton.mpr ht,mem_product.mpr ⟨?_,?_⟩⟩
  · apply Fintype.mem_piFinset.mpr
    intro j
    simp only [coarseXY_x]
    exact floor_neighbor (mul_pos (by exact_mod_cast hR) (mu_pos m)) 600 (hX j)
  · apply Fintype.mem_piFinset.mpr
    intro j
    simp only [coarseXY_y]
    exact floor_neighbor (mul_pos (by exact_mod_cast hR) (mu_pos m)) 600 (hY j)

end NativeReferenceXYGridMenus
