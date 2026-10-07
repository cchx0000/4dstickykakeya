import Theorems.Thm_StickyKakeya4_native_slice_class_balls
import Theorems.Thm_StickyKakeya4_native_fixed_size_scale_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeSliceRadiusInterpolation
open Classical Finset
open scoped BigOperators

def radius (fine depth : ℕ) : ℝ := ((2^(fine-depth):ℕ):ℝ)
lemma radius_pos (fine depth : ℕ) : 0 < radius fine depth := by unfold radius;positivity

lemma adjacent_ratio (fine a b : ℕ) (hab : a ≤ b) (hbf : b ≤ fine) :
    radius fine a=((2^(b-a):ℕ):ℝ)*radius fine b := by
  have he : fine-a=(b-a)+(fine-b) := by omega
  unfold radius
  rw [he,pow_add,Nat.cast_mul]

/-- Real radii, including exact menu endpoints, are bracketed by two actual
installed depths. Only the fixed maximum adjacent depth gap is lost. -/
theorem bracket_real_radius (J fine coarse G : ℕ) (_hJ : 0 < J)
    (depth : Fin (J+1) → ℕ) (hfirst : depth 0=coarse)
    (hlast : depth (Fin.last J)=fine) (hdepth : ∀j,depth j ≤ fine)
    (hmono : Monotone depth) (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc ≤ G)
    (t : ℝ) (ht : 1 ≤ t) (htop : t ≤ radius fine coarse) :
    ∃lo hi : Fin (J+1),radius fine (depth lo) ≤ t ∧ t ≤ radius fine (depth hi) ∧
      t ≤ ((2^G:ℕ):ℝ)*radius fine (depth lo) ∧
      radius fine (depth hi) ≤ ((2^G:ℕ):ℝ)*t := by
  have hB : (1:ℝ) ≤ ((2^G:ℕ):ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (show 0 < (2:ℕ)^G by positivity)
  by_cases he : t=radius fine coarse
  · refine ⟨0,0,?_,?_,?_,?_⟩
    · simpa only [hfirst,he] using (le_rfl : radius fine coarse ≤ radius fine coarse)
    · simpa only [hfirst,he] using (le_rfl : radius fine coarse ≤ radius fine coarse)
    · rw [hfirst,←he]
      nlinarith only [hB,ht]
    · rw [hfirst,←he]
      nlinarith only [hB,ht]
  · have hstrict : t < radius fine coarse := lt_of_le_of_ne htop he
    let A := univ.filter (fun j : Fin (J+1) => t < radius fine (depth j))
    have hA : A.Nonempty := ⟨0,mem_filter.mpr ⟨mem_univ _,by simpa only [hfirst] using hstrict⟩⟩
    obtain ⟨j,hj,hmax⟩ := exists_max_image A (fun j => j.val) hA
    have hjlt := (mem_filter.mp hj).2
    have hjJ : j.val < J := by
      by_contra hn
      have heq : j=Fin.last J := by
        apply Fin.ext
        change j.val=J
        have hjbound := j.isLt
        omega
      rw [heq,hlast] at hjlt
      norm_num [radius] at hjlt
      linarith
    let i : Fin J := ⟨j.val,hjJ⟩
    have hij : i.castSucc=j := Fin.ext rfl
    have hlo : radius fine (depth i.succ) ≤ t := by
      by_contra hn
      have hiA : i.succ∈A := mem_filter.mpr ⟨mem_univ _,lt_of_not_ge hn⟩
      have hmax' := hmax i.succ hiA
      dsimp [i] at hmax'
      omega
    have hratio : radius fine (depth i.castSucc) ≤ ((2^G:ℕ):ℝ)*radius fine (depth i.succ) := by
      rw [adjacent_ratio fine _ _ (hmono (Fin.castSucc_le_succ i)) (hdepth i.succ)]
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) (hgap i))) (radius_pos _ _).le
    refine ⟨i.succ,i.castSucc,hlo,by simpa only [hij] using hjlt.le,?_,?_⟩
    · exact (show t ≤ radius fine (depth i.castSucc) by simpa only [hij] using hjlt.le).trans hratio
    · exact hratio.trans (mul_le_mul_of_nonneg_left hlo (by positivity))

/-- Sup-metric closed-ball population on a finite actual spatial set. -/
def ballCount {X : Type*} [PseudoMetricSpace X] (P : Finset X) (x : X) (r : ℝ) : ℝ :=
  ((P.filter (fun y => dist y x ≤ r)).card:ℝ)

lemma ballCount_mono {X : Type*} [PseudoMetricSpace X] (P : Finset X) (x : X)
    {r s : ℝ} (hrs : r ≤ s) : ballCount P x r ≤ ballCount P x s := by
  unfold ballCount
  exact_mod_cast card_le_card (show P.filter (fun y => dist y x ≤ r)⊆P.filter (fun y => dist y x ≤ s) from
    fun y hy => mem_filter.mpr ⟨(mem_filter.mp hy).1,(mem_filter.mp hy).2.trans hrs⟩)

/-- The fixed parent chart has outer horizontal cell width1/8. Prepared
bounds extend to every radius in[mu,1], with explicit finite-menu cost. -/
theorem all_radius_bounds {X : Type*} [PseudoMetricSpace X]
    (P : Finset X) (x : X) (J fine coarse G : ℕ) (hJ : 0 < J)
    (depth : Fin (J+1) → ℕ) (hfirst : depth 0=coarse)
    (hlast : depth (Fin.last J)=fine) (hdepth : ∀j,depth j ≤ fine)
    (hmono : Monotone depth) (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc ≤ G)
    (mu L U s : ℝ) (hmu : 0 < mu) (hL : 0 ≤ L) (hU : 0 ≤ U) (hs : 0 ≤ s)
    (houter : mu*radius fine coarse=1/8)
    (Hlo : ∀j,L*(radius fine (depth j))^s ≤ ballCount P x (mu*radius fine (depth j)))
    (Hhi : ∀j,ballCount P x (mu*radius fine (depth j)) ≤ U*(radius fine (depth j))^s)
    (Hglobal : (P.card:ℝ) ≤ 27*U*(radius fine coarse)^s)
    (r : ℝ) (hr : mu ≤ r) (hr1 : r ≤ 1) :
    let B : ℝ := max 8 ((2^G:ℕ):ℝ)
    L*(r/mu)^s ≤ B^s*ballCount P x r ∧
      ballCount P x r ≤ 27*U*B^s*(r/mu)^s := by
  intro B
  have hB8 : 8 ≤ B := le_max_left _ _
  have hBG : ((2^G:ℕ):ℝ) ≤ B := le_max_right _ _
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB8
  have hB1 : 1 ≤ B := by linarith
  have hBp : 1 ≤ B^s := Real.one_le_rpow hB1 hs
  have ht : 1 ≤ r/mu := (le_div_iff₀ hmu).mpr (by simpa using hr)
  have ht0 : 0 ≤ r/mu := by positivity
  by_cases hsmall : r/mu ≤ radius fine coarse
  · obtain ⟨lo,hi,hlo,hhi,hlo',hhi'⟩ := bracket_real_radius J fine coarse G hJ depth hfirst hlast hdepth hmono hgap (r/mu) ht hsmall
    have hloR : mu*radius fine (depth lo) ≤ r := by
      have hh := (le_div_iff₀ hmu).mp hlo
      simpa only [mul_comm] using hh
    have hhiR : r ≤ mu*radius fine (depth hi) := by
      have hh := (div_le_iff₀ hmu).mp hhi
      simpa only [mul_comm] using hh
    have hloB : r/mu ≤ B*radius fine (depth lo) := hlo'.trans
      (mul_le_mul_of_nonneg_right hBG (radius_pos _ _).le)
    have hhiB : radius fine (depth hi) ≤ B*(r/mu) := hhi'.trans
      (mul_le_mul_of_nonneg_right hBG ht0)
    have lowPower := Real.rpow_le_rpow ht0 hloB hs
    rw [Real.mul_rpow hB.le (radius_pos _ _).le] at lowPower
    have highPower := Real.rpow_le_rpow (radius_pos _ _).le hhiB hs
    rw [Real.mul_rpow hB.le ht0] at highPower
    constructor
    · calc
        _  ≤  L*(B^s*(radius fine (depth lo))^s) := mul_le_mul_of_nonneg_left lowPower hL
        _ = B^s*(L*(radius fine (depth lo))^s) := by ring
        _  ≤  B^s*ballCount P x (mu*radius fine (depth lo)) := mul_le_mul_of_nonneg_left (Hlo lo) (by positivity)
        _  ≤  _ := mul_le_mul_of_nonneg_left (ballCount_mono P x hloR) (by positivity)
    · calc
        _  ≤  ballCount P x (mu*radius fine (depth hi)) := ballCount_mono P x hhiR
        _  ≤  U*(radius fine (depth hi))^s := Hhi hi
        _  ≤  U*(B^s*(r/mu)^s) := mul_le_mul_of_nonneg_left highPower hU
        _  ≤  _ := by nlinarith only [show 0 ≤ U*B^s*(r/mu)^s by positivity]
  · have hlarge : mu*radius fine coarse ≤ r := by
      have hh := (lt_div_iff₀ hmu).mp (lt_of_not_ge hsmall)
      simpa only [mul_comm] using hh.le
    have htcap : r/mu ≤ B*radius fine coarse := by
      apply (div_le_iff₀ hmu).mpr
      have heq : B*radius fine coarse*mu=B/8 := by
        calc
          _ = B*(mu*radius fine coarse) := by ring
          _ = _ := by rw [houter];ring
      rw [heq]
      linarith only [hr1,hB8]
    have htbottom : radius fine coarse ≤ r/mu := (le_div_iff₀ hmu).mpr (by simpa only [mul_comm] using hlarge)
    have hlowPower := Real.rpow_le_rpow ht0 htcap hs
    rw [Real.mul_rpow hB.le (radius_pos _ _).le] at hlowPower
    have hhighPower := Real.rpow_le_rpow (radius_pos _ _).le htbottom hs
    constructor
    · calc
        _  ≤  L*(B^s*(radius fine coarse)^s) := mul_le_mul_of_nonneg_left hlowPower hL
        _ = B^s*(L*(radius fine (depth 0))^s) := by rw [hfirst];ring
        _  ≤  B^s*ballCount P x (mu*radius fine (depth 0)) := mul_le_mul_of_nonneg_left (Hlo 0) (by positivity)
        _  ≤  _ := by rw [hfirst];exact mul_le_mul_of_nonneg_left (ballCount_mono P x hlarge) (by positivity)
    · calc
        _ ≤ (P.card:ℝ) := Nat.cast_le.mpr (card_le_card (filter_subset _ _))
        _  ≤  27*U*(radius fine coarse)^s := Hglobal
        _  ≤  27*U*(r/mu)^s := mul_le_mul_of_nonneg_left hhighPower (by positivity)
        _  ≤  _ := by nlinarith only [hBp,show 0 ≤ 27*U*(r/mu)^s by positivity]

end NativeSliceRadiusInterpolation
