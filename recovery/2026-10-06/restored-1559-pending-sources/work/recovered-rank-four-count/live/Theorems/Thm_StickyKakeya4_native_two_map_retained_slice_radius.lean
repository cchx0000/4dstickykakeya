import Theorems.Thm_StickyKakeya4_native_slice_menu_ball_join

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeTwoMapRetainedSliceRadius
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeSliceClassBalls NativeSliceRadiusInterpolation NativeAnisotropicSliceLabels NativeSliceCountComparison

/-- The actual XY mesh has outer horizontal width1/64. Prepared-radius
counts extend to all radii without replacing the XY coordinates or mesh. -/
theorem all_radius_bounds64 {X : Type*} [PseudoMetricSpace X]
    (P : Finset X) (x : X) (J fine coarse G : ℕ) (hJ : 0 < J)
    (depth : Fin (J+1) → ℕ) (hfirst : depth 0=coarse)
    (hlast : depth (Fin.last J)=fine) (hdepth : ∀j,depth j ≤ fine)
    (hmono : Monotone depth) (hgap : ∀i : Fin J,depth i.succ-depth i.castSucc ≤ G)
    (mu L U s : ℝ) (hmu : 0 < mu) (hL : 0 ≤ L) (hU : 0 ≤ U) (hs : 0 ≤ s)
    (houter : mu*radius fine coarse=1/64)
    (Hlo : ∀j,L*(radius fine (depth j))^s ≤ ballCount P x (mu*radius fine (depth j)))
    (Hhi : ∀j,ballCount P x (mu*radius fine (depth j)) ≤ U*(radius fine (depth j))^s)
    (Hglobal : (P.card:ℝ) ≤ 27*U*(radius fine coarse)^s)
    (r : ℝ) (hr : mu ≤ r) (hr1 : r ≤ 1) :
    let B : ℝ := max 64 ((2^G:ℕ):ℝ)
    L*(r/mu)^s ≤ B^s*ballCount P x r ∧
      ballCount P x r ≤ 27*U*B^s*(r/mu)^s := by
  intro B
  have hB64 : 64 ≤ B := le_max_left _ _
  have hBG : ((2^G:ℕ):ℝ) ≤ B := le_max_right _ _
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB64
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
      have heq : B*radius fine coarse*mu=B/64 := by
        calc
          _ = B*(mu*radius fine coarse) := by ring
          _ = _ := by rw [houter];ring
      rw [heq]
      linarith only [hr1,hB64]
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

end NativeTwoMapRetainedSliceRadius
