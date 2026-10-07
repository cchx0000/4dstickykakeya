import Theorems.Thm_StickyKakeya4_native_two_axis_conditional_transfer
import Theorems.Thm_StickyKakeya4_native_middle_window_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeMiddleTwoScaleBalance
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalParentDensityCore NativeJointUniformCoarseRelations NativeConditionedPairMenu
open NativeTwoScaleConfiguration NativeTwoAxisPowerInterpolation NativeTwoAxisConditionalTransfer
open NativeFixedCompactKakeyaExponent NativeFixedSizeScaleMenu NativeScaleMenuSuccessor

/-- Both physical conditional bounds hold at every pair in the middle window
of the SAME finite-menu source. The near-diagonal branch is the actual
six-dimensional descendant estimate, and the far branch uses the genuine
forward/reverse physical comparisons and conditioned menu uniformity. -/
theorem middle_pair_bounds {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (E : Finset (Fin n × Index)) (hE : E⊆NativeCubicalIncidenceCounts.incidences original)
    (hER : ∀z∈E,z.1∈R) (level : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (w : ℝ) (hw : 0 < w) (hwsmall : w < 1/2) (g rad : ℕ)
    (hg : 0 < g) (hgl : g ≤ level) (hgrid : 1/(g:ℝ) < w/4)
    (loss target : ℝ) (hcostQ : (729:ℝ)*(rad:ℝ)^4 ≤ D.thickness^(-loss))
    (hcost : (729:ℝ) ≤ D.thickness^(-loss)) (hdiag : 12*w ≤ target)
    (hmargin : 2*loss+16*(2/(g:ℝ)) ≤ target)
    (HU : ∀i j : Fin (g+1),
      HasUniformFibers E rad (conditionedGlobalPair h R a level
        (windowSchedule w hw.le g level i).val (windowSchedule w hw.le g level j).val) ∧
      HasUniformFibers E rad (conditionedGlobalPoint h R a level
        (windowSchedule w hw.le g level i).val (windowSchedule w hw.le g level j).val))
    (HM : ∀i j : Fin (g+1),
      (windowSchedule w hw.le g level i).val ≤ (windowSchedule w hw.le g level j).val →
      ((2^(windowSchedule w hw.le g level i).val:ℕ):ℝ)/
        ((2^(windowSchedule w hw.le g level j).val:ℕ):ℝ) ≤ D.thickness^(w/2) →
      HasConditionalTwoScale h R E a level
        (windowSchedule w hw.le g level i).val (windowSchedule w hw.le g level j).val loss)
    (m f : ℕ) (hmf : m ≤ f)
    (hmlo : w*(level:ℝ) ≤ m) (hfhi : (f:ℝ) ≤ (1-w)*(level:ℝ)) :
    HasConditionalTwoScale h R E a level m f target := by
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
  have hmfR : (m:ℝ) ≤ f := by exact_mod_cast hmf
  have hmhi : (m:ℝ) ≤ (1-w)*(level:ℝ) := hmfR.trans hfhi
  have hflo : w*(level:ℝ) ≤ f := hmlo.trans hmfR
  have hfl : f ≤ level := by
    have hh : (f:ℝ) ≤ level := by nlinarith
    exact_mod_cast hh
  intro p hp
  change D.thickness^target*((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent) ≤ _ ∧ _
  rw [conditional_full_eq_image h R E a level m f hER p,←depthPower_eq_relative]
  have hP := (depthPower_pos extremalExponent m f).le
  by_cases hNear : ((f-m:ℕ):ℝ) ≤ (2*w)*(level:ℝ)
  · have hh := NativeConditionalCoarseDiagonal.actual_short_gap_power h R E a level m f hmf hdy
      (2*w) extremalExponent (by positivity) extremalExponent_nonneg
      (extremalExponent_le_three.trans (by norm_num)) hNear p hp
    rw [←depthPower_eq_nat hmf] at hh
    have hmarginNear : 6*(2*w) ≤ target := by linarith
    constructor
    · exact (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 hmarginNear) hP).trans hh.1
    · exact hh.2.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith : -target ≤ -6*(2*w))) hP)
  · have hlarge := NativeMiddleWindowBalance.large_level_of_grid w hw g level hg hgrid hgl
    obtain ⟨jc,hcm,_hcGap,hcGapR⟩ :=
      exists_window_predecessor w hw hwsmall g level m hg hgrid hlarge hmlo hmhi
    obtain ⟨jd,hmd,_hdGap,hdGapR⟩ :=
      exists_window_successor w hw hwsmall g level m hg hlarge hmlo hmhi
    obtain ⟨jb,hbf,_hbGap,hbGapR⟩ :=
      exists_window_predecessor w hw hwsmall g level f hg hgrid hlarge hflo hfhi
    let c := (windowSchedule w hw.le g level jc).val
    let d := (windowSchedule w hw.le g level jd).val
    let b := (windowSchedule w hw.le g level jb).val
    let s := 2/(g:ℝ)
    have hs : 0 ≤ s := by dsimp [s]; positivity
    change 2*loss+16*s ≤ target at hmargin
    have hsSmall : s ≤ w/2 := by
      dsimp [s]
      rw [show 2/(g:ℝ)=2*(1/(g:ℝ)) by ring]
      linarith
    have hGapC : ((m-c:ℕ):ℝ) ≤ s*level := gap_le_twice_fraction g level m c hg hgl hcGapR
    have hGapF : ((f-b:ℕ):ℝ) ≤ s*level := gap_le_twice_fraction g level f b hg hgl hbGapR
    have hGapD : ((d-m:ℕ):ℝ) ≤ s*level := hdGapR.trans (by
      dsimp [s]
      have hh : 1/(g:ℝ) ≤ 2/(g:ℝ) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_right hh hln)
    have hFar : 2*w*(level:ℝ) < (f:ℝ)-(m:ℝ) := by
      rw [Nat.cast_sub hmf] at hNear
      exact lt_of_not_ge hNear
    have hGapDR : (d:ℝ)-(m:ℝ) ≤ s*level := by
      calc
        _ = ((d-m:ℕ):ℝ) := (Nat.cast_sub hmd).symm
        _ ≤ _ := hGapD
    have hGapFR : (f:ℝ)-(b:ℝ) ≤ s*level := by
      calc
        _ = ((f-b:ℕ):ℝ) := (Nat.cast_sub hbf).symm
        _ ≤ _ := hGapF
    have hSmallLevel : s*(level:ℝ) ≤ (w/2)*(level:ℝ) := mul_le_mul_of_nonneg_right hsSmall hln
    have hSepD : (w/2)*(level:ℝ) ≤ (b:ℝ)-(d:ℝ) := by nlinarith
    have hdb : d ≤ b := by
      have hh : (d:ℝ) ≤ b := by nlinarith
      exact_mod_cast hh
    have hcmR : (c:ℝ) ≤ m := by exact_mod_cast hcm
    have hmdR : (m:ℝ) ≤ d := by exact_mod_cast hmd
    have hSepC : (w/2)*(level:ℝ) ≤ (b:ℝ)-(c:ℝ) := by linarith
    have hMenuC := HM jc jb (hcm.trans (hmd.trans hdb)) (depth_gap_power hdy hSepC)
    have hMenuD := HM jd jb hdb (depth_gap_power hdy hSepD)
    obtain ⟨hG,hX⟩ := HU jc jb
    have hh := far_pair_bounds h original horiginal ha R E hE hER level c m d b f hdy
      hcm hmd hdb hbf hfl hGapC hGapD hGapF rad hG hX hcostQ hcost
      (fun q hq => (scheduled_image_bounds h R E a level c b loss hER hMenuC q hq).2)
      (fun q hq => (scheduled_image_bounds h R E a level d b loss hER hMenuD q hq).1) p hp
    have hkS := mul_le_mul_of_nonneg_left extremalExponent_le_three hs
    have hmarginLower : 2*loss+s*(4+2*extremalExponent) ≤ target := by nlinarith
    have hmarginUpper : 2*loss+s*(10+extremalExponent) ≤ target := by nlinarith
    constructor
    · exact (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 hmarginLower) hP).trans hh.1
    · exact hh.2.trans (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hmarginUpper)) hP)

end NativeMiddleTwoScaleBalance
