import Theorems.Thm_StickyKakeya4_original_native_profile_power_algebra
import Theorems.Thm_StickyKakeya4_original_native_comparison_power_algebra
import Theorems.Thm_StickyKakeya4_native_original_log_budget
import Theorems.Thm_StickyKakeya4_native_dyadic_pruning_cutoff

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048
noncomputable section

namespace OriginalNativeProjectionPowerCutoff
open ProjectionAnnulusEnergy NativeQuarterScaleParameters NativeOriginalLogBudget

def profileConstant : ℝ := (2:ℝ)^74*3145729
def comparisonConstant : ℝ := (2:ℝ)^1018*7920^15*12672

theorem native_monomial {delta e u : ℝ} (hd : 0<delta) (a b : ℕ) :
    (delta^e)^a*(delta^(8*e/u))^b=delta^(((a:ℝ)+8*(b:ℝ)/u)*e) := by
  rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_mul hd.le,
    ←Real.rpow_mul hd.le,←Real.rpow_add hd]
  congr 1
  ring

theorem exists_native_exponent_margins {u gap eta epsilon : ℝ}
    (hu : 0<u) (hgap : 0<gap) (heta : 0<eta) (hepsilon : 0<epsilon) :
    ∃ e : ℝ, 0<e ∧ e≤u/16 ∧ e≤gap/2 ∧
      0<eta-(44+88/u)*e ∧ 0<epsilon-(386+1648/u)*e := by
  let A := 45+88/u
  let B := 387+1648/u
  have hA : 0<A := by dsimp [A]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  let e := min (u/16) (min (gap/2) (min (eta/(2*A)) (epsilon/(2*B))))
  have he : 0<e := by dsimp [e]; positivity
  have heu : e≤u/16 := min_le_left _ _
  have heg : e≤gap/2 := (min_le_right _ _).trans (min_le_left _ _)
  have heA : e≤eta/(2*A) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have heB : e≤epsilon/(2*B) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have ha := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hA)).mp heA
  have hb := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hB)).mp heB
  refine ⟨e,he,heu,heg,?_,?_⟩
  · dsimp [A] at ha
    nlinarith only [ha,heta,he]
  · dsimp [B] at hb
    nlinarith only [hb,hepsilon,he]

private theorem exists_constant_power_cutoff {a C : ℝ} (ha : 0<a) (hC : 0<C) :
    ∃ d : ℝ, 0<d ∧ d≤1 ∧ ∀ delta : ℝ, 0<delta → delta≤d → C*delta^a≤1 := by
  obtain ⟨d,hd,hd1,hcut⟩ := exists_small_power_cutoff ha (one_div_pos.mpr hC)
  refine ⟨d,hd,hd1,?_⟩
  intro delta hdelta hsmall
  have hh := (le_div_iff₀ hC).mp (hcut delta hdelta hsmall)
  simpa only [mul_comm] using hh

/-- A single original-mesh cutoff pays every numerical loss in the native
source comparison. It is fixed before the dyadic level or point cardinality. -/
theorem exists_native_power_cutoff {u gap eta epsilon scalarCutoff : ℝ}
    (hu : 0<u) (hgap : 0<gap) (heta : 0<eta) (hepsilon : 0<epsilon)
    (hcutoff : 0<scalarCutoff) :
    ∃ e d : ℝ, 0<e ∧ e≤u/16 ∧ e≤gap/2 ∧ 0<d ∧ d≤1 ∧ d ≤ scalarCutoff ∧
      ∀ n : ℕ, mesh n≤d →
        (mesh n)^(e/4)≤1/64 ∧ (mesh n)^(2*e)≤(1/(2:ℝ)^52) ∧
        ((n:ℝ)+3)^2≤1/(mesh n)^e ∧
        profileConstant/(((mesh n)^e)^44*((mesh n)^(8*e/u))^11)≤
          (mesh n)^(-eta) ∧
        comparisonConstant≤((mesh n)^e)^386*((mesh n)^(8*e/u))^206*(mesh n)^(-epsilon) := by
  obtain ⟨e,he,heu,heg,heA,heB⟩ := exists_native_exponent_margins hu hgap heta hepsilon
  obtain ⟨d1,hd1,_hd11,h1⟩ := exists_small_power_cutoff (show 0<e/4 by positivity)
    (by norm_num : (0:ℝ)<1/64)
  obtain ⟨d2,hd2,_hd21,h2⟩ := exists_small_power_cutoff (show 0<2*e by positivity)
    (by norm_num : (0:ℝ)<1/2^52)
  obtain ⟨d3,hd3,_hd31,h3⟩ := exists_constant_power_cutoff heA
    (show 0<profileConstant by unfold profileConstant; positivity)
  obtain ⟨d4,hd4,_hd41,h4⟩ := exists_constant_power_cutoff heB
    (show 0<comparisonConstant by unfold comparisonConstant; positivity)
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨d5,hd5,_hd51,h5⟩ := exists_logarithmic_budget_cutoff
    (show 0<e/2 by positivity) (by norm_num : (0:ℝ)≤3)
    (show 0≤1/Real.log 2 by positivity)
  let d := min 1 (min scalarCutoff (min d1 (min d2 (min d3 (min d4 d5)))))
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨e,d,he,heu,heg,hd,min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),?_⟩
  intro n hn
  have hδ := mesh_pos n
  have hsub : mesh n ≤ scalarCutoff ∧ mesh n≤d1 ∧ mesh n≤d2 ∧ mesh n≤d3 ∧ mesh n≤d4 ∧ mesh n≤d5 := by
    dsimp [d] at hn
    simp only [le_min_iff] at hn
    exact hn.2
  refine ⟨h1 _ hδ hsub.2.1,h2 _ hδ hsub.2.2.1,?_,?_,?_⟩
  · have hh := h5 (mesh n) hδ hsub.2.2.2.2.2
    have hlog : (n:ℝ)+3=3+(1/Real.log 2)*(-Real.log (mesh n)) := by
      have hh' := NativeDyadicPruningCutoff.dyadic_depth_log n (show mesh n=(2:ℝ)⁻¹^n by simp only [mesh,one_div])
      have hform : 3+(1/Real.log 2)*(-Real.log (mesh n))=2+(1+(-Real.log (mesh n))/Real.log 2) := by ring
      rw [hform,←hh']
      ring
    rw [←hlog] at hh
    have hp := pow_le_pow_left₀ (show 0≤(n:ℝ)+3 by positivity) hh 2
    have hid : ((mesh n)^(-(e/2)))^2=1/(mesh n)^e := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hδ.le]
      norm_num only [Nat.cast_ofNat]
      rw [show -(e/2)*(2:ℝ) = -e by ring,Real.rpow_neg hδ.le,one_div]
    simpa only [hid] using hp
  · rw [native_monomial hδ 44 11]
    norm_num only [Nat.cast_ofNat] at *
    have hh := h3 (mesh n) hδ hsub.2.2.2.1
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hδ _)).mpr
    have hp := mul_le_mul_of_nonneg_right hh (Real.rpow_pos_of_pos hδ (-eta+(44+88/u)*e)).le
    have hid : profileConstant*(mesh n)^(eta-(44+88/u)*e)*
        (mesh n)^(-eta+(44+88/u)*e)=profileConstant := by
      rw [mul_assoc,←Real.rpow_add hδ]
      rw [show eta-(44+88/u)*e+(-eta+(44+88/u)*e)=0 by ring,Real.rpow_zero,mul_one]
    rw [hid,one_mul] at hp
    rw [←Real.rpow_add hδ]
    convert hp using 1
  · rw [native_monomial hδ 386 206]
    norm_num only [Nat.cast_ofNat] at *
    have hh := h4 (mesh n) hδ hsub.2.2.2.2.1
    have hp := mul_le_mul_of_nonneg_right hh
      (Real.rpow_pos_of_pos hδ ((386+1648/u)*e-epsilon)).le
    have hid : comparisonConstant*(mesh n)^(epsilon-(386+1648/u)*e)*
        (mesh n)^((386+1648/u)*e-epsilon)=comparisonConstant := by
      rw [mul_assoc,←Real.rpow_add hδ]
      rw [show epsilon-(386+1648/u)*e+((386+1648/u)*e-epsilon)=0 by ring,Real.rpow_zero,mul_one]
    rw [hid,one_mul] at hp
    rw [←Real.rpow_add hδ]
    simpa only [sub_eq_add_neg] using hp

end OriginalNativeProjectionPowerCutoff
