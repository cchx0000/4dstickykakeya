import Theorems.Thm_StickyKakeya4_native_coarse_shading_pruning
import Theorems.Thm_StickyKakeya4_native_dyadic_pruning_cutoff
import Theorems.Thm_StickyKakeya4_native_finite_kakeya_exponent
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeCoarseMassBudget
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalLogBudget NativeDyadicPruningCutoff
open NativeFiniteKakeyaCounts NativeOriginalPrunedMass
open scoped BigOperators ENNReal

def colorCost : ℝ := 23328*512^3
def massCost : ℝ := 2*43*colorCost
def pruneCost : ℝ := 746496*64^3*volumeConstant
lemma colorCost_pos : 0 < colorCost := by norm_num [colorCost]
lemma massCost_pos : 0 < massCost := by norm_num [massCost,colorCost]
lemma pruneCost_pos : 0 < pruneCost := by dsimp [pruneCost]; exact mul_pos (by norm_num) volumeConstant_pos

/-- Source-scale constants and the logarithmic number of levels are fixed
before the finite source or its coarse scale. -/
theorem exists_mass_cutoff {zeta : ℝ} (hz : 0 < zeta) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      (∀ (delta : ℝ) (level : ℕ),0 < delta → delta ≤ delta0 → delta=(2:ℝ)⁻¹^level →
        massCost*delta^zeta ≤ 1 ∧ 2*delta^zeta ≤ 1 ∧
        2*pruneCost*((level:ℝ)+1) ≤ delta^(-zeta)) ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
        IsWangZakharovNativeFiniteInput D eta → D.thickness ≤ delta0 → eta ≤ zeta/16 →
          D.thickness^zeta ≤ (wzTotalShadingVolume D).toReal := by
  have hprune := pruneCost_pos
  have hmass := massCost_pos
  obtain ⟨dt,hdt,htube⟩ := exists_markedUnitTube_admissible_scale (half_pos hz)
  obtain ⟨dc,hdc,_hdc1,hconst⟩ := exists_positive_rpow_absorption_threshold hz
    (show 0 ≤ max massCost 2 by positivity) (by norm_num : (0:ℝ)<1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨dl,hdl,_hdl1,hlog⟩ := exists_logarithmic_budget_cutoff hz
    (show 0 ≤ 2*pruneCost by positivity) (show 0 ≤ (2*pruneCost)/Real.log 2 by positivity)
  let delta0 := min (1/8:ℝ) (min dt (min dc dl))
  have hd0 : 0 < delta0 := lt_min (by norm_num) (lt_min hdt (lt_min hdc hdl))
  refine ⟨delta0,hd0,min_le_left _ _,?_,?_⟩
  · intro delta level hd hsmall hdy
    have hrest := hsmall.trans (min_le_right _ _)
    have hmore := hrest.trans (min_le_right _ _)
    have hc := hconst delta hd (hmore.trans (min_le_left _ _))
    have hl := hlog delta hd (hmore.trans (min_le_right _ _))
    refine ⟨(mul_le_mul_of_nonneg_right (le_max_left massCost 2) (Real.rpow_pos_of_pos hd _).le).trans hc,
      (mul_le_mul_of_nonneg_right (le_max_right massCost 2) (Real.rpow_pos_of_pos hd _).le).trans hc,?_⟩
    rw [dyadic_depth_log level hdy]
    convert hl using 1
    ring
  · intro n D eta h hsmall heta
    have hd := h.1.2.1
    have hdt' := (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
    have hh := total_shading_lower h (fun i => htube (D.line i) (h.1.2.2.2.2.1 i) D.thickness hd hdt')
    have hfin : wzTotalShadingVolume D≠⊤ := by
      simpa only [shadingMass,wzTotalShadingVolume] using shadingMass_ne_top h univ
    have hr := ENNReal.toReal_mono hfin hh
    simp only [ENNReal.rpow_eq_pow] at hr
    simp only [←ENNReal.toReal_rpow,ENNReal.toReal_ofReal hd.le] at hr
    exact (Real.rpow_le_rpow_of_exponent_ge hd h.1.2.2.1 (by linarith)).trans hr

/-- The actual original shading lower mass, half-mass original pruning,
coarse incidence capacity and directional color loss imply positive mass
on the chosen color. All losses stay at the original delta scale. -/
lemma chosen_color_mass {delta zeta old retained full chosen : ℝ}
    (hd : 0 < delta) (hret : old ≤ 2*retained)
    (hsource : delta^zeta ≤ old)
    (hcoarse : retained ≤ 43*delta^(-zeta)*full)
    (hcolor : full ≤ colorCost*delta^(-zeta)*chosen)
    (hsmall : massCost*delta^zeta ≤ 1) : delta^(4*zeta) ≤ chosen := by
  have hcross : delta^zeta ≤ (massCost*delta^(-2*zeta))*chosen := by
    calc
      _ ≤ old := hsource
      _ ≤ 2*retained := hret
      _ ≤ 2*(43*delta^(-zeta)*full) := mul_le_mul_of_nonneg_left hcoarse (by norm_num)
      _ ≤ 2*(43*delta^(-zeta)*(colorCost*delta^(-zeta)*chosen)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcolor (by positivity)) (by norm_num)
      _ = _ := by
        rw [show -2*zeta=(-zeta)+(-zeta) by ring,Real.rpow_add hd]
        dsimp [massCost]
        ring
  have hbase : (massCost*delta^(-2*zeta))*delta^(4*zeta) ≤ delta^zeta := by
    calc
      _ = (massCost*delta^zeta)*delta^zeta := by
        rw [mul_assoc,←Real.rpow_add hd,show -2*zeta+4*zeta=zeta+zeta by ring,Real.rpow_add hd]
        ring
      _ ≤ 1*delta^zeta := mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hd _).le
      _ = _ := one_mul _
  have hp : 0 < massCost*delta^(-2*zeta) := mul_pos massCost_pos (Real.rpow_pos_of_pos hd _)
  exact (mul_le_mul_iff_right₀ hp).mp (hbase.trans hcross)

/-- Choosing the deletion threshold delta^(8*zeta) preserves half the actual
color shading and leaves a positive delta^(5*zeta) aggregate mass. -/
lemma pruned_color_mass {delta zeta chosen kept : ℝ} {m level : ℕ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hz : 0 ≤ zeta) (hm : m ≤ level)
    (hcolor : delta^(4*zeta) ≤ chosen)
    (hprune : chosen ≤ kept+pruneCost*((m:ℝ)+1)*delta^(7*zeta))
    (hlog : 2*pruneCost*((level:ℝ)+1) ≤ delta^(-zeta))
    (hsmall : 2*delta^zeta ≤ 1) : chosen ≤ 2*kept ∧ delta^(5*zeta) ≤ kept := by
  have hcost : 2*(pruneCost*((m:ℝ)+1)*delta^(7*zeta)) ≤ delta^(4*zeta) := by
    calc
      _ ≤ (2*pruneCost*((level:ℝ)+1))*delta^(7*zeta) := by
        have hm' : (m:ℝ)+1 ≤ (level:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hm 1
        have hh := mul_le_mul_of_nonneg_left hm' (le_of_lt (mul_pos (by norm_num : (0:ℝ)<2) pruneCost_pos))
        have hhh := mul_le_mul_of_nonneg_right hh (Real.rpow_pos_of_pos hd (7*zeta)).le
        simpa only [mul_assoc] using hhh
      _ ≤ delta^(-zeta)*delta^(7*zeta) := mul_le_mul_of_nonneg_right hlog (Real.rpow_pos_of_pos hd _).le
      _ = delta^(6*zeta) := by rw [←Real.rpow_add hd]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  have hpow : 2*delta^(5*zeta) ≤ delta^(4*zeta) := by
    calc
      _ = (2*delta^zeta)*delta^(4*zeta) := by rw [mul_assoc,←Real.rpow_add hd]; congr 1; ring
      _ ≤ 1*delta^(4*zeta) := mul_le_mul_of_nonneg_right hsmall (Real.rpow_pos_of_pos hd _).le
      _ = _ := one_mul _
  constructor <;> linarith

end NativeCoarseMassBudget
