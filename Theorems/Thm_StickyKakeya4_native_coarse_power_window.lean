import Theorems.Thm_StickyKakeya4_native_coarse_relative_cw
import Theorems.Thm_StickyKakeya4_native_padded_source_admissibility
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeCoarsePowerWindow
open StickyKakeya4 NativeCoarseRelativeCW NativeOriginalPrunedMass

def densityCost : ℝ := 373248*64^3*volumeConstant
lemma densityCost_pos : 0 < densityCost := by
  have hv := volumeConstant_pos
  dsimp [densityCost]
  positivity

/-- A fixed window exponent and requested output loss choose the original
source exponent BEFORE delta. Both coarse and fine-side scales remain visible. -/
theorem exists_power_window_cutoff {e a : ℝ} (he : 0 < e) (ha : 0 < a) :
    let zeta := a*e/32
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧ ∀delta rho eta : ℝ,
      0 < delta → delta ≤ delta0 → 0 < rho → rho ≤ delta^a → delta/rho ≤ delta^a → eta ≤ zeta/16 →
        delta ≤ rho ∧ 64*rho ≤ 1 ∧ (64*rho)^e ≤ delta^(8*zeta) ∧
        10077696*delta^(8*zeta) ≤ 1 ∧ densityCost*delta^zeta ≤ 1 ∧
        cwCost*delta^(8*zeta-(eta+6*zeta)) ≤ 1 := by
  let zeta := a*e/32
  have hz : 0 < zeta := by dsimp [zeta]; positivity
  let C := max (10077696:ℝ) (max densityCost (max cwCost ((64:ℝ)^e)))
  have hC : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 10077696).trans (le_max_left _ _)
  obtain ⟨dc,hdc,hdc1,hconst⟩ := exists_positive_rpow_absorption_threshold hz hC (by norm_num : (0:ℝ)<1)
  obtain ⟨dw,hdw,_hdw1,hwindow⟩ := exists_positive_rpow_absorption_threshold ha
    (by norm_num : (0:ℝ) ≤ 64) (by norm_num : (0:ℝ)<1)
  refine ⟨min dc dw,lt_min hdc hdw,(min_le_left _ _).trans hdc1,?_⟩
  intro delta rho eta hd hsmall hr hcoarse hfine heta
  change eta ≤ zeta/16 at heta
  have hd1 := (hsmall.trans (min_le_left _ _)).trans hdc1
  have hc := hconst delta hd (hsmall.trans (min_le_left _ _))
  have hw := hwindow delta hd (hsmall.trans (min_le_right _ _))
  have hda : delta^a ≤ 1 := Real.rpow_le_one hd.le hd1 ha.le
  have hfine' : delta ≤ rho := (div_le_one hr).mp (hfine.trans hda)
  have hcoarse' : 64*rho ≤ 1 := (mul_le_mul_of_nonneg_left hcoarse (by norm_num)).trans hw
  have hcost {c g : ℝ} (hcC : c ≤ C) (hg : zeta ≤ g) : c*delta^g ≤ 1 :=
    (mul_le_mul_of_nonneg_right hcC (Real.rpow_pos_of_pos hd _).le).trans
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hd hd1 hg) hC).trans hc)
  have h64 : (64:ℝ)^e ≤ C :=
    (le_max_right cwCost _).trans ((le_max_right densityCost _).trans (le_max_right _ _))
  have hpower : (64*rho)^e ≤ delta^(8*zeta) := by
    calc
      _ ≤ (64*delta^a)^e := Real.rpow_le_rpow (by positivity)
        (mul_le_mul_of_nonneg_left hcoarse (by norm_num)) he.le
      _ = (64:ℝ)^e*delta^(a*e) := by rw [Real.mul_rpow (by norm_num) (Real.rpow_pos_of_pos hd _).le,←Real.rpow_mul hd.le]
      _ = ((64:ℝ)^e*delta^(a*e-8*zeta))*delta^(8*zeta) := by
        rw [mul_assoc,←Real.rpow_add hd,sub_add_cancel]
      _ ≤ 1*delta^(8*zeta) := mul_le_mul_of_nonneg_right
        (hcost h64 (by dsimp [zeta] at hz ⊢; linarith)) (Real.rpow_pos_of_pos hd _).le
      _ = _ := one_mul _
  refine ⟨hfine',hcoarse',hpower,hcost (le_max_left _ _) (show zeta ≤ 8*zeta by linarith),?_,?_⟩
  · exact hcost ((le_max_left densityCost _).trans (le_max_right _ _)) le_rfl
  · exact hcost ((le_max_left cwCost _).trans ((le_max_right densityCost _).trans (le_max_right _ _))) (show zeta ≤ 8*zeta-(eta+6*zeta) by linarith)

lemma negative_power_transfer {delta out e zeta : ℝ} (hd : 0 < delta) (ho : 0 < out)
    (hp : out^e ≤ delta^(8*zeta)) : delta^(-8*zeta) ≤ out^(-e) := by
  have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (Real.rpow_pos_of_pos ho _) hp
  simpa only [show -8*zeta=-(8*zeta) by ring,Real.rpow_neg hd.le,Real.rpow_neg ho.le,one_div] using hh

lemma coefficient_to_original_power {delta eta zeta C : ℝ} (hd : 0 < delta)
    (hcost : C*delta^(8*zeta-(eta+6*zeta)) ≤ 1) :
    C*delta^(-eta-6*zeta) ≤ delta^(-8*zeta) := by
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hd (8*zeta))).mp
  have hl : (C*delta^(-eta-6*zeta))*delta^(8*zeta)=C*delta^(8*zeta-(eta+6*zeta)) := by
    rw [mul_assoc,←Real.rpow_add hd]
    congr 2
    ring
  have hr : delta^(-8*zeta)*delta^(8*zeta)=1 := by rw [←Real.rpow_add hd]; simp
  rw [hl,hr]
  exact hcost

end NativeCoarsePowerWindow
