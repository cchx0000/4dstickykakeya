import Theorems.Thm_StickyKakeya4_native_middle_window_balance
import Theorems.Thm_StickyKakeya4_wz_carrier_pruning

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeTwoStageTransversalityBudget
open StickyKakeya4 NativeMiddleWindowBalance

/-- The second actual transfer cost also pays its retained-incidence factor.
This keeps the original reference and does not normalize the selected source. -/
lemma retention_radix_le_of_transfer_cost {delta eta cost : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta)
    (F Q : ℕ) (G : ℝ) (hGF : G ≤ F)
    (hcost : (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) ≤
      delta^(-cost)) : G*(Q:ℝ)^2 ≤ delta^(-cost) := by
  have hC : (F:ℝ) ≤ (125*175616*16384:ℝ)*(F:ℝ) := by
    have hF := Nat.cast_nonneg (α := ℝ) F
    nlinarith
  have hp : 1 ≤ delta^(-eta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr heta)
  calc
    _ ≤ (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2 :=
      mul_le_mul_of_nonneg_right (hGF.trans hC) (sq_nonneg (Q:ℝ))
    _ ≤ (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*delta^(-eta) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
        (show 0 ≤ (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2 by positivity)
    _ ≤ _ := hcost

/-- Earlier-rank failure at the selected test radius has the extra power
needed to pay refinement. This uses the actual test upper bound only. -/
lemma test_power_le {r q beta previous stop : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hq : 0 ≤ q)
    (hprevious : 0 ≤ previous) (hqr : q ≤ r^beta)
    (hgap : 2*stop ≤ beta*previous) : q^previous ≤ r^(2*stop) := by
  calc
    q^previous ≤ (r^beta)^previous := Real.rpow_le_rpow hq hqr hprevious
    _ = r^(beta*previous) := (Real.rpow_mul hr.le beta previous).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hr hr1 hgap

/-- Choose the source cutoff before both stages and all their actual radices.
The two returned transfer costs, together with the earlier-rank test, imply
the exact half-mass budget used by the original-incidence tuple constructor.
No pointwise retention or final power-budget hypothesis is supplied. -/
theorem exists_half_mass_cutoff {a stop c1 c2 menuCost : ℝ}
    (hstop : 0 < stop) (hmenu : 0 < menuCost)
    (hgap : c1+c2 < a*stop) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        ∀ F1 F2 Q1 Q2 : ℕ, 0 < F1 →
          ∀ eta1 eta2 G r q beta previous : ℝ,
          0 ≤ eta1 → 0 ≤ eta2 → 0 ≤ G → G ≤ F2 →
          0 < r → r ≤ 1 → r ≤ delta^a → 0 ≤ q → 0 ≤ previous →
          q ≤ r^beta → 2*stop ≤ beta*previous →
          (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta1) ≤ delta^(-c1) →
          (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-c2) →
          q^previous*G*(Q1:ℝ)^2*(Q2:ℝ)^2 ≤ (r^stop/menuCost)/2 := by
  obtain ⟨delta0,hd0,hd01,hcut⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < a*stop-(c1+c2) by linarith)
    (show 0 ≤ 2*menuCost by positivity) (show (0:ℝ)<1 by norm_num)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall F1 F2 Q1 Q2 hF1 eta1 eta2 G r q beta previous
    heta1 heta2 hG hGF hr hr1 hrdelta hq hprevious hqr hprev hcost1 hcost2
  have hd1 := hsmall.trans hd01
  have hQ1 := radix_sq_le_of_transfer_cost hd hd1 heta1 F1 Q1 hF1 hcost1
  have hQ2 := retention_radix_le_of_transfer_cost hd hd1 heta2 F2 Q2 G hGF hcost2
  have hqpow := test_power_le hr hr1 hq hprevious hqr hprev
  have hcost : G*(Q1:ℝ)^2*(Q2:ℝ)^2 ≤ delta^(-(c1+c2)) := by
    calc
      _ = (Q1:ℝ)^2*(G*(Q2:ℝ)^2) := by ring
      _ ≤ delta^(-c1)*delta^(-c2) := mul_le_mul hQ1 hQ2 (by positivity) (by positivity)
      _ = _ := by rw [←Real.rpow_add hd]; congr 1; ring
  have hrpow : r^stop ≤ delta^(a*stop) := by
    calc
      _ ≤ (delta^a)^stop := Real.rpow_le_rpow hr.le hrdelta hstop.le
      _ = _ := (Real.rpow_mul hd.le a stop).symm
  have hpaid : 2*menuCost*(r^stop*delta^(-(c1+c2))) ≤ 1 := by
    calc
      _ ≤ 2*menuCost*(delta^(a*stop)*delta^(-(c1+c2))) := by gcongr
      _ = 2*menuCost*delta^(a*stop-(c1+c2)) := by
        rw [←Real.rpow_add hd]; congr 2
      _ ≤ 1 := hcut delta hd hsmall
  have hs : 0 < r^stop := Real.rpow_pos_of_pos hr _
  have hfinal : r^(2*stop)*delta^(-(c1+c2)) ≤ (r^stop/menuCost)/2 := by
    have hmul := mul_le_mul_of_nonneg_right hpaid hs.le
    have he : r^(2*stop)=r^stop*r^stop := by
      rw [←Real.rpow_add hr]; congr 1; ring
    rw [he]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (le_div_iff₀ hmenu).mpr
    nlinarith
  calc
    _ = q^previous*(G*(Q1:ℝ)^2*(Q2:ℝ)^2) := by ring
    _ ≤ r^(2*stop)*delta^(-(c1+c2)) :=
      mul_le_mul hqpow hcost (by positivity) (Real.rpow_nonneg hr.le _)
    _ ≤ _ := hfinal

end NativeTwoStageTransversalityBudget
