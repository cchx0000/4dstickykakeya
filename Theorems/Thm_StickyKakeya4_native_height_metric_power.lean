import Theorems.Thm_StickyKakeya4_native_actual_height_metric_variation
import Theorems.Thm_StickyKakeya4_native_small_loss_parent_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeHeightMetricPower
open Classical Finset StickyKakeya4 NativeRankExponentHierarchy
open NativeHeightMetricMenu NativeSmallLossParentBudget NativeSeparatedSpanControl NativeSpanCoefficientPower
open scoped BigOperators

/-- Choose the EVEN grain count2K before tau, g and the source. -/
theorem exists_grain_count (epsilon : ℝ) (he : 0 < epsilon) (Kmin : ℕ) :
    ∃K : ℕ,0 < K ∧ Kmin ≤ K ∧ 1/((2*K:ℕ):ℝ) ≤ epsilon/2 := by
  obtain ⟨K0,hK0⟩ := exists_nat_gt (1/epsilon)
  let K := max K0 (Kmin+1)
  have hK : 0 < K := lt_of_lt_of_le (Nat.succ_pos _) (le_max_right _ _)
  have hK0K : (K0:ℝ) ≤ K := by exact_mod_cast (le_max_left K0 (Kmin+1))
  have hh := (div_lt_iff₀ he).mp hK0
  refine ⟨K,hK,(Nat.le_succ Kmin).trans (le_max_right _ _),?_⟩
  apply (div_le_iff₀ (show (0:ℝ)<((2*K:ℕ):ℝ) by positivity)).mpr
  push_cast
  nlinarith only [hh,hK0K,he]

/-- The actual stopping identity pays the finite-menu interpolation gap. -/
lemma menu_gap_power {r : ℝ} (hr : 0 < r) (K stop : ℕ) (hK : 0 < K)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) :
    ((2^((stop-6)/(2*K)+1):ℕ):ℝ) ≤ 2*r^(-(1/((2*K:ℕ):ℝ))) := by
  have hKR : (0:ℝ)<((2*K:ℕ):ℝ) := by positivity
  have hpow : ((2^(stop-6):ℕ):ℝ) ≤ 1/r := by
    have hp : ((2^(stop-6):ℕ):ℝ) ≤ ((2^stop:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) (Nat.sub_le stop 6)
    have hm := mul_le_mul_of_nonneg_right hp hr.le
    apply (le_div_iff₀ hr).mpr
    nlinarith only [hm,hidentity]
  have hfloor : (((stop-6)/(2*K):ℕ):ℝ) ≤ ((stop-6:ℕ):ℝ)/((2*K:ℕ):ℝ) := Nat.cast_div_le
  have hbase : ((2^((stop-6)/(2*K)):ℕ):ℝ) ≤ r^(-(1/((2*K:ℕ):ℝ))) := by
    calc
      _ = (2:ℝ)^((((stop-6)/(2*K):ℕ):ℝ)) := by rw [Real.rpow_natCast]; norm_cast
      _ ≤ (2:ℝ)^(((stop-6:ℕ):ℝ)/((2*K:ℕ):ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
      _ = (((2^(stop-6):ℕ):ℝ))^(1/((2*K:ℕ):ℝ)) := by
        rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
        congr 1
        ring
      _ ≤ (1/r)^(1/((2*K:ℕ):ℝ)) := Real.rpow_le_rpow (by positivity) hpow (by positivity)
      _ = _ := by rw [one_div,Real.inv_rpow hr.le,Real.rpow_neg hr.le]
  calc
    _ = 2*((2^((stop-6)/(2*K)):ℕ):ℝ) := by rw [pow_succ]; push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by norm_num)

lemma metricConstant_small_loss {r q epsilon : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (he : 0 ≤ epsilon) (hq : 0 < q) (hq1 : q ≤ 1)
    (ell K stop : ℕ) (hell : ell ≤ 3) (hK : 0 < K)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) (hqlow : r^(epsilon/6)/2 ≤ q) :
    metricConstant ((stop-6)/(2*K)+1) (coefficientCost 2 q ell) ≤
      1152*r^(-epsilon/2-1/((2*K:ℕ):ℝ)) := by
  have hmenu := menu_gap_power hr K stop hK hidentity
  have hC := (coefficientCost_le_power hq hq1 ell).trans (coefficient_small_loss hr hq hq1 ell hell hqlow)
  have hCn := coefficientCost_nonneg (by norm_num : (0:ℝ)≤2) hq ell
  have hpow : 1 ≤ r^(-epsilon/2-1/((2*K:ℕ):ℝ)) := by
    calc
      1 = r^(0:ℝ) := (Real.rpow_zero r).symm
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_ge hr hr1
        have hh : (0:ℝ) ≤ 1/((2*K:ℕ):ℝ) := by positivity
        linarith only [he,hh]
  unfold metricConstant
  apply max_le
  · nlinarith only [hpow]
  · calc
      _ ≤ (9/8)*(2*r^(-(1/((2*K:ℕ):ℝ))))*(512*r^(-epsilon/2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmenu (by norm_num)) hC hCn (by positivity)
      _ = 1152*(r^(-(1/((2*K:ℕ):ℝ)))*r^(-epsilon/2)) := by ring
      _ = _ := by rw [←Real.rpow_add hr]; congr 1; congr 1; ring

lemma metricConstant_small_loss_of_grain_count {r q epsilon : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (he : 0 ≤ epsilon) (hq : 0 < q) (hq1 : q ≤ 1)
    (ell K stop : ℕ) (hell : ell ≤ 3) (hK : 0 < K)
    (hgrain : 1/((2*K:ℕ):ℝ) ≤ epsilon/2)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) (hqlow : r^(epsilon/6)/2 ≤ q) :
    metricConstant ((stop-6)/(2*K)+1) (coefficientCost 2 q ell) ≤ 1152*r^(-epsilon) := by
  apply (metricConstant_small_loss hr hr1 he hq hq1 ell K stop hell hK hidentity hqlow).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_ge hr hr1
  linarith only [hgrain]

/-- The fixed512 time normalization is included in the once-only cutoff. -/
def normalizationConstant : ℝ := 589824

lemma absorb_normalized_metric {delta r a epsilon : ℝ} (hd : 0 < delta) (hr : 0 < r)
    (he : 0 ≤ epsilon) (hscale : r ≤ delta^a)
    (hsmall : delta^(a*epsilon) ≤ 1/normalizationConstant) :
    normalizationConstant*r^(-epsilon) ≤ r^(-2*epsilon) := by
  have hrsmall : r^epsilon ≤ 1/normalizationConstant := by
    calc
      _ ≤ (delta^a)^epsilon := Real.rpow_le_rpow hr.le hscale he
      _ = delta^(a*epsilon) := (Real.rpow_mul hd.le _ _).symm
      _ ≤ _ := hsmall
  have hC : 0 < normalizationConstant := by norm_num [normalizationConstant]
  have hpaid : normalizationConstant*r^epsilon ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hrsmall hC.le
    simpa only [mul_one_div_cancel hC.ne'] using hh
  have hsplit : r^(-epsilon)=r^epsilon*r^(-2*epsilon) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  calc
    _ = (normalizationConstant*r^epsilon)*r^(-2*epsilon) := by rw [hsplit]; ring
    _ ≤ 1*r^(-2*epsilon) := mul_le_mul_of_nonneg_right hpaid (Real.rpow_nonneg hr.le _)
    _ = _ := one_mul _

theorem exists_uniform_metric_cutoff (c epsilon : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (he : 0 < epsilon) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 → ∀i : Fin 4,
        delta^(cutoff c i*epsilon) ≤ 1/normalizationConstant := by
  have H : ∀i : Fin 4,∃di : ℝ,0 < di ∧ di ≤ 1 ∧
      ∀delta : ℝ,0 < delta → delta ≤ di → delta^(cutoff c i*epsilon) ≤ 1/normalizationConstant := by
    intro i
    have ha := (cutoff_bounds hc hc1 i).1
    exact NativeQuarterScaleParameters.exists_small_power_cutoff
      (show 0<cutoff c i*epsilon by positivity) (by norm_num [normalizationConstant])
  choose d hd _hd1 H using H
  let delta0 := min (1/8) (univ.inf' (univ_nonempty : (univ:Finset (Fin 4)).Nonempty) d)
  refine ⟨delta0,?_,min_le_left _ _,?_⟩
  · apply lt_min (by norm_num)
    exact (lt_inf'_iff _).mpr (fun i _ => hd i)
  · intro delta hdelta hsmall i
    exact H i delta hdelta ((hsmall.trans (min_le_right _ _)).trans (inf'_le d (mem_univ i)))

/-- Actual source parameters pay the full normalized metric constant.
K is fixed before tau, and the displayed cutoff is chosen before D. -/
theorem actual_metric_constant_paid {delta r q eta0 c tau epsilon : ℝ}
    (hd : 0 < delta) (hr : 0 < r) (hr1 : r ≤ 1)
    (he : 0 < epsilon) (he0 : 0 ≤ eta0) (heSmall : eta0 ≤ epsilon)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcSmall : c ≤ epsilon/24) (i : Fin 4)
    (hrdelta : r ≤ delta^(cutoff c i)) (htau : 0 ≤ tau) (g K stop ell : ℕ)
    (hK : 0 < K) (hell : ell ≤ 3) (hgrain : 1/((2*K:ℕ):ℝ) ≤ epsilon/2)
    (hTau : tau ≤ commonBudget eta0 c/(1000*(((2*K:ℕ):ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : 0 < q) (hq1 : q ≤ 1) (hqlow : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1)
    (hsmall : delta^(cutoff c i*epsilon) ≤ 1/normalizationConstant) :
    512*metricConstant ((stop-6)/(2*K)+1) (coefficientCost 2 q ell) ≤ r^(-2*epsilon) := by
  have htest := actual_test_radius_small_loss hd hr hr1 he he0 heSmall hc hc1 hcSmall i hrdelta htau
    g (2*K) hTau hgrid hqlow
  have hmetric := metricConstant_small_loss_of_grain_count hr hr1 he.le hq hq1 ell K stop hell hK hgrain hidentity htest
  calc
    _ ≤ 512*(1152*r^(-epsilon)) := mul_le_mul_of_nonneg_left hmetric (by norm_num)
    _ = normalizationConstant*r^(-epsilon) := by unfold normalizationConstant; ring
    _ ≤ _ := absorb_normalized_metric hd hr he.le hrdelta hsmall

end NativeHeightMetricPower
