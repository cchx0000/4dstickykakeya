import Theorems.Thm_StickyKakeya4_native_middle_grain_parent_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeSmallLossParentBudget
open Classical Finset StickyKakeya4 NativeRankExponentHierarchy
open NativeMiddleGrainParentBudget NativeCompatibleWeightedRetention
open NativeSpanCoefficientPower NativeSeparatedSpanControl
open NativeRetainedQueryMenu NativeCompatibleNodeDirections NativeDirectionRankDichotomy
open NativeHorizontalGrainSlice NativeSpatialAngularGeometry NativeOriginalParentSelection NativeCommonCubicalMesh
open scoped BigOperators

/-- The original source grid gives an arbitrarily small separation exponent
when the two INITIAL hierarchy parameters are chosen below the requested loss. -/
theorem actual_test_radius_small_loss {delta r q eta0 c tau epsilon : ℝ}
    (hd : 0 < delta) (hr : 0 < r) (hr1 : r ≤ 1)
    (he : 0 < epsilon) (he0 : 0 ≤ eta0) (heSmall : eta0 ≤ epsilon)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcSmall : c ≤ epsilon/24) (i : Fin 4)
    (hrdelta : r ≤ delta^(cutoff c i)) (htau : 0 ≤ tau) (g J : ℕ)
    (hTau : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q) :
    r^(epsilon/6)/2 ≤ q := by
  have ha := (cutoff_bounds hc hc1 i).1
  have hident := cutoff_mul_rankLoss eta0 c i
  have ht := NativeGeneralRankScalarBudget.tau_budget htau J
    (show tau ≤ cutoff c i*rankLoss eta0 c i/(1000*((J:ℝ)+1)) by rwa [hident])
  have hg := NativeRankFourScalarBudget.grid_inverse_le_tau htau g hgrid
  have heRank := rankLoss_le_initial he0 hc.le hc1 i
  have hgridDiv : (1/(g:ℝ))/cutoff c i ≤ epsilon/1000 := by
    apply (div_le_iff₀ ha).mpr
    have hm := mul_le_mul_of_nonneg_left (heRank.trans heSmall) ha.le
    nlinarith only [ht,hg,hm]
  have hexp : 2*c+(1/(g:ℝ))/cutoff c i ≤ epsilon/6 := by
    linarith only [hcSmall,hgridDiv,he]
  have hdPower := delta_loss_lower hd hr.le ha (show (0:ℝ)≤1/(g:ℝ) by positivity) hrdelta
  have hq' := NativeRankFourScalarBudget.actual_test_lower hd hr g hq
  calc
    _ ≤ r^(2*c+(1/(g:ℝ))/cutoff c i)/2 :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hr hr1 hexp) (by norm_num)
    _ = (r^(2*c)*r^((1/(g:ℝ))/cutoff c i))/2 := by rw [Real.rpow_add hr]
    _ ≤ (r^(2*c)*delta^(1/(g:ℝ)))/2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdPower (Real.rpow_nonneg hr.le _)) (by norm_num)
    _ ≤ _ := hq'

lemma coefficient_small_loss {r q epsilon : ℝ} (hr : 0 < r)
    (hq : 0 < q) (hq1 : q ≤ 1) (ell : ℕ) (hell : ell ≤ 3)
    (hqlow : r^(epsilon/6)/2 ≤ q) :
    (4/q)^ell ≤ 512*r^(-epsilon/2) := by
  have hbase : 1 ≤ 4/q := (le_div_iff₀ hq).mpr (by linarith)
  have hpow : (4/q)^ell ≤ (4/q)^3 := pow_le_pow_right₀ hbase hell
  have hlow : 4/q ≤ 8/r^(epsilon/6) := by
    apply (div_le_div_iff₀ hq (Real.rpow_pos_of_pos hr _)).mpr
    linarith only [hqlow]
  have hcube := pow_le_pow_left₀ (by positivity : (0:ℝ)≤4/q) hlow 3
  have hcubepow : (r^(epsilon/6))^3=r^(epsilon/2) := by
    rw [←Real.rpow_mul_natCast hr.le]
    congr 1
    ring
  have heq : (8/r^(epsilon/6))^3=512*r^(-epsilon/2) := by
    rw [div_pow,hcubepow,show -epsilon/2=-(epsilon/2) by ring,Real.rpow_neg hr.le]
    norm_num
    ring
  exact hpow.trans (hcube.trans_eq heq)

lemma normalized_error_small_loss {r q epsilon : ℝ}
    (hr : 0 < r) (hq : 0 < q) (hq1 : q ≤ 1)
    (stop ell : ℕ) (hs : 6 ≤ stop) (hell : ell ≤ 3)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) (hqlow : r^(epsilon/6)/2 ≤ q) :
    normalizedError (middleDepth stop) ell r q ≤ errorConstant*r^(1/2-epsilon/2) := by
  obtain ⟨_hD,hD1,_hsq,hlo,_hhi⟩ := middle_scale_bounds stop hs r hidentity
  have hrD : r ≤ ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^2 := by linarith only [hlo,hr]
  have herror := normalized_error_le_scale hq hq1 (middleDepth stop) ell hrD hD1
  have hroot := middle_scale_root_bound hr stop hs hidentity
  have hcoefficient := coefficient_small_loss hr hq hq1 ell hell hqlow
  calc
    _ ≤ 456*((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))*(4/q)^ell := herror
    _ ≤ (456*(80*r^(1/2:ℝ)))*(512*r^(-epsilon/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hroot (by norm_num)) hcoefficient (by positivity) (by positivity)
    _ = errorConstant*(r^(1/2:ℝ)*r^(-epsilon/2)) := by unfold errorConstant; ring
    _ = _ := by rw [←Real.rpow_add hr]; congr 1; ring

/-- One finite cutoff, fixed before D, pays the fixed geometric constant at
all four actual rank choices. It depends only on the chosen loss and c. -/
theorem exists_uniform_small_loss_cutoff (c epsilon : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (he : 0 < epsilon) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 → ∀i : Fin 4,
        delta^(cutoff c i*epsilon/2) ≤ 1/errorConstant := by
  have H : ∀i : Fin 4,∃di : ℝ,0 < di ∧ di ≤ 1 ∧
      ∀delta : ℝ,0 < delta → delta ≤ di → delta^(cutoff c i*epsilon/2) ≤ 1/errorConstant := by
    intro i
    have ha := (cutoff_bounds hc hc1 i).1
    exact NativeQuarterScaleParameters.exists_small_power_cutoff
      (show 0<cutoff c i*epsilon/2 by positivity) (by norm_num [errorConstant])
  choose d hd _hd1 H using H
  let delta0 := min (1/8) (univ.inf' (univ_nonempty : (univ:Finset (Fin 4)).Nonempty) d)
  refine ⟨delta0,?_,min_le_left _ _,?_⟩
  · apply lt_min (by norm_num)
    exact (lt_inf'_iff _).mpr (fun i _ => hd i)
  · intro delta hdelta hsmall i
    exact H i delta hdelta ((hsmall.trans (min_le_right _ _)).trans (inf'_le d (mem_univ i)))

lemma absorb_small_loss {delta r a epsilon : ℝ}
    (hd : 0 < delta) (hr : 0 < r) (he : 0 < epsilon)
    (hrdelta : r ≤ delta^a) (hsmall : delta^(a*epsilon/2) ≤ 1/errorConstant) :
    errorConstant*r^(1/2-epsilon/2) ≤ r^(1/2-epsilon) := by
  have hrsmall : r^(epsilon/2) ≤ 1/errorConstant := by
    calc
      _ ≤ (delta^a)^(epsilon/2) := Real.rpow_le_rpow hr.le hrdelta (by positivity)
      _ = delta^(a*epsilon/2) := by rw [←Real.rpow_mul hd.le]; congr 1; ring
      _ ≤ _ := hsmall
  have hC : 0 < errorConstant := by norm_num [errorConstant]
  have hpaid : errorConstant*r^(epsilon/2) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hrsmall hC.le
    simpa only [mul_one_div_cancel hC.ne'] using hh
  have hsplit : r^(1/2-epsilon/2)=r^(epsilon/2)*r^(1/2-epsilon) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  calc
    _ = (errorConstant*r^(epsilon/2))*r^(1/2-epsilon) := by rw [hsplit]; ring
    _ ≤ 1*r^(1/2-epsilon) := mul_le_mul_of_nonneg_right hpaid (Real.rpow_nonneg hr.le _)
    _ = _ := one_mul _

/-- At the genuine middle grain, the normalized directional error has exponent
arbitrarily close to one in Delta. Every source/hierarchy dependency is explicit. -/
theorem actual_middle_error_small_loss {delta r q eta0 c tau epsilon : ℝ}
    (hd : 0 < delta) (hr : 0 < r) (hr1 : r ≤ 1)
    (he : 0 < epsilon) (heHalf : epsilon ≤ 1/2)
    (he0 : 0 ≤ eta0) (heSmall : eta0 ≤ epsilon)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcSmall : c ≤ epsilon/24) (i : Fin 4) (hi : i.val+1 ≤ 3)
    (hrdelta : r ≤ delta^(cutoff c i)) (htau : 0 ≤ tau) (g K stop : ℕ)
    (hK : 0 < K) (hs : 6 ≤ stop)
    (hTau : tau ≤ commonBudget eta0 c/(1000*(((2*K:ℕ):ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : 0 < q) (hq1 : q ≤ 1) (hqlow : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1)
    (hsmall : delta^(cutoff c i*epsilon/2) ≤ 1/errorConstant) :
    normalizedError (NativeRetainedQueryMenu.grainDepth (2*K) stop (middleIndex K)) (i.val+1) r q ≤
      ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^(1-2*epsilon) := by
  have htest := actual_test_radius_small_loss hd hr hr1 he he0 heSmall hc hc1 hcSmall i
    hrdelta htau g (2*K) hTau hgrid hqlow
  rw [grainDepth_middle K stop hK hs]
  have herror := (normalized_error_small_loss hr hq hq1 stop (i.val+1) hs hi hidentity htest).trans
    (absorb_small_loss hd hr he hrdelta hsmall)
  obtain ⟨hD,_hD1,_hsq,hlo,_hhi⟩ := middle_scale_bounds stop hs r hidentity
  have hrD : r ≤ ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^2 := by linarith only [hlo,hr]
  calc
    _ ≤ r^(1/2-epsilon) := herror
    _ ≤ (((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^2)^(1/2-epsilon) :=
      Real.rpow_le_rpow hr.le hrD (by linarith)
    _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul hD.le]; congr 1; ring

/-- Exact original incidence and parent readback for the small-loss bound. -/
theorem actual_middle_parent_direction_small_loss {n : ℕ} {D : FiniteScaleSource n}
    {eta a q r eta0 c tau epsilon : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hr : 0 < r) (hr1 : r ≤ 1)
    (he : 0 < epsilon) (heHalf : epsilon ≤ 1/2)
    (he0 : 0 ≤ eta0) (heSmall : eta0 ≤ epsilon)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcSmall : c ≤ epsilon/24) (rank : Fin 4) (hrank : rank.val+1 ≤ 3)
    (hrdelta : r ≤ D.thickness^(cutoff c rank)) (htau : 0 ≤ tau) (g K stop : ℕ)
    (hK : 0 < K) (hs : 6 ≤ stop)
    (hTau : tau ≤ commonBudget eta0 c/(1000*(((2*K:ℕ):ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : 0 < q) (hq1 : q ≤ 1) (hqlow : r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1)
    (hsmall : D.thickness^(cutoff c rank*epsilon/2) ≤ 1/errorConstant)
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin (rank.val+1) → (Fin n × Index)}
    {anchor : Index → Fin (rank.val+1) → Fin n}
    (H : IsNodeDirectionSystem D a (grainDepth (2*K) stop (middleIndex K)) E S q (rank.val+1) point tuple anchor)
    (P : Index → Submodule ℝ E4) (hP : ∀k∈S,Module.finrank ℝ (P k)=rank.val+1)
    (hnear : ∀z∈E,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ r)
    (k : Index) (hk : k∈S) (i j : Fin n) (hi : (i,k)∈E) (hj : (j,k)∈E)
    (hparent : parentLabel D a (2^(grainDepth (2*K) stop (middleIndex K))) i=
      parentLabel D a (2^(grainDepth (2*K) stop (middleIndex K))) j) :
    let m := grainDepth (2*K) stop (middleIndex K)
    let Q := spanOf (fun z : Fin n × Index => slopeVector D z.1)
      (List.ofFn (tuple (spatialLabel D (2^m) k)))
    Metric.infDist (((2^m:ℕ):ℝ) • (slopeVector D i-slopeVector D j)) (sliceSpace Q:Set E4) ≤
      ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^(1-2*epsilon) := by
  have herror := actual_middle_error_small_loss h.1.2.1 hr hr1 he heHalf he0 heSmall hc hc1 hcSmall rank hrank
    hrdelta htau g K stop hK hs hTau hgrid hq hq1 hqlow hidentity hsmall
  exact parent_direction_from_error h hq hr (by omega) H P hP hnear k hk i j hi hj hparent herror

end NativeSmallLossParentBudget
