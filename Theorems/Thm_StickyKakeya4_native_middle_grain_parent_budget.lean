import Theorems.Thm_StickyKakeya4_native_general_rank_scalar_budget
import Theorems.Thm_StickyKakeya4_native_parent_direction_difference
import Theorems.Thm_StickyKakeya4_native_span_coefficient_power

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace NativeMiddleGrainParentBudget
open Classical Finset StickyKakeya4 NativeRankExponentHierarchy NativeRetainedQueryMenu
open NativeSquaredGrainQueries NativeActualQueryRankConfiguration NativeCompatibleWeightedRetention
open NativeSeparatedSpanControl NativeSpanCoefficientPower NativeParentDirectionDifference
open NativeCompatibleNodeDirections NativeDirectionRankDichotomy NativeHorizontalGrainSlice
open NativeSpatialAngularGeometry NativeOriginalParentSelection NativeCommonCubicalMesh
open scoped BigOperators

/-- A fixed even grain count2K has a literal middle query. K is chosen before tau. -/
def middleIndex (K : ℕ) : Fin (2*K+1) := ⟨K,by omega⟩

def middleDepth (stop : ℕ) : ℕ := 6+(stop-6)/2

lemma grainDepth_middle (K stop : ℕ) (hK : 0 < K) (hs : 6 ≤ stop) :
    grainDepth (2*K) stop (middleIndex K)=middleDepth stop := by
  simp only [grainDepth,NativeFixedSizeScaleMenu.schedule,middleIndex,middleDepth,min_eq_left hs]
  congr 1
  rw [Nat.mul_comm 2 K]
  exact Nat.mul_div_mul_left (stop-6) 2 hK

lemma middle_depth_bounds (stop : ℕ) (hs : 6 ≤ stop) :
    6 ≤ middleDepth stop ∧ middleDepth stop ≤ stop ∧
      stop-1 ≤ phaseDepth (middleDepth stop) ∧ phaseDepth (middleDepth stop) ≤ stop := by
  dsimp [middleDepth,phaseDepth]
  omega

/-- Both installed queries use the original middle grain and its squared fine phase. -/
lemma middle_query_readback (K stop : ℕ) (hK : 0 < K) (hs : 6 ≤ stop) :
    pairedQueries (2*K) stop (Fin.castAdd (2*K+1) (middleIndex K))=
      (phaseDepth (middleDepth stop),middleDepth stop) ∧
    pairedQueries (2*K) stop (Fin.natAdd (2*K+1) (middleIndex K))=
      (phaseDepth (middleDepth stop),phaseDepth (middleDepth stop)) := by
  rw [pairedQueries_short,pairedQueries_vertex,grainDepth_middle K stop hK hs]
  exact ⟨rfl,rfl⟩

/-- Exact scale readback: the squared middle grain is within a factor two
of the original stopping physical scale3072r. -/
theorem middle_scale_bounds (stop : ℕ) (hs : 6 ≤ stop) (r : ℝ)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) :
    let Delta := (64:ℝ)/((2^(middleDepth stop):ℕ):ℝ)
    0 < Delta ∧ Delta ≤ 1 ∧
      (64:ℝ)/((2^(phaseDepth (middleDepth stop)):ℕ):ℝ)=Delta^2 ∧
      3072*r ≤ Delta^2 ∧ Delta^2 ≤ 6144*r := by
  intro Delta
  obtain ⟨hm6,_hms,hp1,hps⟩ := middle_depth_bounds stop hs
  have hN : (64:ℝ) ≤ ((2^(middleDepth stop):ℕ):ℝ) := by
    exact_mod_cast (show (64:ℕ)≤2^(middleDepth stop) by
      simpa only [show (2:ℕ)^6=64 by norm_num] using Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hm6)
  have hp : ((2^(phaseDepth (middleDepth stop)):ℕ):ℝ) ≤ ((2^stop:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) hps
  have hp' : ((2^stop:ℕ):ℝ) ≤ 2*((2^(phaseDepth (middleDepth stop)):ℕ):ℝ) := by
    have hh := Nat.pow_le_pow_right (by norm_num : 0<(2:ℕ)) (show stop≤phaseDepth (middleDepth stop)+1 by omega)
    rw [pow_succ] at hh
    exact_mod_cast (by simpa only [Nat.mul_comm] using hh : (2:ℕ)^stop≤2*2^(phaseDepth (middleDepth stop)))
  have hstop := stopping_physical_scale stop r hidentity
  have hsq := squared_scale_identity (middleDepth stop) hm6
  refine ⟨by dsimp [Delta]; positivity,(div_le_one (by positivity)).mpr hN,hsq,?_,?_⟩
  · rw [←hsq,←hstop]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
  · rw [←hsq]
    calc
      _ ≤ 2*((64:ℝ)/((2^stop:ℕ):ℝ)) := by
        rw [←mul_div_assoc]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith only [hp']
      _ = _ := by rw [hstop]; ring

lemma middle_scale_root_bound {r : ℝ} (hr : 0 < r) (stop : ℕ) (hs : 6 ≤ stop)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) :
    (64:ℝ)/((2^(middleDepth stop):ℕ):ℝ) ≤ 80*r^(1/2:ℝ) := by
  obtain ⟨hD,_hD1,_hsq,_hlo,hhi⟩ := middle_scale_bounds stop hs r hidentity
  have hroot : (r^(1/2:ℝ))^2=r := by
    rw [←Real.rpow_mul_natCast hr.le]
    norm_num
  have hroot0 := Real.rpow_nonneg hr.le (1/2:ℝ)
  nlinarith only [hhi,hroot,hroot0,hD,hr]

/-- The exact previously-proved normalized directional error. -/
def normalizedError (m ell : ℕ) (r q : ℝ) : ℝ :=
  6*((2^m:ℕ):ℝ)*r+24*(2*r+2/((2^m:ℕ):ℝ))*coefficientCost 2 q ell

lemma normalized_error_le_scale {r q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (m ell : ℕ) (hr : r ≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2)
    (hD1 : (64:ℝ)/((2^m:ℕ):ℝ) ≤ 1) :
    normalizedError m ell r q ≤ 456*((64:ℝ)/((2^m:ℕ):ℝ))*(4/q)^ell := by
  let N : ℝ := ((2^m:ℕ):ℝ)
  let Delta : ℝ := 64/N
  have hN : 0 < N := by dsimp [N]; positivity
  have hD : 0 < Delta := by dsimp [Delta]; positivity
  have hND : N*Delta=64 := by dsimp [Delta]; field_simp
  have hR : r ≤ Delta := by nlinarith only [hr,hD1,hD]
  have hsmall : 2/N ≤ Delta := div_le_div_of_nonneg_right (by norm_num : (2:ℝ)≤64) hN.le
  have hfirst : 6*N*r ≤ 384*Delta := by
    calc
      _ ≤ 6*N*Delta^2 := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 384*Delta := by calc
        _ = 6*(N*Delta)*Delta := by ring
        _ = _ := by rw [hND]; ring
  have hC := coefficientCost_le_power hq hq1 ell
  have hCn := coefficientCost_nonneg (by norm_num : (0:ℝ)≤2) hq ell
  have hK : 1 ≤ (4/q)^ell := one_le_pow₀ ((le_div_iff₀ hq).mpr (by linarith))
  have hsecond : 24*(2*r+2/N)*coefficientCost 2 q ell ≤ 72*Delta*(4/q)^ell := by
    calc
      _ ≤ 72*Delta*coefficientCost 2 q ell :=
        mul_le_mul_of_nonneg_right (by linarith only [hR,hsmall]) hCn
      _ ≤ _ := mul_le_mul_of_nonneg_left hC (by positivity)
  have hfirst' : 384*Delta ≤ 384*Delta*(4/q)^ell :=
    le_mul_of_one_le_right (by positivity) hK
  change 6*N*r+24*(2*r+2/N)*coefficientCost 2 q ell ≤ 456*Delta*(4/q)^ell
  nlinarith only [hfirst,hsecond,hfirst']

/-- The actual source grid and tau budget give a uniform test-radius power.
No plane-gap budget is assumed. -/
theorem actual_test_radius_lower {delta r q eta0 c tau : ℝ}
    (hd : 0 < delta) (hr : 0 < r) (hr1 : r ≤ 1)
    (he0 : 0 ≤ eta0) (heSmall : eta0 ≤ 1/1000)
    (hc : 0 < c) (hcSmall : c ≤ 1/64) (i : Fin 4)
    (hrdelta : r ≤ delta^(cutoff c i))
    (htau : 0 ≤ tau) (g J : ℕ)
    (hTau : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q) : r^(1/24:ℝ)/2 ≤ q := by
  have hc1 : c ≤ 1 := by linarith
  have ha := (cutoff_bounds hc hc1 i).1
  have hident := cutoff_mul_rankLoss eta0 c i
  have ht := NativeGeneralRankScalarBudget.tau_budget htau J
    (show tau ≤ cutoff c i*rankLoss eta0 c i/(1000*((J:ℝ)+1)) by rwa [hident])
  have hg := NativeRankFourScalarBudget.grid_inverse_le_tau htau g hgrid
  have he := rankLoss_le_initial he0 hc.le hc1 i
  have hgridDiv : (1/(g:ℝ))/cutoff c i ≤ 1/1000000 := by
    apply (div_le_iff₀ ha).mpr
    have hm := mul_le_mul_of_nonneg_left (he.trans heSmall) ha.le
    nlinarith only [ht,hg,hm]
  have hexp : 2*c+(1/(g:ℝ))/cutoff c i ≤ 1/24 := by linarith only [hcSmall,hgridDiv]
  have hdPower := delta_loss_lower hd hr.le ha (show (0:ℝ)≤1/(g:ℝ) by positivity) hrdelta
  have hq' := NativeRankFourScalarBudget.actual_test_lower hd hr g hq
  calc
    _ ≤ r^(2*c+(1/(g:ℝ))/cutoff c i)/2 :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hr hr1 hexp) (by norm_num)
    _ = (r^(2*c)*r^((1/(g:ℝ))/cutoff c i))/2 := by rw [Real.rpow_add hr]
    _ ≤ (r^(2*c)*delta^(1/(g:ℝ)))/2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdPower (Real.rpow_nonneg hr.le _)) (by norm_num)
    _ ≤ _ := hq'

lemma coefficient_power_bound {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hq1 : q ≤ 1)
    (ell : ℕ) (hell : ell ≤ 3) (hqlow : r^(1/24:ℝ)/2 ≤ q) :
    (4/q)^ell ≤ 512*r^(-(1/8:ℝ)) := by
  have hbase : 1 ≤ 4/q := (le_div_iff₀ hq).mpr (by linarith)
  have hpow : (4/q)^ell ≤ (4/q)^3 := pow_le_pow_right₀ hbase hell
  have hlow : 4/q ≤ 8/r^(1/24:ℝ) := by
    apply (div_le_div_iff₀ hq (Real.rpow_pos_of_pos hr _)).mpr
    linarith only [hqlow]
  have hcube := pow_le_pow_left₀ (by positivity : (0:ℝ)≤4/q) hlow 3
  have hcubepow : (r^(1/24:ℝ))^3=r^(1/8:ℝ) := by
    rw [←Real.rpow_mul_natCast hr.le]
    congr 1
    norm_num
  have heq : (8/r^(1/24:ℝ))^3=512*r^(-(1/8:ℝ)) := by
    rw [div_pow,hcubepow,Real.rpow_neg hr.le]
    norm_num
    ring
  exact hpow.trans (hcube.trans_eq heq)

/-- A fixed constant, independent of tau, g, rank and the native source. -/
def errorConstant : ℝ := 18677760

lemma normalized_error_power {r q : ℝ} (hr : 0 < r) (hq : 0 < q) (hq1 : q ≤ 1)
    (stop ell : ℕ) (hs : 6 ≤ stop) (hell : ell ≤ 3)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1) (hqlow : r^(1/24:ℝ)/2 ≤ q) :
    normalizedError (middleDepth stop) ell r q ≤ errorConstant*r^(3/8:ℝ) := by
  obtain ⟨_hD,hD1,_hsq,hlo,_hhi⟩ := middle_scale_bounds stop hs r hidentity
  have hrD : r ≤ ((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))^2 := by linarith only [hlo,hr]
  have herror := normalized_error_le_scale hq hq1 (middleDepth stop) ell hrD hD1
  have hroot := middle_scale_root_bound hr stop hs hidentity
  have hcoefficient := coefficient_power_bound hr hq hq1 ell hell hqlow
  calc
    _ ≤ 456*((64:ℝ)/((2^(middleDepth stop):ℕ):ℝ))*(4/q)^ell := herror
    _ ≤ (456*(80*r^(1/2:ℝ)))*(512*r^(-(1/8:ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hroot (by norm_num)) hcoefficient (by positivity) (by positivity)
    _ = errorConstant*(r^(1/2:ℝ)*r^(-(1/8:ℝ))) := by unfold errorConstant; ring
    _ = _ := by rw [←Real.rpow_add hr]; norm_num

/-- This simultaneous cutoff is fixed before D and works for any later g.
It may be intersected with the existing source and dimension-range cutoffs. -/
theorem exists_uniform_cutoff (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 → ∀i : Fin 4,
        delta^(cutoff c i/8) ≤ 1/errorConstant := by
  have H : ∀i : Fin 4,∃di : ℝ,0 < di ∧ di ≤ 1 ∧
      ∀delta : ℝ,0 < delta → delta ≤ di → delta^(cutoff c i/8) ≤ 1/errorConstant := by
    intro i
    have ha := (cutoff_bounds hc hc1 i).1
    exact NativeQuarterScaleParameters.exists_small_power_cutoff
      (show 0<cutoff c i/8 by positivity) (by norm_num [errorConstant])
  choose d hd _hd1 H using H
  let delta0 := min (1/8) (univ.inf' (univ_nonempty : (univ:Finset (Fin 4)).Nonempty) d)
  refine ⟨delta0,?_,min_le_left _ _,?_⟩
  · apply lt_min (by norm_num)
    exact (lt_inf'_iff _).mpr (fun i _ => hd i)
  · intro delta hdelta hsmall i
    exact H i delta hdelta ((hsmall.trans (min_le_right _ _)).trans (inf'_le d (mem_univ i)))

lemma absorb_error_constant {delta r a : ℝ} (hd : 0 < delta) (hr : 0 < r)
    (hrdelta : r ≤ delta^a) (hsmall : delta^(a/8) ≤ 1/errorConstant) :
    errorConstant*r^(3/8:ℝ) ≤ r^(1/4:ℝ) := by
  have hrsmall : r^(1/8:ℝ) ≤ 1/errorConstant := by
    calc
      _ ≤ (delta^a)^(1/8:ℝ) := Real.rpow_le_rpow hr.le hrdelta (by norm_num)
      _ = delta^(a/8) := by rw [←Real.rpow_mul hd.le]; congr 1; ring
      _ ≤ _ := hsmall
  have hC : 0 < errorConstant := by norm_num [errorConstant]
  have hpaid : errorConstant*r^(1/8:ℝ) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hrsmall hC.le
    simpa only [mul_one_div_cancel hC.ne'] using hh
  have hsplit : r^(3/8:ℝ)=r^(1/8:ℝ)*r^(1/4:ℝ) := by
    rw [←Real.rpow_add hr]
    congr 1
    norm_num
  calc
    _ = (errorConstant*r^(1/8:ℝ))*r^(1/4:ℝ) := by rw [hsplit]; ring
    _ ≤ 1*r^(1/4:ℝ) := mul_le_mul_of_nonneg_right hpaid (Real.rpow_nonneg hr.le _)
    _ = _ := one_mul _

/-- Actual source scalars at the literal middle grain give a positive
quarter-power horizontal error, without an assumed plane-gap budget. -/
theorem actual_middle_error {delta r q eta0 c tau : ℝ}
    (hd : 0 < delta) (hr : 0 < r) (hr1 : r ≤ 1)
    (he0 : 0 ≤ eta0) (heSmall : eta0 ≤ 1/1000)
    (hc : 0 < c) (hcSmall : c ≤ 1/64) (i : Fin 4) (hi : i.val+1 ≤ 3)
    (hrdelta : r ≤ delta^(cutoff c i)) (htau : 0 ≤ tau) (g K stop : ℕ)
    (hK : 0 < K) (hs : 6 ≤ stop)
    (hTau : tau ≤ commonBudget eta0 c/(1000*(((2*K:ℕ):ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : 0 < q) (hq1 : q ≤ 1) (hqlow : r^(2*c)/(2*delta^(-(1/(g:ℝ)))) ≤ q)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1)
    (hsmall : delta^(cutoff c i/8) ≤ 1/errorConstant) :
    normalizedError (grainDepth (2*K) stop (middleIndex K)) (i.val+1) r q ≤ r^(1/4:ℝ) := by
  have htest := actual_test_radius_lower hd hr hr1 he0 heSmall hc hcSmall i hrdelta htau g (2*K) hTau hgrid hqlow
  rw [grainDepth_middle K stop hK hs]
  exact (normalized_error_power hr hq hq1 stop (i.val+1) hs hi hidentity htest).trans
    (absorb_error_constant hd hr hrdelta hsmall)

/-- The already-proved source-facing directional-difference formula has
exactly the normalized error paid above. This wrapper preserves its times,
original incidences, native phase parent and chosen node tuple. -/
theorem parent_direction_from_error {n ell m : ℕ} {D : FiniteScaleSource n} {eta a q r epsilon : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hq : 0 < q) (hr : 0 < r) (hell : 0 < ell)
    {E : Finset (Fin n × Index)} {S : Finset Index}
    {point : Index → Index} {tuple : Index → Fin ell → (Fin n × Index)}
    {anchor : Index → Fin ell → Fin n}
    (H : IsNodeDirectionSystem D a m E S q ell point tuple anchor)
    (P : Index → Submodule ℝ E4) (hP : ∀k∈S,Module.finrank ℝ (P k)=ell)
    (hnear : ∀z∈E,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ r)
    (k : Index) (hk : k∈S) (i j : Fin n) (hi : (i,k)∈E) (hj : (j,k)∈E)
    (hparent : parentLabel D a (2^m) i=parentLabel D a (2^m) j)
    (herror : normalizedError m ell r q ≤ epsilon) :
    let Q := spanOf (fun z : Fin n × Index => slopeVector D z.1)
      (List.ofFn (tuple (spatialLabel D (2^m) k)))
    Metric.infDist (((2^m:ℕ):ℝ) • (slopeVector D i-slopeVector D j)) (sliceSpace Q:Set E4) ≤ epsilon := by
  exact (parent_normalized_horizontal_difference h hq hr hell H P hP hnear k hk i j hi hj
    (2^m) (by positivity) hparent).trans herror

/-- The literal source-facing quarter-power conclusion at the installed
middle grain. All normalized directions use the same original time a and
phase-parent factor2^m, with no plane-gap or normalized-error premise. -/
theorem actual_middle_parent_direction {n : ℕ} {D : FiniteScaleSource n}
    {eta a q r eta0 c tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hr : 0 < r) (hr1 : r ≤ 1)
    (he0 : 0 ≤ eta0) (heSmall : eta0 ≤ 1/1000)
    (hc : 0 < c) (hcSmall : c ≤ 1/64) (rank : Fin 4) (hrank : rank.val+1 ≤ 3)
    (hrdelta : r ≤ D.thickness^(cutoff c rank)) (htau : 0 ≤ tau) (g K stop : ℕ)
    (hK : 0 < K) (hs : 6 ≤ stop)
    (hTau : tau ≤ commonBudget eta0 c/(1000*(((2*K:ℕ):ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : 0 < q) (hq1 : q ≤ 1) (hqlow : r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1)
    (hsmall : D.thickness^(cutoff c rank/8) ≤ 1/errorConstant)
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
    Metric.infDist (((2^m:ℕ):ℝ) • (slopeVector D i-slopeVector D j)) (sliceSpace Q:Set E4) ≤ r^(1/4:ℝ) := by
  have herror := actual_middle_error h.1.2.1 hr hr1 he0 heSmall hc hcSmall rank hrank
    hrdelta htau g K stop hK hs hTau hgrid hq hq1 hqlow hidentity hsmall
  exact parent_direction_from_error h hq hr (by omega) H P hP hnear k hk i j hi hj hparent herror

end NativeMiddleGrainParentBudget
