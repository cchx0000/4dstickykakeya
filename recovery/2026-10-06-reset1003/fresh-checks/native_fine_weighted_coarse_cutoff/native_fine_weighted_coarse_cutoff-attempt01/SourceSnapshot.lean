import Theorems.Thm_StickyKakeya4_native_fine_weighted_coarse_core
import Theorems.Thm_StickyKakeya4_native_effective_output_threshold

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeFineWeightedCoarseCutoff
open NativeFineWeightedCoarseCore NativeOriginalPrunedMass NativeOriginalLogBudget
open NativeDyadicPruningCutoff NativeCoarsePowerWindow NativeCoarseRelativeCW

/-- One original-thickness cutoff, chosen before the source, pays all fixed
constants and the logarithmic pruning charge uniformly for z ≥ zMin.
The pruning payment uses 3*zMin; it does not choose a cutoff after z or b. -/
theorem exists_uniform_cutoff {zMin : ℝ} (hzMin : 0 < zMin) :
    ∃r0 : ℝ,0 < r0 ∧ r0 ≤ 1/8 ∧
      ∀ (r z eta : ℝ) (level b : ℕ),
        0 < r → r ≤ r0 → r=(2:ℝ)⁻¹^level → b ≤ level → zMin ≤ z → eta ≤ zMin →
        colorCost*r^z ≤ 1 ∧
        2*pruneCost*((b:ℝ)+1)*r^(3*z) ≤ 1 ∧
        1088*fineCapacity*r^z ≤ 1 ∧
        10077696*r^(8*z) ≤ 1 ∧
        densityCost*r^z ≤ 1 ∧ cwCost*r^(2*z-eta) ≤ 1 := by
  have hcol := colorCost_pos
  have hpr := pruneCost_pos
  have hfine := fineCapacity_pos
  have hden := densityCost_pos
  have hcw := cwCost_pos
  let C : ℝ := colorCost+1088*fineCapacity+10077696+densityCost+cwCost
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨dc,hdc,_hdc1,hconst⟩ := exists_positive_rpow_absorption_threshold
    hzMin hC (by norm_num : (0:ℝ)<1)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨dl,hdl,_hdl1,hlog⟩ := exists_logarithmic_budget_cutoff
    (show 0 < 3*zMin by positivity)
    (show 0 ≤ 2*pruneCost by positivity)
    (show 0 ≤ (2*pruneCost)/Real.log 2 by positivity)
  refine ⟨min (1/8:ℝ) (min dc dl),lt_min (by norm_num) (lt_min hdc hdl),min_le_left _ _,?_⟩
  intro r z eta level b hr hsmall hdy hb hz heta
  have hr1 : r ≤ 1 := (hsmall.trans (min_le_left _ _)).trans (by norm_num)
  have hrest := hsmall.trans (min_le_right _ _)
  have hc := hconst r hr (hrest.trans (min_le_left _ _))
  have hpay (c t : ℝ) (hcC : c ≤ C) (ht : zMin ≤ t) : c*r^t ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right hcC (Real.rpow_pos_of_pos hr t).le).trans
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr1 ht) hC).trans hc)
  have hdepth : 2*pruneCost*((level:ℝ)+1) ≤ r^(-(3*zMin)) := by
    have hh := hlog r hr (hrest.trans (min_le_right _ _))
    rw [dyadic_depth_log level hdy]
    convert hh using 1
    ring
  have hlogpaid : 2*pruneCost*((level:ℝ)+1)*r^(3*zMin) ≤ 1 := by
    calc
      _ ≤ r^(-(3*zMin))*r^(3*zMin) :=
        mul_le_mul_of_nonneg_right hdepth (Real.rpow_pos_of_pos hr _).le
      _ = 1 := by rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
  refine ⟨hpay colorCost z (by dsimp [C]; linarith) hz,?_,
    hpay (1088*fineCapacity) z (by dsimp [C]; linarith) hz,
    hpay 10077696 (8*z) (by dsimp [C]; linarith) (by linarith),
    hpay densityCost z (by dsimp [C]; linarith) hz,
    hpay cwCost (2*z-eta) (by dsimp [C]; linarith) (by linarith)⟩
  calc
    2*pruneCost*((b:ℝ)+1)*r^(3*z) ≤ 2*pruneCost*((level:ℝ)+1)*r^(3*zMin) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (show (b:ℝ)+1 ≤ (level:ℝ)+1 by exact_mod_cast Nat.add_le_add_right hb 1)
          (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
      · exact (Real.rpow_pos_of_pos hr _).le
      · positivity
    _ ≤ 1 := hlogpaid

/-- The effective exponent reads back exactly at the output scale, and its
native power-window inequality follows whenever that output is at most one. -/
theorem effective_power {r d e : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hd : 0 < d) (hd1 : d ≤ 1) (he : 0 ≤ e) :
    r^(NativeEffectiveOutputThreshold.exponent r d e)=d^(e/16) ∧
    d^e ≤ r^(8*NativeEffectiveOutputThreshold.exponent r d e) := by
  constructor
  · simpa only [one_mul] using NativeEffectiveOutputThreshold.power_readback hr hr1 hd e 1
  · rw [NativeEffectiveOutputThreshold.power_readback hr hr1 hd e 8]
    exact Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)

/-- Fixed window and accuracy parameters choose one cutoff before D. The
effective exponent may then depend on the actual output without introducing
a source-dependent constant or changing the order of parameter choices. -/
theorem exists_effective_cutoff {window e : ℝ} (hw : 0 < window) (he : 0 < e) :
    ∃r0 : ℝ,0 < r0 ∧ r0 ≤ 1/8 ∧
      ∀ (r d eta : ℝ) (level b : ℕ),
        0 < r → r ≤ r0 → r=(2:ℝ)⁻¹^level → b ≤ level →
        0 < d → d ≤ r^window → eta ≤ window*e/16 →
        let z := NativeEffectiveOutputThreshold.exponent r d e
        window*e/16 ≤ z ∧ r^z=d^(e/16) ∧ d^e ≤ r^(8*z) ∧
        colorCost*r^z ≤ 1 ∧
        2*pruneCost*((b:ℝ)+1)*r^(3*z) ≤ 1 ∧
        1088*fineCapacity*r^z ≤ 1 ∧
        10077696*r^(8*z) ≤ 1 ∧
        densityCost*r^z ≤ 1 ∧ cwCost*r^(2*z-eta) ≤ 1 := by
  obtain ⟨r0,hr0,hr08,H⟩ := exists_uniform_cutoff (show 0 < window*e/16 by positivity)
  refine ⟨r0,hr0,hr08,?_⟩
  intro r d eta level b hr hsmall hdy hb hd hwindow heta
  have hr1 : r < 1 := lt_of_le_of_lt (hsmall.trans hr08) (by norm_num)
  have hd1 : d ≤ 1 := hwindow.trans (Real.rpow_le_one hr.le hr1.le hw.le)
  have hz := NativeEffectiveOutputThreshold.fixed_lower_bound hr hr1 hd he.le hwindow
  have hread := effective_power hr hr1 hd hd1 he.le
  exact ⟨hz,hread.1,hread.2,H r _ eta level b hr hsmall hdy hb hz heta⟩

/-- When the final relative output sigma exceeds the absolute intermediate
mesh d, both exponents are read at sigma. No conversion from a fixed power
of d to a power of sigma, and hence no division by a window exponent, occurs. -/
theorem two_output_power_readback {r d sigma E : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hd : 0 < d) (hd1 : d < 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hds : d ≤ sigma) (hE : 0 ≤ E) :
    let z1 := NativeEffectiveOutputThreshold.exponent r sigma (E/256)
    let etaA := NativeEffectiveOutputThreshold.exponent d sigma (E/16)
    let z2 := NativeEffectiveOutputThreshold.exponent d sigma E
    etaA=z2/16 ∧ 0 ≤ etaA ∧ etaA ≤ E/256 ∧
      d^etaA=sigma^(E/256) ∧ r^(8*z1)=sigma^(E/512) ∧
      r^(5*z1)=sigma^(5*E/4096) ∧ d^z2=sigma^(E/16) ∧
      d^(2*z2-etaA)=sigma^(31*E/256) ∧
      d^etaA ≤ r^(8*z1) ∧ d^z2 ≤ r^(5*z1) := by
  intro z1 etaA z2
  have hratio : etaA=z2/16 := by
    dsimp [etaA,z2,NativeEffectiveOutputThreshold.exponent]
    ring
  have heta0 : 0 ≤ etaA := by
    have hh := NativeEffectiveOutputThreshold.fixed_lower_bound (window:=0)
      hd hd1 hs (show 0 ≤ E/16 by positivity) (by simpa only [Real.rpow_zero] using hs1)
    simpa only [zero_mul,zero_div] using hh
  have hetaUpper : etaA ≤ E/256 := by
    have hh := NativeEffectiveOutputThreshold.fixed_upper_bound hd hd1
      (show 0 ≤ E/16 by positivity) hds
    convert hh using 1
    ring
  have hA : d^etaA=sigma^(E/256) := by
    have hh := NativeEffectiveOutputThreshold.power_readback hd hd1 hs (E/16) 1
    simpa only [one_mul,show E/16/16=E/256 by ring] using hh
  have h8 : r^(8*z1)=sigma^(E/512) := by
    have hh := NativeEffectiveOutputThreshold.power_readback hr hr1 hs (E/256) 8
    simpa only [show 8*(E/256)/16=E/512 by ring] using hh
  have h5 : r^(5*z1)=sigma^(5*E/4096) := by
    have hh := NativeEffectiveOutputThreshold.power_readback hr hr1 hs (E/256) 5
    simpa only [show 5*(E/256)/16=5*E/4096 by ring] using hh
  have h2 : d^z2=sigma^(E/16) := by
    simpa only [one_mul] using NativeEffectiveOutputThreshold.power_readback hd hd1 hs E 1
  have hCW : d^(2*z2-etaA)=sigma^(31*E/256) := by
    rw [hratio,show 2*z2-z2/16=(31/16)*z2 by ring]
    have hh := NativeEffectiveOutputThreshold.power_readback hd hd1 hs E (31/16)
    simpa only [show (31/16)*E/16=31*E/256 by ring] using hh
  refine ⟨hratio,heta0,hetaUpper,hA,h8,h5,h2,hCW,?_,?_⟩
  · rw [hA,h8]
    exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  · rw [h2,h5]
    exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)

/-- Fixed lower window bounds still determine all pre-source cutoffs for
the two varying exponents. Neither intermediate etaA nor z1 is fixed before
the two actual output scales; only these positive lower bounds are fixed. -/
theorem two_output_lower_bounds {r d sigma E u v : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hd : 0 < d) (hd1 : d < 1)
    (hs : 0 < sigma) (hE : 0 ≤ E) (hu : sigma ≤ r^u) (hv : sigma ≤ d^v) :
    u*E/4096 ≤ NativeEffectiveOutputThreshold.exponent r sigma (E/256) ∧
      v*E/16 ≤ NativeEffectiveOutputThreshold.exponent d sigma E := by
  constructor
  · have hh := NativeEffectiveOutputThreshold.fixed_lower_bound hr hr1 hs
      (show 0 ≤ E/256 by positivity) hu
    convert hh using 1
    ring
  · exact NativeEffectiveOutputThreshold.fixed_lower_bound hd hd1 hs hE hv

/-- Explicit ordered-scale form of the two-output parameters. The actual
definition of exponent contains the factor 1/16: z1 therefore uses E/256,
whereas etaA uses E/16. The same positive window controls both base scales. -/
theorem ordered_two_output_parameters {r d sigma E window : ℝ}
    (hr : 0 < r) (hrd : r ≤ d) (hds : d ≤ sigma) (hs1 : sigma < 1)
    (hw : 0 < window) (hE : 0 < E) (hwindow : sigma ≤ r^window) :
    let z1 := NativeEffectiveOutputThreshold.exponent r sigma (E/256)
    let etaA := NativeEffectiveOutputThreshold.exponent d sigma (E/16)
    let z2 := NativeEffectiveOutputThreshold.exponent d sigma E
    sigma ≤ d^window ∧ window*E/4096 ≤ z1 ∧
      0 < etaA ∧ etaA ≤ E/256 ∧ window*E/16 ≤ z2 ∧ etaA=z2/16 ∧
      d^etaA=sigma^(E/256) ∧ r^(8*z1)=sigma^(E/512) ∧
      r^(5*z1)=sigma^(5*E/4096) ∧ d^z2=sigma^(E/16) ∧
      d^etaA ≤ r^(8*z1) ∧ d^z2 ≤ r^(5*z1) := by
  intro z1 etaA z2
  have hd : 0 < d := hr.trans_le hrd
  have hs : 0 < sigma := hd.trans_le hds
  have hd1 : d < 1 := hds.trans_lt hs1
  have hr1 : r < 1 := hrd.trans_lt hd1
  have hwindowD : sigma ≤ d^window :=
    hwindow.trans (Real.rpow_le_rpow hr.le hrd hw.le)
  have hlower := two_output_lower_bounds hr hr1 hd hd1 hs hE.le hwindow hwindowD
  have hetaLower : window*E/256 ≤ etaA := by
    have hh := NativeEffectiveOutputThreshold.fixed_lower_bound hd hd1 hs
      (show 0 ≤ E/16 by positivity) hwindowD
    convert hh using 1
    ring
  obtain ⟨hratio,_heta0,hetaUpper,hA,h8,h5,h2,_hCW,hpower,hmass⟩ :=
    two_output_power_readback hr hr1 hd hd1 hs hs1.le hds hE.le
  exact ⟨hwindowD,hlower.1,(show 0 < window*E/256 by positivity).trans_le hetaLower,
    hetaUpper,hlower.2,hratio,hA,h8,h5,h2,hpower,hmass⟩

/-- Pull every intermediate-mesh and final-relative-output cutoff back to
one reference cutoff before the source. The supplied positive d0 and sigma0
are quantified before r,d,sigma. Thus d ≤ sigma ≤ r^window enforces both
cutoffs uniformly, while the same pre-source cutoff pays the fine-weight
ledger at z1Min=window*E/4096. -/
theorem exists_two_output_cutoff {window E : ℝ} (hw : 0 < window) (hE : 0 < E)
    (d0 sigma0 : ℝ) (hd0 : 0 < d0) (hsigma0 : 0 < sigma0) :
    ∃r0 : ℝ,0 < r0 ∧ r0 ≤ 1/8 ∧
      ∀ (r d sigma eta : ℝ) (level b : ℕ),
        0 < r → r ≤ r0 → r=(2:ℝ)⁻¹^level → b ≤ level →
        r ≤ d → d ≤ sigma → sigma ≤ r^window → eta ≤ window*E/4096 →
        d ≤ d0 ∧ sigma ≤ sigma0 ∧ sigma < 1 ∧
        let z1 := NativeEffectiveOutputThreshold.exponent r sigma (E/256)
        colorCost*r^z1 ≤ 1 ∧
        2*pruneCost*((b:ℝ)+1)*r^(3*z1) ≤ 1 ∧
        1088*fineCapacity*r^z1 ≤ 1 ∧
        10077696*r^(8*z1) ≤ 1 ∧
        densityCost*r^z1 ≤ 1 ∧ cwCost*r^(2*z1-eta) ≤ 1 := by
  obtain ⟨dc,hdc,hdc8,Hcore⟩ := exists_uniform_cutoff (show 0 < window*E/4096 by positivity)
  obtain ⟨dp,hdp,_hdp1,Hpull⟩ := NativeQuarterScaleParameters.exists_small_power_cutoff
    hw (lt_min hd0 hsigma0)
  refine ⟨min dc dp,lt_min hdc hdp,(min_le_left _ _).trans hdc8,?_⟩
  intro r d sigma eta level b hr hsmall hdy hb hrd hds hwindow heta
  have hcore := hsmall.trans (min_le_left _ _)
  have hr1 : r < 1 := lt_of_le_of_lt (hcore.trans hdc8) (by norm_num)
  have hbound : sigma ≤ min d0 sigma0 :=
    hwindow.trans (Hpull r hr (hsmall.trans (min_le_right _ _)))
  have hs : 0 < sigma := hr.trans_le (hrd.trans hds)
  have hz : window*E/4096 ≤ NativeEffectiveOutputThreshold.exponent r sigma (E/256) := by
    have hh := NativeEffectiveOutputThreshold.fixed_lower_bound hr hr1 hs
      (show 0 ≤ E/256 by positivity) hwindow
    convert hh using 1
    ring
  exact ⟨(hds.trans hbound).trans (min_le_left _ _),
    hbound.trans (min_le_right _ _),hwindow.trans_lt (Real.rpow_lt_one hr.le hr1 hw),
    Hcore r _ eta level b hr hcore hdy hb hz heta⟩

end NativeFineWeightedCoarseCutoff
