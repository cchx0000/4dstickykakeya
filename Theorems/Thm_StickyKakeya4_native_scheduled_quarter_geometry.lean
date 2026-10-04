import Theorems.Thm_StickyKakeya4_native_scheduled_scale_selection
import Theorems.Thm_StickyKakeya4_native_original_cutoff_selection
import Theorems.Thm_StickyKakeya4_original_angular_exponent_range
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeScheduledQuarterGeometry
open NativeScheduledScaleSelection NativeQuarterScaleParameters NativeDyadicMeshSelection
/-- The original scheduled macro scale and the source angular error determine
 the actual working scale; all normalization losses are retained. -/
theorem scheduled_quarter_bounds {delta eta C0 q : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta)
    (hC : 1 ≤ C0) (hCM : C0 ≤ delta^(-eta))
    (hqlo : delta^(1/4:ℝ) ≤ q) (hqhi : q ≤ delta^(-eta)*delta^(1/4:ℝ))
    (hsmall : delta^((1/4:ℝ)-2*eta) ≤ (1/64:ℝ)) :
    let M := delta^(-eta)
    let rho := q+C0*delta
    let S0 := 4*C0*M
    1 ≤ M ∧ delta ≤ q ∧ 0 < rho ∧ rho ≤ 1 ∧ delta ≤ rho^2 ∧
      0 < rho/S0 ∧ rho/S0 ≤ delta^(1/4:ℝ) ∧ M*q ≤ (1/8:ℝ) := by
  dsimp only
  let M := delta^(-eta)
  let b := delta^(1/4:ℝ)
  have hM : 1 ≤ M := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr heta)
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hb : 0 < b := Real.rpow_pos_of_pos hd _
  have hdb : delta ≤ b := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by norm_num : (1/4:ℝ)≤1))
  have hb1 : b ≤ 1 := Real.rpow_le_one hd.le hd1 (by norm_num)
  have hsplit : M^2*b=delta^((1/4:ℝ)-2*eta) := by
    dsimp only [M,b]
    rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_add hd]
    congr 1
    ring
  have hM2b : M^2*b ≤ (1/64:ℝ) := by simpa only [hsplit] using hsmall
  have hMb : M*b ≤ (1/64:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hM (mul_nonneg hM0.le hb.le)
    nlinarith only [hh,hM2b]
  have hrlo : b ≤ q+C0*delta := by
    have hnon : 0 ≤ C0*delta := mul_nonneg (by linarith) hd.le
    linarith only [hqlo,hnon]
  have hrhi : q+C0*delta ≤ 2*M*b := by
    have hh := mul_le_mul hCM hdb hd.le hM0.le
    linarith only [hqhi,hh]
  have hC0 : 0 < C0 := lt_of_lt_of_le (by norm_num) hC
  have hS : 0 < 4*C0*M := by positivity
  have hscale : (q+C0*delta)/(4*C0*M) ≤ b := by
    apply (div_le_iff₀ hS).mpr
    have hh := mul_le_mul_of_nonneg_right hC (mul_nonneg hM0.le hb.le)
    nlinarith only [hrhi,hh,hM0,hb]
  have hdsq : delta ≤ b^2 := by
    have heq : b^2=delta^(1/2:ℝ) := by
      dsimp only [b]
      rw [← Real.rpow_mul_natCast hd.le]
      norm_num
    rw [heq]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by norm_num : (1/2:ℝ)≤1))
  have hMq : M*q ≤ (1/8:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hqhi hM0.le
    nlinarith only [hh,hM2b]
  exact ⟨hM,hdb.trans hqlo,hb.trans_le hrlo,by linarith only [hrhi,hMb],
    hdsq.trans (sq_le_sq₀ hb.le (hb.le.trans hrlo) |>.mpr hrlo),
    div_pos (hb.trans_le hrlo) hS,hscale,hMq⟩
/-- The same actual working scale admits a balanced projection mesh in the
 required original-delta power range, with the constant 64 paid explicitly. -/
theorem scheduled_quarter_balanced_bounds {delta eta C0 q rhoP : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta)
    (hC : 1 ≤ C0) (hCM : C0 ≤ delta^(-eta))
    (hqlo : delta^(1/4:ℝ) ≤ q) (hqhi : q ≤ delta^(-eta)*delta^(1/4:ℝ))
    (hsmall : delta^((1/4:ℝ)-2*eta) ≤ (1/64:ℝ))
    (hhalf : ((q+C0*delta)/(4*C0*delta^(-eta)))/2 ≤ rhoP)
    (hupper : rhoP ≤ (q+C0*delta)/(4*C0*delta^(-eta))) :
    delta^(1/2:ℝ) ≤ rhoP/8 ∧ rhoP/8 ≤ delta^(1/4:ℝ) := by
  obtain ⟨hM,_,hr,_,_,_,ht,_⟩ := scheduled_quarter_bounds hd hd1 heta hC hCM hqlo hqhi hsmall
  let M := delta^(-eta)
  let b := delta^(1/4:ℝ)
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hb : 0 < b := Real.rpow_pos_of_pos hd _
  have hC0 : 0 < C0 := lt_of_lt_of_le (by norm_num) hC
  have hS : 0 < 4*C0*M := by positivity
  have hden : 4*C0*M ≤ 4*M^2 := by nlinarith only [mul_le_mul_of_nonneg_right hCM hM0.le]
  have hlow : b/(4*M^2) ≤ (q+C0*delta)/(4*C0*M) := by
    calc
      _ ≤ b/(4*C0*M) := div_le_div_of_nonneg_left hb.le hS hden
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith only [hqlo,mul_pos hC0 hd]) hS.le
  have hpower : b/M^2=delta^((1/4:ℝ)+2*eta) := by
    dsimp only [b,M]
    rw [← Real.rpow_mul_natCast hd.le,← Real.rpow_sub hd]
    congr 1
    ring
  have hsplit : delta^(1/2:ℝ)=delta^((1/4:ℝ)-2*eta)*delta^((1/4:ℝ)+2*eta) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right hsmall
    (Real.rpow_pos_of_pos hd ((1/4:ℝ)+2*eta)).le
  rw [← hsplit,← hpower] at hh
  constructor
  · have hid : (1/64:ℝ)*(b/M^2)=(b/(4*M^2))/16 := by ring
    rw [hid] at hh
    linarith only [hh,hlow,hhalf]
  · linarith only [hupper,ht,hb]
/-- The analytic cutoff is fixed before any original source data. The macro
 scale is literally on the source schedule, and the balanced mesh is dyadic. -/
theorem exists_scheduled_quarter_dyadic_cutoff {eta : ℝ}
    (heta : 0 < eta) (hgap : eta < (1/8:ℝ)) (n0 : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 < 1 ∧ ∀ delta C0 : ℝ,
      0 < delta → delta ≤ delta0 → 1 ≤ C0 → C0 ≤ delta^(-eta) →
      ∃ j n : ℕ, ∃ rhoP : ℝ,
        let q := scheduledScale delta eta j
        let rho := q+C0*delta
        let S0 := 4*C0*delta^(-eta)
        delta ≤ q ∧ q ≤ 1 ∧ delta^(1/4:ℝ) ≤ q ∧
        q ≤ delta^(-eta)*delta^(1/4:ℝ) ∧ 0 < rho ∧ rho ≤ 1 ∧ delta ≤ rho^2 ∧
        n0 ≤ n ∧ 0 < rhoP ∧ rhoP/8=((2:ℝ)^n)⁻¹ ∧
        (rho/S0)/2 ≤ rhoP ∧ rhoP < rho/S0 ∧
        delta^(1/2:ℝ) ≤ rhoP/8 ∧ rhoP/8 ≤ delta^(1/4:ℝ) ∧
        delta^(-eta)*q ≤ (1/8:ℝ) := by
  obtain ⟨d1,hd1,_,hc1⟩ := exists_small_power_cutoff
    (show 0 < (1/4:ℝ)-2*eta by linarith) (by norm_num : (0:ℝ)<1/64)
  obtain ⟨d2,hd2,_,hc2⟩ := NativeOriginalCutoffSelection.exists_native_mesh_cutoff
    (by norm_num : (0:ℝ)<1/4) n0
  refine ⟨min (min d1 d2) (1/2),lt_min (lt_min hd1 hd2) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
  intro delta C0 hd hd0 hC hCM
  have hdlt : delta < 1 := lt_of_le_of_lt (hd0.trans (min_le_right _ _)) (by norm_num)
  have hdb : delta ≤ delta^(1/4:ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge hd hdlt.le (by norm_num : (1/4:ℝ)≤1))
  obtain ⟨j,hqδ,hq1,hqlo,hqhi⟩ := exists_scheduled_scale_above hd hdlt heta hdb
    (Real.rpow_le_one hd.le hdlt.le (by norm_num : (0:ℝ)≤1/4))
  have hsmall := hc1 delta hd (hd0.trans ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨_,_,hr,hr1,hdr,ht,htb,hMq⟩ :=
    scheduled_quarter_bounds hd hdlt.le heta.le hC hCM hqlo hqhi hsmall
  have hbt : delta^(1/4:ℝ) ≤ 1 := Real.rpow_le_one hd.le hdlt.le (by norm_num)
  obtain ⟨n,rhoP,hn,hrp,heq,hlo,hhi⟩ := exists_balanced_nearby_dyadic_mesh ht
    (htb.trans hbt) n0 (hc2 delta _ hd
      (hd0.trans ((min_le_left _ _).trans (min_le_right _ _))) htb)
  obtain ⟨hmeshlo,hmeshhi⟩ := scheduled_quarter_balanced_bounds hd hdlt.le heta.le hC hCM
    hqlo hqhi hsmall hlo hhi.le
  exact ⟨j,n,rhoP,hqδ,hq1,hqlo,hqhi,hr,hr1,hdr,hn,hrp,heq,hlo,hhi,hmeshlo,hmeshhi,hMq⟩
/-- The exponent range follows from the literal original angular AD law and
 one-dimensional packing at the chosen scheduled macro scale. -/
theorem scheduled_angular_exponent_lt_two (Phi : Finset ℝ) (hPhi : Phi.Nonempty)
    {delta eta C0 q kappa : ℝ} (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta)
    (hC : 1 ≤ C0) (hCM : C0 ≤ delta^(-eta))
    (hqlo : delta^(1/4:ℝ) ≤ q) (hqhi : q ≤ delta^(-eta)*delta^(1/4:ℝ)) (hq1 : q ≤ 1)
    (hsmall : delta^((1/4:ℝ)-2*eta) ≤ (1/64:ℝ))
    (hsep : FiniteVoronoiPopulation.Separated Phi q)
    (hbox : ∀ phi ∈ Phi, |phi| ≤ 1)
    (hAD : FiniteVoronoiRealADCoarsening.ADBounds Phi q (delta^(-eta)) kappa) : kappa < 2 := by
  obtain ⟨_,hdq,_,_,_,_,_,hpack⟩ := scheduled_quarter_bounds hd hd1 heta hC hCM hqlo hqhi hsmall
  exact OriginalAngularExponentRange.original_angular_exponent_lt_two Phi hPhi
    (hd.trans_le hdq) hq1 (Real.rpow_pos_of_pos hd _) hsep hbox hAD hpack
end NativeScheduledQuarterGeometry
