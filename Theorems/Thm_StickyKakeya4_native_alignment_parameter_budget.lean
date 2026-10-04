import Theorems.Thm_StickyKakeya4_native_alignment_scale_separation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Filter
namespace NativeAlignmentParameterBudget
open CoverProfileStopping
noncomputable section

lemma exists_nat_budget {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ n : ℕ, 0 < n ∧ b ≤ a*(n:ℝ) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 0 (b/a))
  have hn0 : 0 < (n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hb : b/a < (n:ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  exact ⟨n,Nat.cast_pos.mp hn0,by simpa only [mul_comm] using ((div_lt_iff₀ ha).mp hb).le⟩

structure Choice (zeta : ℝ) where
  m : ℕ
  H : ℕ
  L1 : ℕ
  L2 : ℕ
  epsilon : ℝ
  eta : ℝ
  m_pos : 0 < m
  H_pos : 0 < H
  L1_pos : 0 < L1
  L2_pos : 0 < L2
  epsilon_pos : 0 < epsilon
  epsilon_half : epsilon ≤ 1/2
  eta_pos : 0 < eta
  eta_one : eta ≤ 1
  profile_small : 3*(m:ℝ)*epsilon+1/(m:ℝ)+2/(H:ℝ) ≤ zeta/4
  residual_small : 18*eta+24/(L1:ℝ)+6/(L2:ℝ) ≤
    (separationExponent epsilon/(m:ℝ))*zeta/4

/-- Parameters are chosen in the noncircular order m,H; epsilon; q; L1,L2;
 eta. All later logarithmic losses are absorbed after these choices. -/
theorem exists_choice {zeta : ℝ} (hzeta : 0 < zeta) : Nonempty (Choice zeta) := by
  obtain ⟨m,hm,hmB⟩ := exists_nat_budget hzeta 12
  obtain ⟨H,hH,hHB⟩ := exists_nat_budget hzeta 24
  have hmR : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hHR : 0 < (H:ℝ) := Nat.cast_pos.mpr hH
  let epsilon := min (1/4:ℝ) (zeta/(36*(m:ℝ)))
  have he : 0 < epsilon := lt_min (by norm_num) (by positivity)
  have heh : epsilon ≤ 1/2 := (min_le_left _ _).trans (by norm_num)
  have hep : 3*(m:ℝ)*epsilon ≤ zeta/12 := by
    have h := (le_div_iff₀ (by positivity : 0 < 36*(m:ℝ))).mp (min_le_right (1/4:ℝ) (zeta/(36*(m:ℝ))))
    change epsilon*(36*(m:ℝ)) ≤ zeta at h
    nlinarith
  have hmone : 1/(m:ℝ) ≤ zeta/12 := (div_le_iff₀ hmR).mpr (by nlinarith)
  have hHtwo : 2/(H:ℝ) ≤ zeta/12 := (div_le_iff₀ hHR).mpr (by nlinarith)
  let q := separationExponent epsilon/(m:ℝ)
  have hq : 0 < q := div_pos (separationExponent_pos epsilon he) hmR
  obtain ⟨L1,hL1,hL1B⟩ := exists_nat_budget (mul_pos hq hzeta) 288
  obtain ⟨L2,hL2,hL2B⟩ := exists_nat_budget (mul_pos hq hzeta) 72
  have hL1R : 0 < (L1:ℝ) := Nat.cast_pos.mpr hL1
  have hL2R : 0 < (L2:ℝ) := Nat.cast_pos.mpr hL2
  have hL1small : 24/(L1:ℝ) ≤ q*zeta/12 := (div_le_iff₀ hL1R).mpr (by nlinarith)
  have hL2small : 6/(L2:ℝ) ≤ q*zeta/12 := (div_le_iff₀ hL2R).mpr (by nlinarith)
  let eta := min (1/2:ℝ) (q*zeta/216)
  have heta : 0 < eta := lt_min (by norm_num) (by positivity)
  have heta1 : eta ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hetasmall : 18*eta ≤ q*zeta/12 := by
    have h : eta ≤ q*zeta/216 := min_le_right _ _
    nlinarith
  exact ⟨{
    m := m
    H := H
    L1 := L1
    L2 := L2
    epsilon := epsilon
    eta := eta
    m_pos := hm
    H_pos := hH
    L1_pos := hL1
    L2_pos := hL2
    epsilon_pos := he
    epsilon_half := heh
    eta_pos := heta
    eta_one := heta1
    profile_small := by nlinarith
    residual_small := by
      change 18*eta+24/(L1:ℝ)+6/(L2:ℝ) ≤ q*zeta/4
      nlinarith }⟩


private theorem polynomial_absorption (C : ℝ) (a : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → C*((n:ℝ)+5)^a ≤ (2:ℝ)^(e*(n:ℝ)) := by
  let r := Real.log 2*e
  have hr : 0 < r := mul_pos (Real.log_pos (by norm_num)) he
  have ht : Tendsto (fun n : ℕ => Real.exp (r*((n:ℝ)+5))/((n:ℝ)+5)^(a:ℝ)) atTop atTop :=
    (tendsto_exp_mul_div_rpow_atTop (a:ℝ) r hr).comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  obtain ⟨n0,hn0⟩ := Filter.eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (C*Real.exp (r*5))))
  refine ⟨n0,fun n hn => ?_⟩
  have hp : 0 < (n:ℝ)+5 := by positivity
  have hb := (le_div_iff₀ (Real.rpow_pos_of_pos hp _)).mp (hn0 n hn)
  rw [Real.rpow_natCast,mul_add,Real.exp_add] at hb
  have hb' : C*((n:ℝ)+5)^a ≤ Real.exp (r*(n:ℝ)) := by
    apply (mul_le_mul_iff_left₀ (Real.exp_pos (r*5))).mp
    nlinarith [hb]
  convert hb' using 1
  rw [Real.rpow_def_of_pos (by norm_num)]
  congr 1
  dsimp [r]
  ring

/-- This absorbs the actual common envelope after its exact source constants
 are expanded. The fixed prefactor may include F1²F2 and every fixed chart cost. -/
theorem absorb_common_envelope {zeta : ℝ} (hzeta : 0 < zeta)
    (B : Choice zeta) (C : ℝ) (_hC : 0 ≤ C) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ R : ℝ,
      (2:ℝ)^((separationExponent B.epsilon/(B.m:ℝ))*(n:ℝ)) ≤ R →
      C*((n:ℝ)+5)^5 *
        (2:ℝ)^((18*B.eta+24/(B.L1:ℝ)+6/(B.L2:ℝ))*(n:ℝ)) *
        R^(3*(B.m:ℝ)*B.epsilon+1/(B.m:ℝ)+2/(B.H:ℝ)) ≤ R^zeta := by
  let q := separationExponent B.epsilon/(B.m:ℝ)
  have hq : 0 < q := div_pos (separationExponent_pos B.epsilon B.epsilon_pos) (Nat.cast_pos.mpr B.m_pos)
  obtain ⟨n0,hn0⟩ := polynomial_absorption C 5 (show 0 < q*zeta/4 by positivity)
  refine ⟨n0,fun n hn R hR => ?_⟩
  have hbase : 1 ≤ (2:ℝ)^(q*(n:ℝ)) := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (1:ℝ) ≤ 2) (mul_nonneg hq.le (Nat.cast_nonneg _))
  have hR1 : 1 ≤ R := hbase.trans hR
  have hRp : 0 < R := zero_lt_one.trans_le hR1
  have hpower : (2:ℝ)^((q*zeta/4)*(n:ℝ)) ≤ R^(zeta/4) := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ (2:ℝ)^(q*(n:ℝ))) hR
      (show 0 ≤ zeta/4 by positivity)
    rw [←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at h
    convert h using 1
    congr 1
    ring
  have hp : C*((n:ℝ)+5)^5 ≤ R^(zeta/4) := (hn0 n hn).trans hpower
  have he : (2:ℝ)^((18*B.eta+24/(B.L1:ℝ)+6/(B.L2:ℝ))*(n:ℝ)) ≤ R^(zeta/4) :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (mul_le_mul_of_nonneg_right B.residual_small (Nat.cast_nonneg n))).trans hpower
  calc
    _ ≤ R^(zeta/4)*R^(zeta/4)*
        R^(3*(B.m:ℝ)*B.epsilon+1/(B.m:ℝ)+2/(B.H:ℝ)) := by gcongr
    _ = R^(zeta/4+zeta/4+(3*(B.m:ℝ)*B.epsilon+1/(B.m:ℝ)+2/(B.H:ℝ))) := by
      rw [← Real.rpow_add hRp, ← Real.rpow_add hRp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR1 (by nlinarith [B.profile_small])
end
end NativeAlignmentParameterBudget
