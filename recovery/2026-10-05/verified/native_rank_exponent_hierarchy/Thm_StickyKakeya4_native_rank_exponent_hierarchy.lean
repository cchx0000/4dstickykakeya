import Mathlib

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

noncomputable section
namespace NativeRankExponentHierarchy

/-- All four geometric rank parameters are chosen before the source tolerance. -/
def rankLoss (eta0 c : ℝ) (i : Fin 4) : ℝ := eta0*c^i.val
def cutoff (c : ℝ) (i : Fin 4) : ℝ := c^(3-i.val)/8
def commonBudget (eta0 c : ℝ) : ℝ := eta0*c^3/8

lemma rankLoss_pos {eta0 c : ℝ} (he : 0 < eta0) (hc : 0 < c) (i : Fin 4) :
    0 < rankLoss eta0 c i := by unfold rankLoss; positivity

lemma cutoff_bounds {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (i : Fin 4) :
    0 < cutoff c i ∧ cutoff c i ≤ 1/8 ∧ c^3/8 ≤ cutoff c i := by
  have hi : 3-i.val ≤ 3 := Nat.sub_le _ _
  have hp := pow_le_one₀ hc.le hc1 (n := 3-i.val)
  have hanti := pow_le_pow_of_le_one hc.le hc1 hi
  unfold cutoff
  exact ⟨by positivity,by linarith,by linarith⟩

lemma commonBudget_pos {eta0 c : ℝ} (he : 0 < eta0) (hc : 0 < c) :
    0 < commonBudget eta0 c := by unfold commonBudget; positivity

/-- The four different rank cutoffs give the same power available to pay
the two retained-source uniformization costs. -/
lemma cutoff_mul_rankLoss (eta0 c : ℝ) (i : Fin 4) :
    cutoff c i*rankLoss eta0 c i=commonBudget eta0 c := by
  have hi : 3-i.val+i.val=3 := by omega
  unfold cutoff rankLoss commonBudget
  calc
    _ = eta0*(c^(3-i.val)*c^i.val)/8 := by ring
    _ = _ := by rw [←pow_add,hi]

lemma rankLoss_le_initial {eta0 c : ℝ} (he : 0 ≤ eta0) (hc : 0 ≤ c)
    (hc1 : c ≤ 1) (i : Fin 4) : rankLoss eta0 c i ≤ eta0 := by
  have hp := pow_le_one₀ hc hc1 (n := i.val)
  simpa only [rankLoss,mul_one] using mul_le_mul_of_nonneg_left hp he

/-- A single beta works at all adjacent rank transitions. -/
lemma adjacent_identities (eta0 c : ℝ) (previous next : Fin 4)
    (hnext : previous.val+1=next.val) :
    (2*c)*rankLoss eta0 c previous=2*rankLoss eta0 c next ∧
      cutoff c next*(2*c)=2*cutoff c previous := by
  have hpow : c^next.val=c^previous.val*c := by rw [←hnext,pow_succ]
  have hexp : 3-previous.val=(3-next.val)+1 := by omega
  constructor
  · unfold rankLoss
    rw [hpow]
    ring
  · unfold cutoff
    rw [hexp,pow_succ]
    ring

lemma test_parameters {eta0 c : ℝ} (_he : 0 < eta0) (hc : 0 < c)
    (hcsmall : c ≤ 1/2) (previous next : Fin 4)
    (hnext : previous.val+1=next.val) :
    0 < 2*c ∧ 2*c ≤ 1 ∧
      cutoff c previous ≤ cutoff c next*(2*c) ∧
      2*rankLoss eta0 c next ≤ (2*c)*rankLoss eta0 c previous := by
  obtain ⟨heta,ha⟩ := adjacent_identities eta0 c previous next hnext
  have hp := (cutoff_bounds hc (by linarith) previous).1
  refine ⟨by positivity,by linarith,?_,heta.ge⟩
  rw [ha]
  linarith

/-- The rank-one contradiction has at least the same positive power as the
tuple budget whenever the largest rank-loss parameter is at most kappa/2. -/
lemma rank_one_power_margin {eta0 c kappa : ℝ} (hc : 0 < c)
    (he : eta0 ≤ kappa/2) :
    commonBudget eta0 c ≤ cutoff c 0*kappa/2 := by
  have hp : 0 ≤ cutoff c 0 := by unfold cutoff; positivity
  have hh := mul_le_mul_of_nonneg_left he hp
  have hid := cutoff_mul_rankLoss eta0 c (0:Fin 4)
  have he0 : rankLoss eta0 c (0:Fin 4)=eta0 := by simp [rankLoss]
  rw [he0] at hid
  rw [←hid]
  nlinarith

end NativeRankExponentHierarchy
