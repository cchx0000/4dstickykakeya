/- UNVERIFIED source draft. No strict Lean check has run on this file. -/
import Theorems.Thm_StickyKakeya4_native_Y_total_epsilon_budget
import Theorems.Thm_StickyKakeya4_native_actual_new_cut_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeYSourceParameterLedger
open NativeActualNewCutBudget NativeRankExponentHierarchy NativeYTotalEpsilonBudget

/-- This choice follows chi and precedes c. In particular eB does not
depend on the later c^3 baseline window. -/
def baselineAccuracy (E chi : ℝ) : ℝ := min 1 (chi*E/65536)

/-- K is the fixed number of coherence rounds, not the source-dependent g. -/
def smallTax (eB : ℝ) (K : ℕ) : ℝ := eB/(8192*((K:ℝ)+1))

theorem baseline_accuracy_bounds {E chi : ℝ} (hE : 0 < E) (hchi : 0 < chi) :
    0 < baselineAccuracy E chi ∧ baselineAccuracy E chi ≤ 1 ∧
      baselineAccuracy E chi ≤ chi*E/65536 :=
  ⟨lt_min (by norm_num) (by positivity),min_le_left _ _,min_le_right _ _⟩

/-- All actual geometry/quotient/rank exponents can be kept below one
positive ceiling chosen after eB. The source's nu then pays the baseline
retention using the exact exponent from its actual newCutCharge. -/
theorem geometry_tax_bound {eB epsilonGeom loss rankLoss epsilonQ : ℝ} (K : ℕ)
    (heB : 0 < eB) (heB1 : eB ≤ 1)
    (heGeom : 0 ≤ epsilonGeom) (hLoss : 0 ≤ loss) (hRank : 0 ≤ rankLoss) (hQ : 0 ≤ epsilonQ)
    (heGeomSmall : epsilonGeom ≤ smallTax eB K) (hLossSmall : loss ≤ smallTax eB K)
    (hRankSmall : rankLoss ≤ smallTax eB K) (hQSmall : epsilonQ ≤ smallTax eB K) :
    newExponent K epsilonGeom loss rankLoss ≤ 1 ∧
      4*newExponent K epsilonGeom loss rankLoss+2*(18*rankLoss+4*epsilonQ/3) ≤ eB/64 := by
  let B := smallTax eB K
  have hB : 0 < B := by dsimp [B,smallTax]; positivity
  have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hEq : ((K:ℝ)+1)*B=eB/8192 := by
    dsimp [B,smallTax]
    field_simp [show (K:ℝ)+1 ≠ 0 by positivity]
  have hnu : newExponent K epsilonGeom loss rankLoss ≤ 14*((K:ℝ)+1)*B := by
    unfold newExponent
    calc
      _ ≤ (4*(K:ℝ)+2)*B+(K:ℝ)*(B+9*B) := by gcongr
      _ ≤ _ := by nlinarith only [hB,hK]
  have hA : 18*rankLoss+4*epsilonQ/3 ≤ 20*B := by
    calc
      _ ≤ 18*B+4*B/3 := by gcongr
      _ ≤ _ := by linarith only [hB]
  constructor
  · calc
      _ ≤ 14*(((K:ℝ)+1)*B) := by simpa only [mul_assoc] using hnu
      _ = 14*(eB/8192) := by rw [hEq]
      _ ≤ 1 := by linarith only [heB1]
  · have hh : 4*newExponent K epsilonGeom loss rankLoss+2*(18*rankLoss+4*epsilonQ/3) ≤
        96*(((K:ℝ)+1)*B) := by nlinarith only [hnu,hA,hB,hK]
    rw [hEq] at hh
    linarith only [hh,heB]

/-- At the actual window=c^3/64 and third allowance commonBudget/4,
the eps-scale mass tax needs rankEta0 small independently of c. This is
the RANK hierarchy parameter, not Lemma 5.3's returned AD threshold.
Any further c-dependent ceiling, including c^6, may be imposed afterward. -/
theorem actual_total_tax {E chi rankEta0 c : ℝ} (K : ℕ)
    (hE : 0 < E) (hchi : 0 < chi) (hc : 0 < c)
    (heta0 : 0 ≤ rankEta0)
    (hetaSmall : rankEta0 ≤ smallTax (baselineAccuracy E chi) K) :
    5*baselineAccuracy E chi/16+
      2*(commonBudget rankEta0 c/4)/(c^3/64)+baselineAccuracy E chi/16 ≤
      (chi/2)*(E/16384) := by
  rw [actual_third_tax rankEta0 c hc]
  obtain ⟨heB,_heB1,heBsmall⟩ := baseline_accuracy_bounds hE hchi
  have hB : smallTax (baselineAccuracy E chi) K ≤ baselineAccuracy E chi/8192 := by
    unfold smallTax
    apply div_le_div_of_nonneg_left heB.le (by norm_num : (0:ℝ)<8192)
    have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
    nlinarith only [hK]
  have heta := hetaSmall.trans hB
  nlinarith only [heBsmall,heta,heB,heta0]

end NativeYSourceParameterLedger

