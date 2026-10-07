/- UNVERIFIED source draft. No strict Lean check has run on this file. -/
import Theorems.Thm_StickyKakeya4_native_actual_height_third_join
import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_extra
import Theorems.Thm_StickyKakeya4_native_retention_output_power
import Theorems.Thm_StickyKakeya4_native_actual_sparse_reference_admission
import Theorems.Thm_StickyKakeya4_native_paid_third_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeActualBaselineRetentionPayment
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeActualSparseReferenceAdmission NativeRetainedSliceBudgetExtra
open NativeRetainedSliceBudgetAlgebra NativeRetainedSliceBudgetCosts
open NativeReferenceSliceBudgetAlgebra NativeActivePhasePopulation NativeOriginalPrunedMass
open NativeActualNewCutBudget NativeRetentionOutputPower NativeRetainedSliceCore
open NativePaidThirdBudget NativeRankExponentHierarchy

/-- Read the exact pre-third continuation product using its existing
source_total_charge identity. The original quotient occurs once. -/
lemma continuation_cost_readback (q : ℝ) (Kcoh Ksupport normal g R0 Khalf F3 : ℕ)
    (meshConstant row rStop loss rankLoss metric kappa : ℝ) (mesh : Fin Kcoh → ℝ) :
    (NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*
      ((quotientCost q*(coherenceCharge Kcoh normal g meshConstant row rStop
        loss rankLoss metric kappa mesh:ℝ))*
        ((((8*R0)*53^(4*Ksupport))*8^4:ℕ):ℝ))*(F3:ℝ) =
    (NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*quotientCost q*
      (newCutCharge Kcoh Ksupport normal g R0 meshConstant row rStop
        loss rankLoss metric kappa mesh:ℝ)*(F3:ℝ) := by
  rw [NativeActualHeightThirdJoin.source_total_charge]
  ring

/-- This reads the universal raw allowance at the FINAL third-core input
Snext and its full relation dimension d. It never substitutes an older
second-core radix or a smaller relation count. -/
theorem final_third_allowance {n : ℕ} (D : FiniteScaleSource n) (eta : ℝ)
    (h : IsWangZakharovNativeFiniteInput D eta)
    (epsilon eta0 c : ℝ) (g K d J L3 : ℕ) (delta0 : ℝ)
    (Hbudget : HasBudget epsilon eta0 c g K d J L3 delta0)
    (hsmall : D.thickness ≤ delta0) (heta : 0 ≤ eta)
    (hetaSmall : eta ≤ commonBudget eta0 c/32)
    (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (Snext : Finset (Fin n × Index)) (hS : Snext⊆incidences original)
    (hSn : Snext.Nonempty) :
    let F3 := refinementCost (d+2) (J+1) L3
    let Q3 := NativeSourceSizeBounds.radix Snext.card L3
    1 ≤ F3 ∧ 1 ≤ Q3 ∧
      (F3:ℝ)*(Q3:ℝ)^4 ≤ D.thickness^(-(commonBudget eta0 c/4)) := by
  intro F3 Q3
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (refinementCost_pos _ _ _)),?_,?_⟩
  · exact (by norm_num : 1 ≤ (4:ℕ)).trans (NativeSourceSizeBounds.radix_four_le _ _)
  · exact Hbudget.1 n D eta h hsmall heta hetaSmall original horiginal Snext hS hSn

/-- The baseline retention contains only the original graph/quotient/core
cost. The additional Q3 fourth power displayed on the left is retained
explicitly: it is not silently inserted into the baseline Cpre. -/
lemma baseline_factor_identity (delta eta lambda b F1 G F3 Q3 q Ccuts : ℝ)
    (Khalf : ℕ) :
    retentionFactor ((NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*
      quotientCost q*Ccuts*F3) (population delta eta lambda b F1 G)*Q3^4 =
      (64*175616:ℝ)*Ccuts*extraCoefficient delta eta lambda b F1 G F3 Q3 q Khalf := by
  unfold retentionFactor extraCoefficient rowConstant
  simp only [div_div_eq_mul_div]
  ring

/-- The original scalar mass budget, the actual new-cut charge, and the
actual base shape give the baseline admission payment. The cutoff depends
only on fixed parameters and g, before D and before the chosen Snext. -/
theorem exists_actual_retention_cutoff (eB : ℝ) (heB : 0 < eB)
    (Kcoh Ksupport g Khalf : ℕ) (meshConstant row : ℝ)
    (hC : 0 ≤ meshConstant) (hrow : 0 ≤ row) :
    ∃eps0 : ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧
      ∀(delta eta lambda b tau seed t c2 rStop a rankLoss q epsilonQ
        loss metric epsilonGeom kappa eps : ℝ)
        (F1 F2 G Q1 Q2 F3 Q3 m R0 normal : ℕ) (depths : Fin Kcoh → ℕ),
      0 < delta → delta ≤ 1 → 0 ≤ eta →
      0 < F1 → 0 < G → 1 ≤ Q1 → 1 ≤ Q2 → 1 ≤ Q3 → G ≤ F2 →
      (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)) →
      (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2) →
      (F3:ℝ)*(Q3:ℝ)^4 ≤ delta^(-(t/4)) →
      0 ≤ t → tau ≤ t/1024 → seed ≤ tau/16384 → c2=t/4 →
      0 < rStop → rStop ≤ 1 → 0 ≤ rankLoss → rankLoss ≤ 1 →
      rStop ≤ delta^a → t=a*rankLoss →
      lambda=rStop^rankLoss/(4*((g:ℝ)+1)) →
      rStop^(7*rankLoss) ≤ b →
      0 < q → q ≤ 1 → 0 ≤ epsilonQ → epsilonQ ≤ 1 →
      rStop^(epsilonQ/6)/2 ≤ q →
      normal ≤ 4 → 0 ≤ loss → 0 ≤ metric → 0 ≤ epsilonGeom → epsilonGeom ≤ 1/4 →
      metric ≤ rStop^(-2*epsilonGeom) →
      let Rho := (64:ℝ)/((2^m:ℕ):ℝ)
      Rho ≤ 1 → 3072*rStop ≤ Rho^2 → Rho^2 ≤ 6144*rStop →
      ((8*R0:ℕ):ℝ) ≤ 1280*(Rho/64)^(-2*epsilonGeom) →
      0 < eps → eps ≤ eps0 →
      64*eps ≤ 2*max ((5/4:ℝ)*Rho^(1-2*epsilonGeom)) Rho →
      let nu := newExponent Kcoh epsilonGeom loss rankLoss
      nu ≤ 1 → 4*nu+2*(18*rankLoss+4*epsilonQ/3) ≤ eB/64 →
      let Ccuts := (newCutCharge Kcoh Ksupport normal g R0 meshConstant row
        rStop loss rankLoss metric kappa (fun j => 64/((2^(depths j):ℕ):ℝ)):ℝ)
      retentionFactor ((NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*
        quotientCost q*Ccuts*(F3:ℝ)) (population delta eta lambda b F1 G) ≤ eps^(-(eB/32)) := by
  let C : ℝ := (64*175616:ℝ)*fixedFactor Kcoh Ksupport g meshConstant row*extraConstant g Khalf
  have hCpos : 0 < C := by
    have hextra := extraConstant_one_le g Khalf
    have hfixed : 0 < fixedFactor Kcoh Ksupport g meshConstant row := by
      unfold fixedFactor offsetCoefficient
      positivity
    dsimp [C]
    positivity
  obtain ⟨eps0,heps0,heps01,Hpay⟩ := exists_uniform_retention_cutoff eB (6144*C) heB (by positivity)
  refine ⟨eps0,heps0,heps01,?_⟩
  intro delta eta lambda b tau seed t c2 rStop a rankLoss q epsilonQ
    loss metric epsilonGeom kappa eps F1 F2 G Q1 Q2 F3 Q3 m R0 normal depths
    hd hd1 heta hF1 hG hQ1 hQ2 hQ3 hGF H1 H2 H3 ht htau hseed hc2
    hr hr1 hloss hloss1 hrdelta hteq hlambda hb hq hq1 heQ heQ1 hqlow
    hnormal hLoss hmetric heGeom heGeom4 hLip Rho hRho1 hstopLo hstopHi hHeight
    heps hepsSmall hshapeBound nu hnu1 hmargin Ccuts
  have hRho : 0 < Rho := by dsimp [Rho]; positivity
  have hpop : 0 < population delta eta lambda b F1 G := by
    have hlambdaPos : 0 < lambda := by rw [hlambda]; positivity
    have hbPos := (Real.rpow_pos_of_pos hr (7*rankLoss)).trans_le hb
    unfold population
    positivity
  have hquot := quotientCost_pos hq
  have hbase : 0 ≤ retentionFactor
      ((NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*quotientCost q*Ccuts*(F3:ℝ))
      (population delta eta lambda b F1 G) := by
    unfold retentionFactor
    have hvolume := volumeConstant_pos
    have hcuts : 0 ≤ Ccuts := Nat.cast_nonneg _
    positivity
  have hq4 : (1:ℝ) ≤ (Q3:ℝ)^4 := by
    have hh : (1:ℝ) ≤ Q3 := by exact_mod_cast hQ3
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hh 4
  have hfactor := (le_mul_of_one_le_right hbase hq4).trans_eq
    (baseline_factor_identity delta eta lambda b F1 G F3 Q3 q Ccuts Khalf)
  have hExtra := extra_coefficient_bound hd hd1 heta F1 F2 G Q1 Q2 F3 Q3 g 3 Khalf
    hF1 hG hQ1 hQ2 hGF H1 H2 H3 ht htau hseed hc2
    hr hr1 hloss hloss1 (by norm_num) hrdelta hteq hlambda
    (by convert hb using 1 <;> norm_num <;> ring)
    hRho hRho1 hstopHi hq hq1 heQ heQ1 hqlow
  have hExtra' := (le_max_right 1 _).trans hExtra
  have hCuts := source_new_cut_cost Kcoh Ksupport normal g R0 m hnormal
    meshConstant row rStop loss rankLoss metric epsilonGeom kappa depths
    hC hrow hr hr1 hLoss hloss hmetric heGeom hLip hRho1 hstopLo hHeight
  have hRaw : retentionFactor
      ((NativeParentHeightGraphCore.selectionCost Khalf:ℝ)*quotientCost q*Ccuts*(F3:ℝ))
      (population delta eta lambda b F1 G) ≤
      C*rStop^(-nu)*Rho^(-(18*rankLoss+4*epsilonQ/3))*eps^(-(0:ℝ)) := by
    apply hfactor.trans
    calc
      _ ≤ (64*175616:ℝ)*
          (fixedFactor Kcoh Ksupport g meshConstant row*rStop^(-nu))*
          (extraConstant g Khalf*Rho^(-(18*rankLoss+4*epsilonQ/3))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hCuts (by norm_num)
            · exact hExtra'
            · unfold extraCoefficient
              have hcuts : 0 ≤ Ccuts := Nat.cast_nonneg _
              positivity
            · positivity
      _ = _ := by simp only [neg_zero,Real.rpow_zero,mul_one]; dsimp [C]; ring
  have hshape := configured_square_le_reference hRho hRho1 heps.le heGeom heGeom4 hshapeBound
  have hbound := total_retention_at_output hCpos.le heps hRho.le
    (show 0 ≤ nu by dsimp [nu,newExponent]; positivity) hnu1
    (show 0 ≤ 18*rankLoss+4*epsilonQ/3 by positivity) hshape hstopHi hRaw
  simp only [add_zero] at hbound
  exact Hpay eps _ _ heps hepsSmall hmargin hbound

end NativeActualBaselineRetentionPayment
