import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_algebra

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000

noncomputable section
namespace NativeRetainedSliceBudgetCosts
open NativeReferenceSliceBudgetAlgebra NativeReferenceSliceBudgetCosts NativeActivePhasePopulation

/-- The actual third-core allowance is paid together with the two original
source costs. In particular, the inverse parent population keeps delta^-eta. -/
lemma third_core_parent_cost {delta eta lambda b tau seed t c2 : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) (heta : 0 ≤ eta) (hlambda : 0 < lambda) (hb : 0 < b)
    (F1 F2 G Q1 Q2 F3 Q3 : ℕ) (hF1 : 0 < F1) (hG : 0 < G)
    (hQ1 : 1 ≤ Q1) (hQ2 : 1 ≤ Q2) (hGF : G ≤ F2)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta) ≤ delta^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta) ≤ delta^(-c2))
    (H3 : (F3:ℝ)*(Q3:ℝ)^4 ≤ delta^(-(t/4)))
    (ht : 0 ≤ t) (htau : tau ≤ t/1024) (hseed : seed ≤ tau/16384) (hc2 : c2=t/4) :
    ((F3:ℝ)*(Q3:ℝ)^4)/(population delta eta lambda b F1 G/rowConstant) ≤
      (2*rowConstant)*delta^(-t)/(lambda*b) := by
  have hF := first_retention_density_cost hd F1 Q1 hQ1 H1
  have hGQ := NativeTwoStageTransversalityBudget.retention_radix_le_of_transfer_cost
    hd hd1 heta F2 Q2 (G:ℝ) (Nat.cast_le.mpr hGF) H2
  have hQ2r : (1:ℝ) ≤ Q2 := by exact_mod_cast hQ2
  have hGcost : (G:ℝ) ≤ delta^(-c2) := (show (G:ℝ) ≤ (G:ℝ)*(Q2:ℝ)^2 from by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hQ2r) (Nat.cast_nonneg G)).trans hGQ
  have hexp : seed/8+c2+t/4 ≤ t := by rw [hc2]; linarith only [ht,htau,hseed]
  have hproduct : ((F1:ℝ)*delta^(-eta))*(G:ℝ)*((F3:ℝ)*(Q3:ℝ)^4) ≤ delta^(-t) := by
    calc
      _ ≤ delta^(-(seed/8))*delta^(-c2)*delta^(-(t/4)) := by gcongr
      _ = delta^(-(seed/8+c2+t/4)) := by
        rw [←Real.rpow_add hd,←Real.rpow_add hd]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hexp)
  have hF1r : (0:ℝ)<F1 := by exact_mod_cast hF1
  have hGr : (0:ℝ)<G := by exact_mod_cast hG
  have hRow := rowConstant_pos
  calc
    _ = (2*rowConstant)*(((F1:ℝ)*delta^(-eta))*(G:ℝ)*((F3:ℝ)*(Q3:ℝ)^4))/(lambda*b) := by
      unfold population
      rw [Real.rpow_neg hd.le eta]
      field_simp
    _ ≤ _ := by gcongr

lemma rank_parent_retention_power {delta r a t rankLoss lambda b : ℝ} (g ell : ℕ)
    (hd : 0 < delta) (hr : 0 < r) (hr1 : r ≤ 1) (hloss : 0 ≤ rankLoss)
    (hell : ell ≤ 3) (hrdelta : r ≤ delta^a) (ht : t=a*rankLoss)
    (hlambda : lambda=r^rankLoss/(4*((g:ℝ)+1)))
    (hb : r^((2*(ell:ℝ)+1)*rankLoss) ≤ b) :
    delta^(-t)/(lambda*b) ≤ (4*((g:ℝ)+1))*r^(-(9*rankLoss)) := by
  have hbpos : 0 < b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hlambdapos : 0 < lambda := by rw [hlambda]; positivity
  have hpow := Real.rpow_le_rpow_of_nonpos hr hrdelta (neg_nonpos.mpr hloss)
  rw [←Real.rpow_mul hd.le] at hpow
  have he : a*(-rankLoss)=-t := by rw [ht]; ring
  rw [he] at hpow
  have hpowers : r^(-rankLoss)/(r^rankLoss*r^((2*(ell:ℝ)+1)*rankLoss))=
      r^(-((2*(ell:ℝ)+3)*rankLoss)) := by
    rw [←Real.rpow_add hr,←Real.rpow_sub hr]
    congr 1
    ring
  calc
    _ ≤ r^(-rankLoss)/(lambda*r^((2*(ell:ℝ)+1)*rankLoss)) := by gcongr
    _ = (4*((g:ℝ)+1))*(r^(-rankLoss)/(r^rankLoss*r^((2*(ell:ℝ)+1)*rankLoss))) := by
      rw [hlambda]
      field_simp
    _ = (4*((g:ℝ)+1))*r^(-((2*(ell:ℝ)+3)*rankLoss)) := by rw [hpowers]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_ge hr hr1
      have hellr : (ell:ℝ) ≤ 3 := by exact_mod_cast hell
      nlinarith only [hellr,hloss]

end NativeRetainedSliceBudgetCosts
