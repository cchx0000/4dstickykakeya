import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_source
import Theorems.Thm_StickyKakeya4_native_retained_slice_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeRetainedSliceBudgetCutoff
open StickyKakeya4 NativeRetainedSliceBudgetExtra NativeRetainedSliceBudgetSource
open NativeReferenceSliceBudgetCutoff NativeRankExponentHierarchy
open NativeCommonCubicalMesh NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeRetainedSliceCore
open NativeOriginalParentSelection

theorem exists_extra_cutoff (epsilon c : ℝ) (g K : ℕ) (he : 0 < epsilon) (hc : 0 < c) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀delta : ℝ,0 < delta → delta ≤ delta0 →
      ∀rho r a : ℝ,0 < rho → c^3/8 ≤ a → r ≤ delta^a → rho^2 ≤ 6144*r →
        extraConstant g K ≤ rho^(-(epsilon/4)) := by
  have hC : 0 < extraConstant g K := lt_of_lt_of_le (by norm_num) (extraConstant_one_le g K)
  obtain ⟨delta0,hd0,hd01,H⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < (c^3/8)*epsilon/8 by positivity)
    (show 0 ≤ extraConstant g K*(6144:ℝ)^(epsilon/8) by positivity)
    (show (0:ℝ)<1 by norm_num)
  refine ⟨delta0,hd0,hd01,?_⟩
  intro delta hd hsmall rho r a hrho ha hrdelta hscale
  have hd1 := hsmall.trans hd01
  have hrbound : r ≤ delta^(c^3/8) := hrdelta.trans
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 ha)
  have hbound : rho^2 ≤ 6144*delta^(c^3/8) := hscale.trans
    (mul_le_mul_of_nonneg_left hrbound (by norm_num))
  have hp := Real.rpow_le_rpow (sq_nonneg rho) hbound (show 0 ≤ epsilon/8 by positivity)
  have hleft : (rho^2)^(epsilon/8)=rho^(epsilon/4) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hrho.le]
    congr 1
    norm_num
    ring
  rw [hleft,Real.mul_rpow (by norm_num) (Real.rpow_nonneg hd.le _),←Real.rpow_mul hd.le] at hp
  have heq : (c^3/8)*(epsilon/8)=(c^3/8)*epsilon/8 := by ring
  rw [heq] at hp
  have hpaid : extraConstant g K*rho^(epsilon/4) ≤ 1 := by
    calc
      _ ≤ extraConstant g K*((6144:ℝ)^(epsilon/8)*delta^((c^3/8)*epsilon/8)) :=
        mul_le_mul_of_nonneg_left hp hC.le
      _ = (extraConstant g K*(6144:ℝ)^(epsilon/8))*delta^((c^3/8)*epsilon/8) := by ring
      _ ≤ _ := H delta hd hsmall
  calc
    _ ≤ 1/rho^(epsilon/4) := (le_div_iff₀ (Real.rpow_pos_of_pos hrho _)).mpr hpaid
    _ = _ := by rw [Real.rpow_neg hrho.le,one_div]

def extraCutoff (epsilon c : ℝ) (g K : ℕ) (he : 0 < epsilon) (hc : 0 < c) : ℝ :=
  Classical.choose (exists_extra_cutoff epsilon c g K he hc)

lemma extraCutoff_pos (epsilon c : ℝ) (g K : ℕ) (he : 0 < epsilon) (hc : 0 < c) :
    0 < extraCutoff epsilon c g K he hc := (Classical.choose_spec (exists_extra_cutoff epsilon c g K he hc)).1

lemma extraCutoff_pays (epsilon c : ℝ) (g K : ℕ) (he : 0 < epsilon) (hc : 0 < c)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ extraCutoff epsilon c g K he hc)
    (rho r a : ℝ) (hrho : 0 < rho) (ha : c^3/8 ≤ a) (hrdelta : r ≤ delta^a)
    (hscale : rho^2 ≤ 6144*r) : extraConstant g K ≤ rho^(-(epsilon/4)) :=
  (Classical.choose_spec (exists_extra_cutoff epsilon c g K he hc)).2.2
    delta hd hsmall rho r a hrho ha hrdelta hscale

/-- Choose the actual third-core parameter and all three source cutoffs
before D or the selected original-incidence subset S. The third dimension
includes the old mixed-grain equality in the very same refinement. -/
theorem exists_third_budget_cutoffs (epsilon eta0 c : ℝ) (g K d J : ℕ)
    (he : 0 < epsilon) (he0 : 0 < eta0) (hc : 0 < c) :
    ∃L3 : ℕ,0 < L3 ∧ ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      delta0 ≤ sourceCutoff (epsilon/2) c g (half_pos he) hc ∧
      delta0 ≤ extraCutoff epsilon c g K he hc ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
        IsWangZakharovNativeFiniteInput D eta → D.thickness ≤ delta0 →
        0 ≤ eta → eta ≤ commonBudget eta0 c/32 →
        ∀original : Fin n → Finset Index,
          (∀i,D.shading i=wzCellShading (mesh D) original i) →
          ∀S : Finset (Fin n × Index),S⊆incidences original → S.Nonempty →
            (refinementCost (d+1) (J+1) L3:ℝ)*(NativeSourceSizeBounds.radix S.card L3:ℝ)^4 ≤
              D.thickness^(-(commonBudget eta0 c/4)) := by
  have ht := commonBudget_pos he0 hc
  obtain ⟨L3,hL3,delta3,hd3,hd31,H3⟩ := NativeRetainedSliceBudget.exists_retained_slice_budget
    (commonBudget eta0 c/4) (by positivity) (d+1) (J+1)
  let delta0 := min delta3 (min (sourceCutoff (epsilon/2) c g (half_pos he) hc)
    (extraCutoff epsilon c g K he hc))
  have h0pos : 0 < delta0 := lt_min hd3 (lt_min (sourceCutoff_pos _ _ _ _ _) (extraCutoff_pos _ _ _ _ _ _))
  refine ⟨L3,hL3,delta0,h0pos,(min_le_left _ _).trans hd31,
    (min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _),?_⟩
  intro n D eta h hsmall heta hetaSmall original horiginal S hS hSn
  exact H3 n D eta h (hsmall.trans (min_le_left _ _)) heta (by linarith only [hetaSmall])
    original horiginal S hS hSn

end NativeRetainedSliceBudgetCutoff
