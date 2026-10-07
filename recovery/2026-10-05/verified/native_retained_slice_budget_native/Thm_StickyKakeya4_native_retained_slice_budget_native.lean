import Theorems.Thm_StickyKakeya4_native_retained_slice_budget_final

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeRetainedSliceBudgetNative
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeRetainedSliceCore
open NativeRetainedSliceBudgetSource NativeRetainedSliceBudgetCutoff NativeRetainedSliceBudgetFinal
open NativeRankExponentHierarchy NativeFixedCompactKakeyaExponent NativeAllTwoScaleConfiguration

/-- Source-facing retained AD budget. The same third-core L3 is chosen
before D, and its actual cost on the eventual original-incidence set S is
derived internally. No third-cost or desired AD-bound certificate is needed. -/
theorem exists_actual_native_retained_budget (epsilon eta0 c : ℝ) (g K d J : ℕ)
    (he : 0 < epsilon) (he0 : 0 < eta0) (he01 : eta0 ≤ 1) (heSmall : eta0 ≤ epsilon/336)
    (hc : 0 < c) (hcsmall : c ≤ 1/2) (hcQ : c ≤ quotientTolerance epsilon/24)
    (hJ : 0 < J) (hJloss : 3/(J:ℝ) ≤ epsilon/8) :
    ∃L3 : ℕ,0 < L3 ∧ ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
        IsWangZakharovNativeFiniteInput D eta → D.thickness ≤ delta0 → 0 ≤ eta →
        ∀original : Fin n → Finset Index,
          (∀i,D.shading i=wzCellShading (mesh D) original i) →
          ∀S : Finset (Fin n × Index),S⊆incidences original → S.Nonempty →
          ∀F1 F2 G Q1 Q2 m : ℕ,0 < F1 → 0 < G → 1 ≤ Q1 → 0 < Q2 → G ≤ F2 → 6 ≤ m →
          ∀i : Fin 4,i.val+1 ≤ 3 →
          ∀zeta lambda b tau seed c2 r q : ℝ,
            eta ≤ seed/8 → 0 ≤ tau → tau ≤ commonBudget eta0 c/1024 →
            seed ≤ tau/16384 → zeta ≤ seed/256 → c2=commonBudget eta0 c/4 →
            (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)) →
            (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2) →
            0 < r → r ≤ 1 → r ≤ D.thickness^(cutoff c i) →
            lambda=r^(rankLoss eta0 c i)/(4*((g:ℝ)+1)) →
            r^((2*((i.val+1:ℕ):ℝ)+1)*rankLoss eta0 c i) ≤ b →
            0 < q → q ≤ 1 →
            1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4 →
            r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q →
            ((64:ℝ)/((2^m:ℕ):ℝ))^2 ≤ 6144*r →
            actualRetainedConstant D.thickness eta zeta lambda b F1 G Q2 tau seed c2
              (min (boundaryWindow tau) ((tau/16)/1000))
              (refinementCost (d+1) (J+1) L3) (NativeSourceSizeBounds.radix S.card L3)
              q J m K (3-extremalExponent) ≤ ((64:ℝ)/((2^m:ℕ):ℝ))^(-epsilon) := by
  obtain ⟨L3,hL3,delta0,hd0,hd01,hdRef,hdExtra,H3⟩ :=
    exists_third_budget_cutoffs epsilon eta0 c g K d J he he0 hc
  refine ⟨L3,hL3,delta0,hd0,hd01,?_⟩
  intro n D eta h hsmall heta original horiginal S hS hSn F1 F2 G Q1 Q2 m
    hF1 hG hQ1 hQ2 hGF hm6 i hell zeta lambda b tau seed c2 r q
    hetaSeed htau0 htau hseed hzeta hc2 H1 H2 hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale
  have ht := commonBudget_pos he0 hc
  have hetaSmall := source_eta_allowance ht.le hetaSeed hseed htau
  have hthird := H3 n D eta h hsmall heta hetaSmall original horiginal S hS hSn
  have hF3 : 0 < refinementCost (d+1) (J+1) L3 := refinementCost_pos _ _ _
  have hQ3 : 0 < NativeSourceSizeBounds.radix S.card L3 :=
    lt_of_lt_of_le (by norm_num : 0 < (4:ℕ)) (NativeSourceSizeBounds.radix_four_le _ _)
  exact actual_retained_constant_le_power he he0 he01 heSmall hc hcsmall hcQ
    F1 F2 G Q1 Q2 (refinementCost (d+1) (J+1) L3) (NativeSourceSizeBounds.radix S.card L3)
    g K J m i hJ hJloss hm6 hell h.1.2.1 (hsmall.trans hdRef) (hsmall.trans hdExtra) heta
    hF1 hG hQ1 hQ2 hGF hF3 hQ3 H1 H2 hthird htau0 htau hseed hzeta hc2
    hr hr1 hrdelta hlambda hb hq hq1 hgrid hqraw hscale

end NativeRetainedSliceBudgetNative
