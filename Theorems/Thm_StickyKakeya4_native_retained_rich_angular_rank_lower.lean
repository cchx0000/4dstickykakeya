import Theorems.Thm_StickyKakeya4_native_retained_rich_angular_power_lower
import Theorems.Thm_StickyKakeya4_native_saturated_angular_rank_budget
import Theorems.Thm_StickyKakeya4_native_sharp_population_admission

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 11000000

noncomputable section
namespace NativeRetainedRichAngularRankLower
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeOriginalCellChartGeometry
open NativeOriginalPointSaturation NativeOriginalPointAngularLower NativeSaturatedAngularPowerLower
open NativeIncidenceMultiplicityTower NativeLocalMenuInterpolation NativeJointUniformCoarseRelations
open NativeFixedCompactKakeyaExponent NativeReferenceOriginalParentProfiles NativeMiddleWindowBalance
open NativeAllTwoScaleConfiguration NativeActualMesoscopicRankConfiguration NativeRankExponentHierarchy
open NativeReferenceSliceBudgetAlgebra NativeActivePhasePopulation NativeSaturatedAngularRankBudget
open NativeQueriedVertexWeights NativeRetainedRichAngularPowerLower NativeNormalizedCellAngularMenu RichDirectionalLayers

/-- Actual source rank mass and original E1 profiles give the retained
rich sigma-class power lower after the single third core. It uses the same
reference/source and original incidence weights; only the explicit third
cost and original sigma-menu count remain for the final scalar payment. -/
theorem actual_retained_rich_angular_rank_lower {n J : ℕ} {D : FiniteScaleSource n}
    {eta a zeta eta0 c tau seed c2 r gap : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (E1 E2 S I T : Finset (Fin n × Index)) (points : Finset Index)
    (hE1 : E1⊆ retained original R) (h21 : E2⊆ E1) (hE2n : E2.Nonempty)
    (rank : Fin 4) (ell : ℕ) (hell : ell≤ 3)
    (heta : 0≤ eta) (heta0 : 0< eta0) (hc : 0< c) (hr : 0< r) (hr1 : r≤ 1)
    (hrdelta : r≤ D.thickness^(cutoff c rank))
    (hmass : r^((2*(ell:ℝ)+1)*rankLoss eta0 c rank)*(E2.card:ℝ)≤ 
      (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ))
    (htau : 0< tau) (hTau : tau≤ commonBudget eta0 c/1024) (hseed : seed≤ tau/16384)
    (hc2 : c2=commonBudget eta0 c/4) (hgap0 : 0≤ gap) (hgapTau : gap≤ tau)
    (g F1 F2 G Q1 Q2 : ℕ) (hg : 0< g) (hgl : g≤ level)
    (hF1 : 0< F1) (hG : 0< G) (hQ1 : 1≤ Q1) (hGF : G≤ F2)
    (hgrid : 1/(g:ℝ)< rankWindow tau/4)
    (H1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta)≤ D.thickness^(-(seed/8)))
    (H2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta)≤ D.thickness^(-c2))
    (HM : ∀d : ℕ,boundaryWindow tau*(level:ℝ)≤ d → (d:ℝ)≤ (1-boundaryWindow tau)*(level:ℝ) →
      HasMiddleScale h R E1 a level d (tau/16))
    (m s ancestorDepth : ℕ) (hm : m≤ level) (hs : 3≤ s) (hf : m+s-3≤ level)
    (hcf : ancestorDepth≤ m+s-3) (hgap : (((m+s-3)-ancestorDepth:ℕ):ℝ)≤ gap*level)
    (p : Parent) (HS : Saturated (parentEdges D a (2^m) E2 p) S Prod.snd)
    (hIS : I⊆ S) (hTI : T⊆ I) (F3 Q3 : ℕ) (hF3 : 0< F3)
    (hret3 : S.card≤ F3*I.card) (HPoint3 : HasUniformFibers I Q3 Prod.snd)
    (HRef : HasUniformFibers E1 Q1 (formalPair D a ancestorDepth))
    (HPoint : HasUniformFibers (parentEdges D a (2^m) E2 p) Q2 Prod.snd)
    (hret :
      let lambda := r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1))
      let W : ℝ := (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)
      let mu := (lambda*W/(2*(F1:ℝ)*G*(E2.card:ℝ)))*D.thickness^eta
      (mu/rowConstant)*(parentEdges D a (2^m) E1 p).card≤ (parentEdges D a (2^m) E2 p).card)
    (sigmaDepth : Fin J → ℕ) (j : Fin J) (k : Index) (hk : k∈I.image Prod.snd) (q : Fin 3 → ℤ)
    (hRich : ((I.filter (fun z => z.2=k)).card:ℝ)/
        (2*(J:ℝ)*(((I.filter (fun z => z.2=k)).image
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1)).card:ℝ)) <
      ((classFiber (T.filter (fun z => z.2=k))
        (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1) q).card:ℝ)) :
    (64/((2^s:ℕ):ℝ))^(-extremalExponent)≤
      ((2744*rowConstant*((g:ℝ)+1))*r^(-(9*rankLoss eta0 c rank)))*
      ((F3:ℝ)*(Q3:ℝ)^2*
        (2*(J:ℝ)*(((I.filter (fun z => z.2=k)).image
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1)).card:ℝ))*
        (((classFiber (T.filter (fun z => z.2=k))
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1) q).image
            (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)) := by
  let loss := rankLoss eta0 c rank
  let lambda := r^loss/(4*((g:ℝ)+1))
  let b : ℝ := (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)/(E2.card:ℝ)
  let gamma := population D.thickness eta lambda b F1 G/rowConstant
  have hd := h.1.2.1
  have hcount : (0:ℝ)< E2.card := by exact_mod_cast hE2n.card_pos
  have hb : r^((2*(ell:ℝ)+1)*loss)≤ b := (le_div_iff₀ hcount).mpr hmass
  have hbpos : 0< b := (Real.rpow_pos_of_pos hr _).trans_le hb
  have hlambda : 0< lambda := by dsimp [lambda]; positivity
  have hloss : 0≤ loss := (rankLoss_pos heta0 hc rank).le
  have hF1r : (0:ℝ)< F1 := by exact_mod_cast hF1
  have hGr : (0:ℝ)< G := by exact_mod_cast hG
  have hRow := rowConstant_pos
  have hgamma : 0< gamma := by dsimp [gamma,population]; positivity
  have hret' : gamma*(parentEdges D a (2^m) E1 p).card≤ (parentEdges D a (2^m) E2 p).card := by
    convert hret using 1
    dsimp [gamma,population,lambda,b,loss]
    congr 1
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hProfiles := actual_all_parent_profiles h original R level Hbackbone E1 hE1 (hE2n.mono h21)
    heta htau hseed g F1 Q1 hg hgl hF1 hQ1 hgrid H1 HM
  have hPower := retained_rich_reference_power_lower h original Hbackbone.1 Hbackbone.2.2.1
    E1 E2 S I T h21 (hE1.trans (filter_subset _ _)) level m s ancestorDepth Hbackbone.2.1 hm hs hf hcf
    hgap0 hgap p HS hIS hTI F3 hF3 hret3 hgamma.le hret' Q1 Q2 Q3 HRef HPoint HPoint3 hProfiles
    sigmaDepth j k hk q hRich
  have ht : commonBudget eta0 c=cutoff c rank*loss := (cutoff_mul_rankLoss eta0 c rank).symm
  have hCost := angular_rank_cost g ell hd h.1.2.2.1 hr hr1 heta hloss hell hrdelta ht rfl hb
    F1 F2 G Q1 Q2 hF1 hG hGF H1 H2 (commonBudget_pos heta0 hc).le hTau hseed hc2 hgapTau
  have hDen : 0< gamma*D.thickness^(2*tau+3*gap) := by positivity
  let X : ℝ := (F3:ℝ)*(Q3:ℝ)^2*
        (2*(J:ℝ)*(((I.filter (fun z => z.2=k)).image
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1)).card:ℝ))*
        (((classFiber (T.filter (fun z => z.2=k))
          (fun z => angularCell D (2^m) (2^(sigmaDepth j)) p z.1) q).image
            (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)
  have hDivide : (64/((2^s:ℕ):ℝ))^(-extremalExponent)≤
      ((343*(Q1:ℝ)^2*(Q2:ℝ)^2)/(gamma*D.thickness^(2*tau+3*gap)))*X := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hDen).mpr
    simpa only [X,mul_assoc,mul_comm,mul_left_comm] using hPower
  exact hDivide.trans (mul_le_mul_of_nonneg_right hCost (by dsimp [X]; positivity))

end NativeRetainedRichAngularRankLower
