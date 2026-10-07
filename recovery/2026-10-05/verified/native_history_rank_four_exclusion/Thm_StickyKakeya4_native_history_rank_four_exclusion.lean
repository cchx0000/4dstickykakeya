import Theorems.Thm_StickyKakeya4_native_actual_history_configuration
import Theorems.Thm_StickyKakeya4_native_rank_four_scalar_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000

noncomputable section
namespace NativeHistoryRankFourExclusion
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeSpatialAngularGeometry NativeJointUniformCoarseRelations NativeBalancedConfiguration
open NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance NativeAllTwoScaleConfiguration
open NativeConditionedPairMenu NativeMasterPointRelations NativeActualMesoscopicRankConfiguration
open NativeLocalPairUniformCore NativeActualCompatibleConfiguration
open NativeRankRadiusMenu NativeRankExponentHierarchy NativeActualHistoryConfiguration
open NativeRetainedQueryMenu NativeSquaredGrainQueries NativeRetainedGrainHistory
open NativeCompatibleAngularCandidates NativeQueriedVertexWeights NativeActualAngularMenuCost
open NativeSourceSizeBounds NativeSecondRefinementCost NativeActualRankFourCount
open NativeRawPointSourceProfiles NativeRawPointRankFourRatio NativeRankFourScalarBudget
open scoped BigOperators

/-- This cutoff depends on the already fixed critical exponent and menu
size, before any native source D or any stopping rank is selected. -/
def extraCutoff (hk : 0 < extremalExponent) (g : ℕ) : ℝ :=
  (exists_scalar_cutoff extremalExponent hk g).choose

theorem extraCutoff_spec (hk : 0 < extremalExponent) (g : ℕ) :
    0 < extraCutoff hk g ∧ extraCutoff hk g ≤ 1/8 ∧
      ∀delta : ℝ,0 < delta → delta ≤ extraCutoff hk g →
        delta^(1/16:ℝ) ≤ 1/48 ∧
          delta^(extremalExponent/16) ≤ 1/(2*fixedConstant extremalExponent g) :=
  (exists_scalar_cutoff extremalExponent hk g).choose_spec

/-- Eliminate rank four from the actual selected history, preserving its
stored E2, original weights, and compatible pair family. Both geometric
counts and both raw point profiles are derived internally from source fields. -/
theorem history_stage_rank_ne_four {n d J g : ℕ} {D : FiniteScaleSource n}
    {eta zeta eta0 c tau seed c2 a : ℝ}
    (hk : 0 < extremalExponent) (hJ : 0 < J)
    (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent/2)
    (hc : 0 < c) (hc8 : c ≤ 1/8) (hcK : c ≤ extremalExponent/128)
    (htau : 0 < tau) (htauHalf : tau ≤ 1/2)
    (hTau : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)))
    (hseed0 : 0 ≤ seed) (hzeta0 : 0 ≤ zeta)
    (hseed : seed ≤ tau/16384) (hzseed : zeta ≤ seed/256)
    (hc2 : c2=commonBudget eta0 c/4)
    (h : IsWangZakharovNativeFiniteInput D eta) (heta : 0 ≤ eta) (hetaSeed : eta ≤ seed/8)
    (original : Fin n → Finset Index) (R : Finset (Fin n))
    (E1 F : Finset (Fin n × Index)) (hF : F⊆E1) (plane : Index → Submodule ℝ E4)
    (level L L2 : ℕ) (schedule : Fin (g+1) → Fin (level+1))
    (hschedule : schedule=fullSchedule tau htau g level)
    (hgrid : 1/(g:ℝ) < rankWindow tau/4)
    (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (Hcore : IsCore D original R a eta zeta
      (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L
      (relationMenu h R a schedule (pairRelationMenu h R a schedule (masterRelations D a schedule)))
      (fun j => 2^(schedule j).val) E1)
    (hcost1 : (125*175616*16384:ℝ)*
      (factor (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L:ℝ)*
      (coreRadix original R L:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)))
    (HM : ∀m : ℕ,boundaryWindow tau*(level:ℝ) ≤ m →
      (m:ℝ) ≤ (1-boundaryWindow tau)*(level:ℝ) → HasMiddleScale h R E1 a level m (tau/16))
    (ell : Fin 4) (j : Fin (g+1))
    (hj : j∈NativeRankMesoscopicRadiusMenu.menu (rankWindow tau) (rankWindow_pos htau).le g level)
    (hrcut : radius (rankWindow tau) (rankWindow_pos htau).le g level j ≤ D.thickness^(cutoff c ell))
    (HB : HasBalancedScale h R E1 a level (schedule j).val seed)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : HasHistorySquaredStage (J:=J) h original R E1 F plane a level schedule L L2
      eta0 c tau seed htau c2 ell j Rel)
    (hsmall : D.thickness ≤ extraCutoff hk g) : ell.val+1≠4 := by
  intro hell
  have heq : ell=(3:Fin 4) := by
    apply Fin.ext
    change ell.val=3
    omega
  subst ell
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let m := (schedule j).val
  let e := eta0*c^3
  let lambda := r^e/(4*((g:ℝ)+1))
  let F1 := factor (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L
  let d2 := (d+pairedCount J+pairedCount J+pairedCount J+1)+(g+1)*(g+1)
  let G := retentionCost d2 1 L2
  let F2 := factor d2 1 L2
  let Q1 := coreRadix original R L
  let Q2 := NativeSourceSizeBounds.radix F.card L2
  obtain ⟨_previous,_hprevious,test,_htest,_hrq,_hqr,hqlo,E2,hE2F,hE2ne,hE2old,_hret2,hret,
    _hnear2,_hCaller,hGrains,_hPoint2,_hRows,hRich,hCost2,_hPlane,_hTuples,_hFamily,hHistory⟩ := H
  let q := radius (rankWindow tau) (rankWindow_pos htau).le g level test
  have hd : 0 < D.thickness := h.1.2.1
  obtain ⟨_hd0,hd08,hcut⟩ := extraCutoff_spec hk g
  obtain ⟨hmidSmall,hscalarSmall⟩ := hcut D.thickness hd hsmall
  have hd8 : D.thickness ≤ 1/8 := hsmall.trans hd08
  have hd1 : D.thickness ≤ 1 := hd8.trans (by norm_num)
  have hr : 0 < r := radius_pos _ _ _ _ _
  have hq : 0 < q := radius_pos _ _ _ _ _
  have hr1 : r ≤ 1 := (radius_le_one_div_48 _ _ _ _ _).trans (by norm_num)
  have hq1 : q ≤ 1 := (radius_le_one_div_48 _ _ _ _ _).trans (by norm_num)
  have hrdelta : r ≤ D.thickness^(1/8:ℝ) := by
    norm_num only [cutoff] at hrcut
    exact hrcut
  have hidentity : 48*((2^m:ℕ):ℝ)*r=1 := by
    simpa only [m,r,hschedule,fullSchedule_eq_rankWindow] using
      radius_parent_identity (rankWindow tau) (rankWindow_pos htau).le g level j
  have hDelta : 64/((2^m:ℕ):ℝ)=3072*r := by
    apply (div_eq_iff (show (((2^m:ℕ):ℝ))≠0 by positivity)).mpr
    nlinarith only [hidentity]
  have hstop : m ≤ level/4 := stopping_depth_cap htau g level schedule hschedule j hj
  have hlo : boundaryWindow tau*(level:ℝ) ≤ m :=
    rank_four_middle_lower hd level m Hbackbone.2.1 hidentity hrdelta hmidSmall htauHalf
  have hw : boundaryWindow tau ≤ 1/2 :=
    (min_le_right _ _).trans (by norm_num : (1/8:ℝ) ≤ 1/2)
  have hlast := hGrains (Fin.last J)
  rw [grainDepth_last J m hJ] at hlast
  obtain ⟨hm6,_hmb,hpL,_hDp,_hD1,_hsquare,_hinv,hscale,_hratio,HF,HC,HV,HVcoarse⟩ := hlast
  have h21 : E2⊆E1 := hE2F.trans hF
  have hE : E2⊆incidences original := fun z hz => (mem_filter.mp (hE2old hz)).1
  have hER : ∀z∈E2,z.1∈R := fun z hz => (mem_filter.mp (hE2old hz)).2
  have hF1 : 0 < F1 := original_factor_pos _ _ _
  have hG : 0 < G := by dsimp [G,retentionCost]; positivity
  have hQ1 : 1 ≤ Q1 := (show 1 ≤ 4 by norm_num).trans (radix_four_le _ _)
  have hQ2 : 0 < Q2 := (show 0 < 4 by norm_num).trans_le (radix_four_le _ _)
  have hGF : G ≤ F2 := retained_cost_le_factor d2 1 L2 (by omega)
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hc2' : c2=e/32 := by rw [hc2]; dsimp [commonBudget,e]; ring
  have hcost2' : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤
      D.thickness^(-(e/32)) := by simpa only [hc2',F2,Q2,d2,pairedCount] using hCost2
  obtain ⟨C,hC,S,_hSE,hS,_hinj,_hmass,hretC,hcompatible,_hwitness,_htrace,_hrest⟩ := hHistory
  subst S
  change r^(2*(4:ℝ)*e)*(WeightedRichDirectionalLayers.mass (E2.image Prod.snd) (pointWeight E2):ℝ) ≤
    (WeightedRichDirectionalLayers.mass (C.image Prod.fst) (pointWeight E2):ℝ) at hretC
  rw [NativeQueriedVertexWeights.reference_mass] at hretC
  have hretPower : r^(8*e)*(E2.card:ℝ) ≤
      (WeightedRichDirectionalLayers.mass (C.image Prod.fst) (pointWeight E2):ℝ) := by
    norm_num only [show (2:ℝ)*4=8 by norm_num] at hretC
    exact hretC
  have hN : 0 < E2.card := card_pos.mpr hE2ne
  have hpositive : 0 < r^(8*e)*(E2.card:ℝ) := by positivity
  have hCn : C.Nonempty := by
    by_contra hcn
    rw [not_nonempty_iff_eq_empty.mp hcn] at hretPower
    simp only [image_empty,WeightedRichDirectionalLayers.mass,sum_empty,Nat.cast_zero] at hretPower
    exact (not_le_of_gt hpositive) hretPower
  have hcompat : ∀x y,x∈C → y∈C → spatialLabel D (2^m) x.1=spatialLabel D (2^m) y.1 →
      projectWord m m x.2=projectWord m m y.2 := by
    simpa only [m,depth_last J (schedule j).val hJ] using hcompatible J (by omega : J<J+1)
  have hgeometry := actual_rank_four_count h original Hbackbone.1 Hbackbone.2.2.1
    R E2 hE hER F1 F2 G Q1 Q2 hF1 hG hQ2 hQ1 hGF heta Hbackbone.2.1 hlambda
    hRich hcost1 hcost2' m m le_rfl hm6 hpL hscale HF HC HV HVcoarse hq hq1 C hCn hC hcompat
  have hprofile := source_squared_raw_ratio_of_middle_window h original R E1 E2 h21 hE2ne L schedule
    (pairRelationMenu h R a schedule (masterRelations D a schedule)) Hbackbone Hcore j hm6 hstop hd8 HB
    (boundaryWindow tau) hw hlo HM G hG lambda hlambda.le hret
  have hVc : 0 < rawPointCount D E2 m := card_pos.mpr (hE2ne.image _)
  simp only [vertices_card_eq_rawPointCount,hDelta] at hgeometry
  change lambda*D.thickness^(2*eta+2*zeta+seed+tau/16)*(64/((2^m:ℕ):ℝ))^4*
      (rawPointCount D E2 (phaseDepth m):ℝ) ≤
    pointRatioConstant*(F1:ℝ)*G*(Q1:ℝ)^4*(64/((2^m:ℕ):ℝ))^extremalExponent*
      (rawPointCount D E2 m:ℝ) at hprofile
  rw [hDelta] at hprofile
  exact contradiction_from_counts hd hd1 hr hr1 hrdelta hk he0 heK hc hc8 hcK
    heta heta hzeta0 hseed0 htau.le hetaSeed hzseed hseed g J hTau hgrid hqlo
    F1 F2 G Q1 Q2 E2.card (WeightedRichDirectionalLayers.mass (C.image Prod.fst) (pointWeight E2))
    (rawPointCount D E2 m) (rawPointCount D E2 (phaseDepth m)) hF1 hGF hN hVc hretPower
    hcost1 hcost2' hgeometry hprofile hscalarSmall

end NativeHistoryRankFourExclusion
