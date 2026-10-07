import Theorems.Thm_StickyKakeya4_native_history_dimension_range
import Theorems.Thm_StickyKakeya4_native_generic_prescribed_history
import Theorems.Thm_StickyKakeya4_native_physical_reference_data
import Theorems.Thm_StickyKakeya4_native_actual_history_configuration
import Theorems.Thm_StickyKakeya4_native_actual_rank_count

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1500000

noncomputable section
namespace NativeGenericHistoryDimensionRange
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeSpatialAngularGeometry NativeJointUniformCoarseRelations NativeBalancedConfiguration
open NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance NativeAllTwoScaleConfiguration
open NativeConditionedPairMenu NativeMasterPointRelations NativeActualMesoscopicRankConfiguration
open NativeLocalPairUniformCore NativeActualCompatibleConfiguration
open NativeRankRadiusMenu NativeRankExponentHierarchy NativeActualHistoryConfiguration
open NativeRetainedQueryMenu NativeSquaredGrainQueries NativeRetainedGrainHistory
open NativeCompatibleAngularCandidates NativeQueriedVertexWeights NativeActualAngularMenuCost
open NativeSourceSizeBounds NativeSecondRefinementCost NativeActualRankCount
open NativeRawPointSourceProfiles NativeRawPointRankFourRatio NativeGeneralRankScalarBudget
open scoped BigOperators

open NativeGenericReferenceData NativePhysicalReferenceData NativeGenericPrescribedHistory
open NativeHistoryDimensionRange

/-- The actual prescribed history gives the dimension range for an arbitrary
source-produced Reference, preserving its full initial relation dimension. -/
theorem history_stage_dimension_range {n d J g : ℕ} {D : FiniteScaleSource n}
    {eta zeta eta0 c tau seed c2 e : ℝ}
    (hJ : 0 < J) (he0 : 0 < eta0)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcUnit : c ≤ 1/(eta0+1))
    (hcGap : c ≤ positiveGap extremalExponent/(256*(eta0+1)))
    (htau : 0 < tau)
    (hTau : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)))
    (hseed0 : 0 ≤ seed) (hzeta0 : 0 ≤ zeta)
    (hseed : seed ≤ tau/16384) (hzseed : zeta ≤ seed/256)
    (hc2 : c2=commonBudget eta0 c/4)
    (h : IsWangZakharovNativeFiniteInput D eta) (heta : 0 ≤ eta) (hetaSeed : eta ≤ seed/8)
    (L L2 : ℕ) (ref : Reference h tau htau seed e zeta L g)
    (Hphysical : HasPhysicalUniformities ref)
    (F : Finset (Fin n × Index)) (hF : F⊆ref.E1) (plane : Index → Submodule ℝ E4)
    (hgrid : 1/(g:ℝ) < rankWindow tau/4)
    (ell : Fin 4) (j : Fin (g+1))
    (hj : j∈NativeRankMesoscopicRadiusMenu.menu (rankWindow tau) (rankWindow_pos htau).le g ref.level)
    (hrcut : radius (rankWindow tau) (rankWindow_pos htau).le g ref.level j ≤ D.thickness^(cutoff c ell))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : HasPrescribedHistoryStage (J:=J) h ref.original ref.R ref.E1 F plane ref.a ref.level ref.schedule
      ref.dimension L L2
      eta0 c tau seed htau c2 ell j Rel)
    (hsmall : D.thickness ≤ extraCutoff c hc hc1 g) :
      extremalExponent+((ell.val+1:ℕ):ℝ) ≤ 4 := by
  let original := ref.original
  let R := ref.R
  let E1 := ref.E1
  let a := ref.a
  let level := ref.level
  let schedule := ref.schedule
  have hschedule : schedule=fullSchedule tau htau g level := ref.schedule_eq
  have Hbackbone := ref.backbone
  have hcost1 := ref.cost
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let m := (schedule j).val
  let e := rankLoss eta0 c ell
  let lambda := r^e/(4*((g:ℝ)+1))
  let F1 := factor ref.dimension (g+1) L
  let d2 := (d+pairedCount J+pairedCount J+pairedCount J+1)+(g+1)*(g+1)
  let G := retentionCost d2 1 L2
  let F2 := factor d2 1 L2
  let Q1 := coreRadix original R L
  let Q2 := NativeSourceSizeBounds.radix F.card L2
  obtain ⟨previous,hprevious,test,_htest,_hrq,_hqr,hqlo,E2,hE2F,hE2ne,hE2old,_hret2,hret,
    _hnear2,_hCaller,hGrains,_hPoint2,_hRows,hRich,hCost2,_hPlane,_hTuples,_hFamily,hHistory⟩ := H
  let q := radius (rankWindow tau) (rankWindow_pos htau).le g level test
  have hd : 0 < D.thickness := h.1.2.1
  obtain ⟨_hd0,hd08,hcut⟩ := extraCutoff_spec c hc hc1 g
  obtain ⟨hmidSmall,hscalarSmall⟩ := hcut D.thickness hd hsmall ell
  have hd8 : D.thickness ≤ 1/8 := hsmall.trans hd08
  have hd1 : D.thickness ≤ 1 := hd8.trans (by norm_num)
  have hr : 0 < r := radius_pos _ _ _ _ _
  have hq : 0 < q := radius_pos _ _ _ _ _
  have hr1 : r ≤ 1 := (radius_le_one_div_48 _ _ _ _ _).trans (by norm_num)
  have hq1 : q ≤ 1 := (radius_le_one_div_48 _ _ _ _ _).trans (by norm_num)
  have hi : 1 ≤ ell.val := by omega
  have hell : 0 < dimension ell := by dsimp [dimension]; omega
  have hell4 : dimension ell ≤ 4 := by dsimp [dimension]; omega
  have hrdelta : r ≤ D.thickness^(cutoff c ell) := hrcut
  have hidentity : 48*((2^m:ℕ):ℝ)*r=1 := by
    simpa only [m,r,hschedule,fullSchedule_eq_rankWindow] using
      radius_parent_identity (rankWindow tau) (rankWindow_pos htau).le g level j
  have hDelta : 64/((2^m:ℕ):ℝ)=3072*r := by
    apply (div_eq_iff (show (((2^m:ℕ):ℝ))≠0 by positivity)).mpr
    nlinarith only [hidentity]
  have hstop : m ≤ level/4 := stopping_depth_cap htau g level schedule hschedule j hj
  have hTauCut := tau_le_cutoff he0.le hc hc1 hcUnit ell hi htau.le J hTau
  have hlo : boundaryWindow tau*(level:ℝ) ≤ m :=
    middle_lower hd (cutoff_bounds hc hc1 ell).1.le level m Hbackbone.2.1 hidentity hrdelta hmidSmall hTauCut
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
  have hcost2' : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤
      D.thickness^(-(commonBudget eta0 c/4)) := by
    simpa only [hc2,F2,Q2,d2,pairedCount] using hCost2
  obtain ⟨C,hC,S,_hSE,hS,_hinj,_hmass,hretC,hcompatible,_hwitness,_htrace,_hrest⟩ := hHistory
  subst S
  change r^(2*(dimension ell:ℝ)*e)*(WeightedRichDirectionalLayers.mass (E2.image Prod.snd) (pointWeight E2):ℝ) ≤
    (WeightedRichDirectionalLayers.mass (C.image Prod.fst) (pointWeight E2):ℝ) at hretC
  rw [NativeQueriedVertexWeights.reference_mass] at hretC
  have hretPower : r^(2*(dimension ell:ℝ)*e)*(E2.card:ℝ) ≤
      (WeightedRichDirectionalLayers.mass (C.image Prod.fst) (pointWeight E2):ℝ) := hretC
  have hN : 0 < E2.card := card_pos.mpr hE2ne
  have hpositive : 0 < r^(2*(dimension ell:ℝ)*e)*(E2.card:ℝ) := by positivity
  have hCn : C.Nonempty := by
    by_contra hcn
    rw [not_nonempty_iff_eq_empty.mp hcn] at hretPower
    simp only [image_empty,WeightedRichDirectionalLayers.mass,sum_empty,Nat.cast_zero] at hretPower
    exact (not_le_of_gt hpositive) hretPower
  have hcompat : ∀x y,x∈C → y∈C → spatialLabel D (2^m) x.1=spatialLabel D (2^m) y.1 →
      projectWord m m x.2=projectWord m m y.2 := by
    simpa only [m,schedule,depth_last J (ref.schedule j).val hJ] using hcompatible J (by omega : J<J+1)
  have hgeometry := actual_rank_count h original Hbackbone.1 Hbackbone.2.2.1
    R E2 hE hER F1 F2 G Q1 Q2 hF1 hG hQ2 hQ1 hGF heta Hbackbone.2.1 hlambda
    hRich hcost1 hcost2' m m le_rfl hm6 hpL hscale HF HC HV HVcoarse (dimension ell) hell hell4 hq hq1 C hCn hC hcompat
  have hprofile := squared_raw_ratio_of_middle ref Hphysical E2 h21 hE2ne j hm6 hstop hd8 hlo
    G hG lambda hlambda.le hret
  have hVc : 0 < rawPointCount D E2 m := card_pos.mpr (hE2ne.image _)
  simp only [vertices_card_eq_rawPointCount,hDelta] at hgeometry
  rw [←loss_power hd.le (seed/8+5*(commonBudget eta0 c/4)) (dimension ell)] at hgeometry
  change lambda*D.thickness^(2*eta+2*zeta+seed+tau/16)*(64/((2^m:ℕ):ℝ))^4*
      (rawPointCount D E2 (phaseDepth m):ℝ) ≤
    pointRatioConstant*(F1:ℝ)*G*(Q1:ℝ)^4*(64/((2^m:ℕ):ℝ))^extremalExponent*
      (rawPointCount D E2 m:ℝ) at hprofile
  rw [hDelta] at hprofile
  exact dimension_range_from_counts hd hd1 hr hr1 he0 hc hc1 hcGap ell hi hrdelta
    heta heta hzeta0 hseed0 htau.le hetaSeed hzseed hseed g J hTau hgrid hqlo
    F1 F2 G Q1 Q2 E2.card (WeightedRichDirectionalLayers.mass (C.image Prod.fst) (pointWeight E2))
    (rawPointCount D E2 m) (rawPointCount D E2 (phaseDepth m)) hF1 hGF hN hVc hretPower
    hcost1 hcost2' hgeometry hprofile hscalarSmall

end NativeGenericHistoryDimensionRange
