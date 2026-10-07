import Theorems.Thm_StickyKakeya4_native_generic_final_history
import Theorems.Thm_StickyKakeya4_native_generic_squared_grain_selection
import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_compatible_weighted_retention
import Theorems.Thm_StickyKakeya4_native_actual_squared_grain_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section

namespace NativeGenericFinalAttachment
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent NativeJointUniformCoarseRelations
open NativeJointQuantitativeMenu NativeBalancedConfiguration NativeFixedSizeScaleMenu NativeLocalMenuInterpolation
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeMiddleTwoScaleConfiguration NativeMasterPointRelations NativeAllTwoScaleConfiguration
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeRankRadiusMenu NativeRankExponentHierarchy
open NativeLocalPairUniformCore NativeLocalPairFibers NativeRankRefinedReferenceCore NativeRefinedRowRelations
open NativeRetainedRankCutoffs NativeSecondRefinementCost NativeTwoStageTransverseTuples NativeTwoStagePlaneRank
open NativeRankRadiusRounding NativeActualMesoscopicRankConfiguration NativeActualRetainedRankConfiguration
open NativeRetainedQueryMenu NativeSquaredGrainQueries NativeActualQueryRankConfiguration
open NativeActualSquaredGrainSelection NativeCompatibleWeightedRetention SelfUniform
open scoped BigOperators ENNReal

open NativeGenericCompatibleStage NativeRetainedGrainHistory NativeGenericReferenceData

def retainedCutoff (g J : ℕ) (eta0 c : ℝ) (he0 : 0 < eta0) (hc : 0 < c) : ℝ :=
  min (compatibleCutoff g J (commonBudget eta0 c) (commonBudget_pos he0 hc))
    (min (historyCutoff J (commonBudget eta0 c) (commonBudget_pos he0 hc))
      (historyCutoff (J+1) (commonBudget eta0 c) (commonBudget_pos he0 hc)))

lemma retainedCutoff_pos (g J : ℕ) (eta0 c : ℝ) (he0 : 0 < eta0) (hc : 0 < c) :
    0 < retainedCutoff g J eta0 c he0 hc := by
  exact lt_min (compatibleCutoff_pos _ _ _ _) (lt_min ((historyCutoff_spec _ _ _).1) ((historyCutoff_spec _ _ _).1))

theorem select_final_stage {n d J g : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (htau : 0 < tau) (L L2 : ℕ)
    (ref : Reference h tau htau seed e zeta L g)
    (F : Finset (Fin n × Index)) (P : Index → Submodule ℝ E4)
    (eta0 c c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (hJ : 0 < J) (he0 : 0 < eta0) (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (heta : 0 ≤ eta) (hseed : 0 < seed) (hseedTau : seed ≤ tau/16384)
    (hg : 0 < g) (hgrid : 1/(g:ℝ) < rankWindow tau/4)
    (htauB : tau ≤ commonBudget eta0 c/(1000*((J:ℝ)+1)))
    (hc2 : c2=commonBudget eta0 c/4)
    (hsmallRet : D.thickness ≤ retainedCutoff g J eta0 c he0 hc)
    (hFE1 : F⊆ref.E1)
    (hjmenu : j∈NativeRankMesoscopicRadiusMenu.menu (rankWindow tau) (rankWindow_pos htau).le g ref.level)
    (hsix : 6 ≤ (ref.schedule j).val)
    (hrcut : radius (rankWindow tau) (rankWindow_pos htau).le g ref.level j ≤ D.thickness^(cutoff c ell))
    (hrhi : radius (rankWindow tau) (rankWindow_pos htau).le g ref.level j ≤ 1/4)
    (hE1Near : D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1)
    (hSelect : ∀ queries : Fin ((J+1)+(J+1)) → ℕ × ℕ,
      (∀i,(queries i).2 ≤ (queries i).1 ∧ (queries i).1 ≤ ref.level) →
      ∀ Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
      (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
      NativeGenericReferenceQueries.HasQuerySecondStageCore h ref.original ref.R ref.E1 F P
        ref.a ref.level queries ref.schedule ref.dimension L L2 eta0 c tau htau c2 ell j Rel)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀i x,Rel i x x) (hsym : ∀i x y,Rel i x y → Rel i y x) :
    NativeGenericFinalHistory.HasPrescribedFinalStage (J:=J) h ref.original ref.R ref.E1 F P ref.a ref.level
      ref.schedule ref.dimension L L2 eta0 c tau seed htau c2 ell j Rel := by
  have hcuts : D.thickness ≤ compatibleCutoff g J (commonBudget eta0 c) (commonBudget_pos he0 hc) ∧
      D.thickness ≤ historyCutoff J (commonBudget eta0 c) (commonBudget_pos he0 hc) ∧
      D.thickness ≤ historyCutoff (J+1) (commonBudget eta0 c) (commonBudget_pos he0 hc) := by
    simpa only [retainedCutoff,le_min_iff] using hsmallRet
  have Hcompatible := NativeGenericCompatibleStage.select_compatible_squared_stage h htau L L2 ref F P
    eta0 c c2 ell j hJ he0 hc hcsmall heta hseed hseedTau hg hgrid htauB hc2 hcuts.1
    hFE1 hjmenu hsix hrcut hrhi hE1Near hSelect Rel hrefl hsym
  have Hhistory := NativeGenericPrescribedHistory.prescribed_history_stage_of_compatible h ref.original
    ref.R ref.E1 F P ref.a ref.level ref.schedule ref.dimension L L2 eta0 c tau seed htau c2 ell j Rel
    he0 hc heta ref.backbone hrcut hcuts.2.1 ref.cost Hcompatible
  exact NativeGenericFinalHistory.prescribed_final_stage_of_history h ref.original ref.R ref.E1 F P
    ref.a ref.level ref.schedule ref.dimension L L2 eta0 c tau seed htau c2 ell j Rel he0 hc hJ hrcut hrhi
    hcuts.2.2 Hhistory

end NativeGenericFinalAttachment
