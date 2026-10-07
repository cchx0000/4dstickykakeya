import Theorems.Thm_StickyKakeya4_native_candidate_reference_configuration
import Theorems.Thm_StickyKakeya4_native_actual_mesoscopic_rank_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeGenericReferenceData
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeAllTwoScaleConfiguration NativeActualMesoscopicRankConfiguration NativeReferenceCoreGlobalNear
open scoped ENNReal

/-- The actual first source data with its original, arbitrary core dimension.
All downstream stages read factor(d,g+1,L) from this record. Enlarged relation
menus are never projected to a smaller retention cost. -/
structure Reference {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g : ℕ) where
  a : ℝ
  level : ℕ
  R : Finset (Fin n)
  original : Fin n → Finset Index
  E1 : Finset (Fin n × Index)
  schedule : Fin (g+1) → Fin (level+1)
  dimension : ℕ
  relations : Fin dimension → (Fin n × Index) → (Fin n × Index) → Prop
  backbone : HasOriginalBackbone D original R a level zeta
  grid_depth : g ≤ level
  schedule_eq : schedule=fullSchedule tau htau g level
  core : IsCore D original R a eta zeta dimension (g+1) L relations
    (fun j => 2^(schedule j).val) E1
  cost : (125*175616*16384:ℝ)*(factor dimension (g+1) L:ℝ)*(coreRadix original R L:ℝ)^2*
    D.thickness^(-eta) ≤ D.thickness^(-(seed/8))
  point : HasUniformFibers E1 (coreRadix original R L) Prod.snd
  parent_point : ∀j x y,x∈E1 → y∈E1 →
    degree (fun _ : Fin n × Index => 1) (NativeLocalMenuInterpolation.parentPointRel D a (2^(schedule j).val)) E1 x ≤
      (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1)
        (NativeLocalMenuInterpolation.parentPointRel D a (2^(schedule j).val)) E1 y
  conditioned : ∀i j,HasUniformFibers E1 (coreRadix original R L)
      (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
    HasUniformFibers E1 (coreRadix original R L)
      (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val)
  scales : ∀j,HasJointScale h R E1 a level (schedule j).val e zeta (seed/8) (seed/8) ∧
    HasBalancedScale h R E1 a level (schedule j).val seed
  middle : ∀m : ℕ,boundaryWindow tau*(level:ℝ) ≤ m → (m:ℝ) ≤ (1-boundaryWindow tau)*(level:ℝ) →
    HasMiddleScale h R E1 a level m (tau/16)
  pairs : ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau

lemma factor_pos {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) : 0 < factor ref.dimension (g+1) L := by
  unfold factor NativeLocalPairUniformCore.retentionCost
  positivity

lemma global_near {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (heta : 0 ≤ eta) (hetaSeed : eta ≤ seed/8)
    (hnear : D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal) :
    D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1 := by
  have hh := core_global_near h heta ref.original ref.backbone.1 ref.R ref.E1
    ref.dimension (g+1) L ref.relations _ ref.core ref.cost hnear
  exact (Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1
    (by linarith : -extremalExponent+eta+seed/8 ≤ -extremalExponent+seed/4)).trans hh

end NativeGenericReferenceData
