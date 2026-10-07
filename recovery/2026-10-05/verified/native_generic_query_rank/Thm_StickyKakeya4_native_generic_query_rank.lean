import Theorems.Thm_StickyKakeya4_native_generic_reference_queries
import Theorems.Thm_StickyKakeya4_native_retained_query_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7500000
noncomputable section

namespace NativeGenericQueryRank
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization
open NativeFixedCompactKakeyaExponent NativeJointUniformCoarseRelations NativeJointQuantitativeMenu
open NativeBalancedConfiguration NativeFixedSizeScaleMenu NativeLocalMenuInterpolation
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeMiddleTwoScaleConfiguration NativeMasterPointRelations NativeAllTwoScaleConfiguration
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeRankRadiusMenu
open NativeRankExponentHierarchy NativeReferenceCoreGlobalNear NativeRankOneExcludedFromSourceCost
open SelfUniform
open scoped BigOperators ENNReal

open NativeLocalPairUniformCore NativeLocalPairFibers NativeRankRefinedReferenceCore
open NativeRefinedRowRelations NativeRetainedRankCutoffs NativeSecondRefinementCost
open NativeTwoStageTransverseTuples NativeTwoStagePlaneRank NativeRankRadiusRounding
open NativeActualMesoscopicRankConfiguration

open NativeActualRetainedRankConfiguration NativeRetainedQueryMenu

open NativeGenericReferenceData NativeGenericReferenceSecondStage NativeGenericReferenceQueries

def HasQueriedRankSelection {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (d K L2 : ℕ) (eta0 c c2 : ℝ) : Prop :=
  let a := ref.a
  let level := ref.level
  let R := ref.R
  let original := ref.original
  let E1 := ref.E1
  let schedule := ref.schedule
  ∃ (ell : Fin 4) (j : Fin (g + 1)), 1 ≤ ell.val ∧
            j ∈ NativeRankMesoscopicRadiusMenu.menu (rankWindow tau) (rankWindow_pos htau).le g level ∧
            let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
            r ≤ D.thickness ^ (cutoff c ell) ∧ D.thickness ≤ r ∧ r ≤ 1 / 4 ∧
            48 * ((2 ^ (schedule j).val : ℕ) : ℝ) * r = 1 ∧
            ((2 ^ (schedule j).val : ℕ) : ℝ) * D.thickness ≤ 1 ∧ 64 * D.thickness ≤ r ^ 2 ∧
            ∃ F ⊆ E1, F.Nonempty ∧
              (r ^ (rankLoss eta0 c ell) / (4 * ((g : ℝ) + 1))) * (E1.card : ℝ) ≤ (F.card : ℝ) ∧
              ∃ P : Index → Submodule ℝ E4,
                (∀ z ∈ F, Metric.infDist (slopeVector D z.1) (P z.2 : Set E4) ≤ r) ∧
                (∀ k ∈ F.image Prod.snd,
                  Module.finrank ℝ (P k) ≤ ell.val + 1 ∧
                  pointSet F k = pointNear D E1 k r (P k) ∧
                  r ^ (rankLoss eta0 c ell) * ((pointSet E1 k).card : ℝ) ≤ (pointSet F k).card ∧
                  ∀ ell' : Fin 4, ell' < ell →
                    ∀ j' ∈ NativeRankMesoscopicRadiusMenu.menu
                      (rankWindow tau) (rankWindow_pos htau).le g level,
                    radius (rankWindow tau) (rankWindow_pos htau).le g level j' ≤
                      D.thickness ^ (cutoff c ell') →
                    ∀ Q : Submodule ℝ E4, Module.finrank ℝ Q ≤ ell'.val + 1 →
                      ((pointNear D E1 k (radius (rankWindow tau) (rankWindow_pos htau).le g level j') Q).card : ℝ) <
                        (radius (rankWindow tau) (rankWindow_pos htau).le g level j') ^ (rankLoss eta0 c ell') *
                          ((pointSet E1 k).card : ℝ)) ∧
                K+6 ≤ (schedule j).val ∧
                ∀ queries : Fin K → ℕ × ℕ,
                  (∀i,(queries i).2 ≤ (queries i).1 ∧ (queries i).1 ≤ level) →
                ∀ Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  NativeGenericReferenceQueries.HasQuerySecondStageCore h original R E1 F P a level queries schedule ref.dimension L L2
                    eta0 c tau htau c2 ell j Rel

/-- A fixed query-count cutoff supplies the actual stopping depth, and the
query decoder runs on the one generic second-stage core. -/
theorem exists_query_depth_cutoff (K : ℕ) (c : ℝ) (hc : 0 < c) (hcsmall : c ≤ 1/2) :
    ∃delta0 : ℝ,0 < delta0 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta tau seed e zeta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau) (L g : ℕ)
        (ref : Reference h tau htau seed e zeta L g) (d L2 : ℕ) (eta0 c2 : ℝ),
        D.thickness ≤ delta0 → HasRetainedRankSelection ref (d+K+K+K) L2 eta0 c c2 →
        HasQueriedRankSelection ref d K L2 eta0 c c2 := by
  obtain ⟨dGrain,hdGrain,_hdGrain1,hGrain⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < c^3/8 by positivity) (by norm_num : (0:ℝ)≤1)
    (by positivity : (0:ℝ)<1/(48*((2^(K+6):ℕ):ℝ)))
  refine ⟨dGrain,hdGrain,?_⟩
  intro n D eta tau seed e zeta h htau L g ref d L2 eta0 c2 hsmallG H
  let a := ref.a
  let level := ref.level
  let R := ref.R
  let original := ref.original
  let E1 := ref.E1
  let schedule := ref.schedule
  obtain ⟨ell,j,hell,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hSelect⟩ := H
  have hpower : D.thickness^(c^3/8) ≤ 1/(48*((2^(K+6):ℕ):ℝ)) := by
    simpa only [one_mul] using hGrain D.thickness h.1.2.1 hsmallG
  have hrcap : radius (rankWindow tau) (rankWindow_pos htau).le g level j ≤ 1/(48*((2^(K+6):ℕ):ℝ)) :=
    hrcut.trans ((Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1
      (cutoff_bounds hc (by linarith) ell).2.2).trans hpower)
  have hstop6 := NativeActualQueryRankConfiguration.stopping_depth_ge (schedule j).val (K+6) _ hidentity hrcap
  refine ⟨ell,j,hell,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstop6,?_⟩
  intro queries hqueries Rel hrefl hsym
  exact NativeGenericReferenceQueries.decode_second_stage_queries h original R E1 F P a level queries hqueries
    schedule ref.dimension L L2 eta0 c tau htau c2 ell j Rel
    (hSelect (queryMenu h R a level queries Rel) (queryMenu_refl h R a level queries Rel hrefl)
      (queryMenu_symm h R a level queries Rel hsym))

end NativeGenericQueryRank
