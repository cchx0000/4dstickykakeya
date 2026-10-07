import Theorems.Thm_StickyKakeya4_native_generic_graph_rank_data
import Theorems.Thm_StickyKakeya4_native_post_graph_XY_hook_stage
import Theorems.Thm_StickyKakeya4_native_generic_parent_graph
import Theorems.Thm_StickyKakeya4_native_generic_final_attachment
import Theorems.Thm_StickyKakeya4_native_generic_reference_queries
import Theorems.Thm_StickyKakeya4_native_retained_query_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7500000
noncomputable section

namespace NativeGenericXYRank
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

open NativeGenericReferenceData NativeGenericFinalAttachment NativeGenericParentGraph
open NativeRetainedGrainHistory NativeActualGrainHistory NativeMiddleGrainParentBudget NativeSquaredGrainQueries
def HasXYRankSelection {n : ℕ} {D : FiniteScaleSource n} {eta tau seed e zeta : ℝ}
    {h : IsWangZakharovNativeFiniteInput D eta} {htau : 0 < tau} {L g : ℕ}
    (ref : Reference h tau htau seed e zeta L g) (d J Jhorizontal d3 Khalf L2 L3 : ℕ) (eta0 c c2 epsilon : ℝ) : Prop :=
  let a := ref.a
  let level := ref.level
  let R := ref.R
  let original := ref.original
  let E1 := ref.E1
  let schedule := ref.schedule
  ∃ (ell : Fin 4) (j : Fin (g + 1)), 1 ≤ ell.val ∧ (ell.val+1=2 ∨ ell.val+1=3) ∧
            extremalExponent+((ell.val+1:ℕ):ℝ) ≤ 4 ∧
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
                NativeGenericCompatibleStage.pairedCount J+6 ≤ (schedule j).val ∧
                (∀ queries : Fin (NativeGenericCompatibleStage.pairedCount J) → ℕ × ℕ,
                  (∀i,(queries i).2 ≤ (queries i).1 ∧ (queries i).1 ≤ level) →
                ∀ Rel : Fin (NativeParentHorizontalQueryMenu.size d (Jhorizontal+1)) → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  NativeGenericReferenceQueries.HasQuerySecondStageCore h original R E1 F P a level queries schedule ref.dimension L L2
                    eta0 c tau htau c2 ell j Rel) ∧
                ∃ selected : Fin J,historyDepth J (schedule j).val selected=middleDepth (schedule j).val ∧
                ∀Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  NativePostGraphXYHookStage.HasXYStage (J:=J) h original R E1 F P a level
                    schedule ref.dimension L L2 eta0 c tau seed zeta htau c2 ell j selected
                    Jhorizontal d3 L3 Khalf epsilon Rel


/-- One XY/X/Y third core on each actual stored graph, retaining every earlier
choice and using the third refinement count fixed before the source. -/
theorem xy_rank_of_graph {n d J Jhorizontal d3 Khalf g : ℕ} {D : FiniteScaleSource n}
    {eta tau seed e zeta eta0 c c2 epsilon : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau) (L L2 L3 : ℕ)
    (ref : Reference h tau htau seed e zeta L g)
    (heta : 0 ≤ eta) (hseedTau : seed ≤ tau/16384) (hg : 0 < g)
    (hgrid : 1/(g:ℝ) < rankWindow tau/4) (hsmall : D.thickness ≤ 1/8)
    (hHalf : 3 ≤ Khalf) (hEven : J=2*Khalf) (hHorizontal : 0 < Jhorizontal) (hL3 : 0 < L3)
    (H : NativeGenericGraphRankData.HasGraphRankSelection ref d J (Jhorizontal+1) Khalf L2 eta0 c c2 epsilon) :
    HasXYRankSelection ref d J Jhorizontal d3 Khalf L2 L3 eta0 c c2 epsilon := by
  obtain ⟨ell,j,hell,hrank23,hrange,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect,selected,hmid,Hgraph⟩ := H
  refine ⟨ell,j,hell,hrank23,hrange,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstopK,hSelect,selected,hmid,?_⟩
  intro Rel hrefl hsym
  have hJ : 0 < J := by rw [hEven]; positivity
  have hm12 : 12 ≤ historyDepth J (ref.schedule j).val selected := by
    rw [hmid]
    dsimp only [middleDepth]
    dsimp only [NativeGenericCompatibleStage.pairedCount] at hstopK
    omega
  let depths := NativeFixedHorizontalMenu.depths Jhorizontal (historyDepth J (ref.schedule j).val selected)
  have hdepths : ∀u,historyDepth J (ref.schedule j).val selected ≤ depths u ∧
      depths u ≤ phaseDepth (historyDepth J (ref.schedule j).val selected) :=
    NativeFixedHorizontalMenu.depths_bounds _ _ (by omega)
  exact NativePostGraphXYHookStage.stage_with_post_graph_XY h ref.original ref.R ref.E1 F P
    ref.a ref.level ref.schedule ref.dimension L L2 eta0 c tau seed zeta htau c2 ell j selected
    Jhorizontal d3 L3 Khalf epsilon hHorizontal hL3 Rel heta hJ hg ref.grid_depth hseedTau hgrid
    ref.backbone ref.schedule_eq ref.relations ref.core ref.cost ref.conditioned ref.pairs
    hFE1 hnearP hidentity hsmall hm12 hrange (Hgraph depths hdepths Rel hrefl hsym)

end NativeGenericXYRank
