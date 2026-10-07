import Theorems.Thm_StickyKakeya4_native_actual_squared_grain_selection
import Theorems.Thm_StickyKakeya4_native_generic_reference_queries

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000
noncomputable section

namespace NativeGenericSquaredGrainSelection
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

open NativeSquaredGrainQueries NativeActualQueryRankConfiguration NativeActualSquaredGrainSelection

/-- Consume the actual source's fixed-cardinality query field ONCE with both
queries for every independent grain. The one resulting E2 has the literal
phase-parent short rows, squared-mesh raw vertices, original costs, and the
same terminal plane and transverse incidence tuples. -/
theorem select_squared_grain_second_stage {n d J g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (firstDimension L L2 : ℕ)
    (eta0 c tau : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hschedule : schedule=fullSchedule tau htau g level)
    (hj : j∈NativeRankMesoscopicRadiusMenu.menu (rankWindow tau) (rankWindow_pos htau).le g level)
    (hstop6 : 6 ≤ (schedule j).val)
    (Hselect : ∀ queries : Fin ((J+1)+(J+1)) → ℕ × ℕ,
      (∀i,(queries i).2 ≤ (queries i).1 ∧ (queries i).1 ≤ level) →
      ∀ Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
      (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
      NativeGenericReferenceQueries.HasQuerySecondStageCore h original R E1 F P a level queries schedule firstDimension L L2
        eta0 c tau htau c2 ell j Rel)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀i x,Rel i x x) (hsym : ∀i x y,Rel i x y → Rel i y x) :
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let lambda := r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1))
  let F1 := factor firstDimension (g+1) L
  let G := retentionCost ((d+((J+1)+(J+1))+((J+1)+(J+1))+((J+1)+(J+1))+1)+(g+1)*(g+1)) 1 L2
  let F2 := factor ((d+((J+1)+(J+1))+((J+1)+(J+1))+((J+1)+(J+1))+1)+(g+1)*(g+1)) 1 L2
  let Q2 := NativeSourceSizeBounds.radix F.card L2
  ∃ previous : Fin 4, previous.val+1=ell.val ∧
    ∃ test ∈ NativeRankMesoscopicRadiusMenu.allowed D.thickness (rankWindow tau)
        (rankWindow_pos htau).le g level (cutoff c previous),
      let q := radius (rankWindow tau) (rankWindow_pos htau).le g level test
      r ≤ q ∧ q ≤ r^(2*c) ∧ r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q ∧
      ∃ E2 ⊆ F, E2.Nonempty ∧ E2 ⊆ retained original R ∧ F.card ≤ G*E2.card ∧
        lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card ∧
        lambda/((F1:ℝ)*G)*NativeIncidenceMultiplicityTower.multiplicity (incidences original) ≤
          NativeIncidenceMultiplicityTower.multiplicity E2 ∧
        (∀i x y,x∈E2 → y∈E2 → degree (fun _ : Fin n × Index => 1) (Rel i) E2 x ≤
          Q2^2*degree (fun _ : Fin n × Index => 1) (Rel i) E2 y) ∧
        (∀i : Fin (J+1),
          let m := grainDepth J (schedule j).val i
          let b := phaseDepth m
          let Delta := (64:ℝ)/((2^m:ℕ):ℝ)
          let rep := NativeCoarseDirectionThinning.representative h R a (2^b)
          6 ≤ m ∧ m ≤ b ∧ b ≤ level ∧ 0 < Delta ∧ Delta ≤ 1 ∧
          (64:ℝ)/((2^b:ℕ):ℝ)=Delta^2 ∧ (1:ℝ)/((2^b:ℕ):ℝ) ≤ Delta^2 ∧
          D.thickness ≤ Delta^2 ∧
          Delta/((64:ℝ)/((2^b:ℕ):ℝ))=1/Delta ∧
          HasUniformFibers E2 Q2 (NativeCoarseShadingUniformity.fixedPair D a level b b rep) ∧
          HasUniformFibers E2 Q2 (NativeCoarseShadingUniformity.fixedPair D a level b m rep) ∧
          HasUniformFibers E2 Q2 (fun z => NativeSpatialAngularGeometry.spatialLabel D (2^b) z.2) ∧
          HasUniformFibers E2 Q2 (fun z => NativeSpatialAngularGeometry.spatialLabel D (2^m) z.2)) ∧
        HasUniformFibers E2 Q2 Prod.snd ∧
        (∀i j,HasUniformFibers E2 Q2 (rowPair h R a schedule i j)) ∧
        (∀e,e∈E2 → D.thickness^eta*(2^level:ℕ)/
          (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
          (pairFiber D a (2^level) E2 (localPair D a (2^level) e)).card) ∧
        (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤
          D.thickness^(-c2) ∧
        (∀k∈E2.image Prod.snd,Module.finrank ℝ (P k)=ell.val+1) ∧
        ∀k∈E2.image Prod.snd,
          let A := pointSet E2 k
          let v := fun z : Fin n × Index => slopeVector D z.1
          let C := NativeDirectionRankDichotomy.chains A v q (ell.val+1)
          C.Nonempty ∧ ((A.card:ℝ)/2)^(ell.val+1) ≤ (C.card:ℝ) ∧
            ∀xs∈C,xs.length=ell.val+1 ∧ (∀z∈xs,z∈E2 ∧ z.2=k) ∧
              NativeDirectionRankDichotomy.Separated v q xs ∧
              LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) ∧
              q^(2*(ell.val+1)) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det := by
  have hcap := stopping_depth_cap htau g level schedule hschedule j hj
  have Hactual := Hselect (pairedQueries J (schedule j).val)
    (pairedQueries_valid J (schedule j).val level hstop6 hcap) Rel hrefl hsym
  obtain ⟨_hvalid,previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hOld,hFine,hShort,hRaw,hPoint2,hRows,hRich,hraw2,hPlane,hTuples⟩ := Hactual
  have Hlabels := pairedQueries_uniformities h R a level (schedule j).val E2 _ hFine hShort hRaw
  refine ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hOld,?_,hPoint2,hRows,hRich,hraw2,hPlane,hTuples⟩
  intro i
  have hm6 : 6 ≤ grainDepth J (schedule j).val i := by
    simpa only [grainQueries] using grainQueries_six_le J (schedule j).val hstop6 i
  have hb := phaseDepth_bounds (grainDepth J (schedule j).val i) (schedule j).val level hm6
    (grainDepth_bounds J (schedule j).val i).2 hcap
  have hDelta := grain_scale_pos_le_one _ hm6
  exact ⟨hm6,hb.1,hb.2,hDelta.1,hDelta.2,squared_scale_identity _ hm6,phase_inverse_le_square _ hm6,
    thickness_le_squared_scale _ level hm6 hdy hb.2,short_fine_scale_ratio _ hm6,Hlabels i⟩

end NativeGenericSquaredGrainSelection
