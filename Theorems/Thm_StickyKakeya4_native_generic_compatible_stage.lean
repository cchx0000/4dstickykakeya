import Theorems.Thm_StickyKakeya4_native_generic_squared_grain_selection
import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_compatible_weighted_retention
import Theorems.Thm_StickyKakeya4_native_actual_squared_grain_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 14000000
noncomputable section

namespace NativeGenericCompatibleStage
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

/-- Two query families per grain, fixed before tau and before the source. -/
def pairedCount (J : ℕ) : ℕ := (J+1)+(J+1)

open NativeGenericReferenceData NativeGenericSquaredGrainSelection
/-- The complete actual squared-grain second stage, with retained compatible
families on this SAME E2 for every choice of original-point Nat weights. -/
def HasCompatibleSquaredStage {n d J g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (firstDimension L L2 : ℕ)
    (eta0 c tau : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
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
        (∀k∈E2.image Prod.snd,
          let A := pointSet E2 k
          let v := fun z : Fin n × Index => slopeVector D z.1
          let C := NativeDirectionRankDichotomy.chains A v q (ell.val+1)
          C.Nonempty ∧ ((A.card:ℝ)/2)^(ell.val+1) ≤ (C.card:ℝ) ∧
            ∀xs∈C,xs.length=ell.val+1 ∧ (∀z∈xs,z∈E2 ∧ z.2=k) ∧
              NativeDirectionRankDichotomy.Separated v q xs ∧
              LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) ∧
              q^(2*(ell.val+1)) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det) ∧
        ∀w : Index → ℕ, NativeCompatibleWeightedRetention.RetainedFamily D a (schedule j).val E2 q
          (ell.val+1) w J (r^(2*((ell.val+1:ℕ):ℝ)*rankLoss eta0 c ell))


/-- The weak retention cutoff depends only on the fixed finite menus and rank budget. -/
def compatibleCutoff (g J : ℕ) (t : ℝ) (ht : 0 < t) : ℝ :=
  (exists_uniform_weak_retention g J ht).choose

lemma compatibleCutoff_pos (g J : ℕ) (t : ℝ) (ht : 0 < t) :
    0 < compatibleCutoff g J t ht := (exists_uniform_weak_retention g J ht).choose_spec.1

/-- The enlarged first-stage reference supplies its actual dimension, cost and
profiles to the compatible-family construction. The second core is chosen once. -/
theorem select_compatible_squared_stage {n d J g : ℕ} {D : FiniteScaleSource n}
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
    (hsmallRet : D.thickness ≤ compatibleCutoff g J (commonBudget eta0 c) (commonBudget_pos he0 hc))
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
    HasCompatibleSquaredStage (J:=J) h ref.original ref.R ref.E1 F P ref.a ref.level
      ref.schedule ref.dimension L L2 eta0 c tau htau c2 ell j Rel := by
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples⟩ :=
    NativeGenericSquaredGrainSelection.select_squared_grain_second_stage h ref.original ref.R ref.E1 F P
      ref.a ref.level ref.schedule ref.dimension L L2 eta0 c tau htau c2 ell j
      ref.backbone.2.1 ref.schedule_eq hjmenu hsix hSelect Rel hrefl hsym
  refine ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hGrains,hPoint2,hRows,hRich,hCost2,hPlane,hTuples,?_⟩
  intro w
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g ref.level j
  let q := radius (rankWindow tau) (rankWindow_pos htau).le g ref.level test
  let d2 := (d+pairedCount J+pairedCount J+pairedCount J+1)+(g+1)*(g+1)
  have hr : 0 < r := radius_pos _ _ _ _ _
  have hq : 0 < q := radius_pos _ _ _ _ _
  have hr1 : r ≤ 1 := hrhi.trans (by norm_num)
  have hstop : (ref.schedule j).val ≤ ref.level := Nat.le_of_lt_succ (ref.schedule j).isLt
  have hgrid' : 1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4 := by
    simpa only [rankWindow] using hgrid
  have hupper : ∀p,(parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D ref.a (2^(ref.schedule j).val) ref.E1 p) ≤
        D.thickness^(-seed)*((((2^(ref.schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent)) := by
    intro p hp
    exact (((ref.scales j).2).2.2 p hp).2.2.2
  have Hcounts : ∀k∈E2.image Prod.snd,
      (((pointSet E2 k).card:ℝ)/2)^(ell.val+1) ≤
        ((chains (pointSet E2 k) (fun z => slopeVector D z.1) q (ell.val+1)).card:ℝ) := by
    intro k hk
    exact (hTuples k hk).2.1
  have Hexact := from_master_and_actual_cost h ref.original ref.R ref.E1 F E2 (hE2F.trans hFE1)
    ref.schedule ref.relations htau heta hseedTau hg ref.grid_depth hgrid' ref.backbone ref.schedule_eq
    ref.core ref.cost ref.conditioned ref.pairs J (ref.schedule j).val d2 L2 hJ hstop hsix r
    (rankLoss eta0 c ell) hr hret hE1Near hCost2 (ref.parent_point j) hPoint2 hupper q hq (ell.val+1) Hcounts w
  have Hweak := (exists_uniform_weak_retention g J (commonBudget_pos he0 hc)).choose_spec.2.2
  exact Hweak n D h.1.2.1 hsmallRet (cutoff c ell) (rankLoss eta0 c ell) seed c2 tau r
    (cutoff_bounds hc (by linarith) ell).1 (rankLoss_pos he0 hc ell)
    (cutoff_mul_rankLoss eta0 c ell).symm htau.le hseed.le hseedTau htauB hc2 hr hr1 hrcut
    ref.a q (ref.schedule j).val (ell.val+1) E2 w Hexact

end NativeGenericCompatibleStage
