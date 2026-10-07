import Theorems.Thm_StickyKakeya4_native_all_two_scale_extra_configuration
import Theorems.Thm_StickyKakeya4_native_candidate_reference_admission
import Theorems.Thm_StickyKakeya4_native_all_two_scale_configuration
import Theorems.Thm_StickyKakeya4_native_two_scale_boundary_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeCandidateReferenceConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeFixedSizeScaleMenu NativeLocalMenuInterpolation NativeMiddleWindowBalance
open NativeTwoScaleConfiguration NativeConditionedPairMenu NativeMiddleTwoScaleConfiguration
open NativeTwoScaleBoundaryBalance NativeMasterPointRelations
open NativeAllTwoScaleConfiguration NativeMiddleTwoScaleExtraConfiguration
open NativeCandidateReferenceAdmission NativeAllTwoScaleExtraConfiguration NativeMiddleGrainParentBudget
open NativeLocalParentSource NativeRelativeCoarseReadback NativeNormalizedCellAngularMenu
open scoped BigOperators ENNReal


/-- The actual local source and angular upper at every installed middle
candidate, on the same E1 and original representative family. -/
def HasCandidateReferenceUpper {n G K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level : ℕ) (stops : Fin G → Fin (level+1)) (relativeDepth : Fin G → Fin K → ℕ)
    (E1 : Finset (Fin n × Index)) (Q : ℕ) (localEta window budget epsilon : ℝ) : Prop :=
  ∀i : Fin G,∀p : Parent,
    (parentEdges D a (2^(middleDepth (stops i).val)) E1 p).Nonempty →
    let m := middleDepth (stops i).val
    let E := parentEdges D a (2^m) E1 p
    IsWangZakharovNativeFiniteInput (source h R E a m p) localEta ∧
    (∀t,(source h R E a m p).line t∈fixedCompactClass) ∧
    ∀j : Fin K,relativeDepth i j ≤ level-m+6 →
      1/((2^(relativeDepth i j):ℕ):ℝ) ≤ (source h R E a m p).thickness^window →
      (source h R E a m p).thickness/(1/((2^(relativeDepth i j):ℕ):ℝ)) ≤
        (source h R E a m p).thickness^window →
    ∀T⊆E,∀q : Index,((angularMenu D a m (2^(relativeDepth i j)) p T q).card:ℝ) ≤
      81*(Q:ℝ)^4*(source h R E a m p).thickness^(-budget)*
        (64/((2^(relativeDepth i j):ℕ):ℝ))^(-extremalExponent-epsilon)

/-- Correct quantifier order for the coherence reference: choose the fixed
number K, the rank-dependent epsilon/window/budget, then this local engine;
only afterward choose tau and the single original source. Candidate relations
are installed before E1, and all returned costs retain the enlarged factor. -/
theorem exists_candidate_reference_configuration (hk : 0 < extremalExponent)
    (K : ℕ) (epsilon window budget : ℝ)
    (hepsilon : 0 < epsilon) (hwindow : 0 < window) (hbudget : 0 < budget) :
    ∃eRel localEta tauCap deltaRef : ℝ,
      0 < eRel ∧ eRel ≤ 32*budget/(7*window) ∧ 0 < localEta ∧ 0 < tauCap ∧
      0 < deltaRef ∧ deltaRef ≤ 1/8 ∧
      ∀tau : ℝ,∀htau : 0 < tau,tau ≤ tauCap →
    ∃ (seed e zeta : ℝ) (L g : ℕ),0 < seed ∧ seed ≤ tau/16384 ∧
      0 < e ∧ 0 < zeta ∧ zeta ≤ seed/256 ∧ 0 < L ∧ 0 < g ∧
      1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4 ∧
      ∀etaBound deltaBound : ℝ,0 < etaBound → 0 < deltaBound →
      ∃ (eta : ℝ) (n : ℕ) (D : FiniteScaleSource n)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0 < eta ∧ eta < etaBound ∧ eta < seed/8 ∧ D.thickness < deltaBound ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-eta) ∧
        D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n))
          (original : Fin n → Finset Index)
          (schedule : Fin (g+1) → Fin (level+1)),
          HasOriginalBackbone D original R a level zeta ∧ g ≤ level ∧
          schedule=fullSchedule tau htau g level ∧
          ∀relativeDepth : Fin (g+1) → Fin K → ℕ,
          let Extra := NativeReferenceRelativeMenu.relations h R a
            (fun i => middleDepth (schedule i).val) (fun i j => 2^(relativeDepth i j));
          ∃E : Finset (Fin n × Index),
          (∀i x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Extra i) E x ≤
            (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Extra i) E y) ∧
          IsCore D original R a eta zeta (menuSize (pairMenuSize (((g+1)+(g+1)*(K+K))+(1+(g+1))) (g+1)) (g+1)) (g+1) L
            (relationMenu h R a schedule (pairRelationMenu h R a schedule
              (NativeInitialExtraRelations.relations D a schedule Extra)))
            (fun j => 2^(schedule j).val) E ∧
          (125*175616*16384:ℝ)*(factor (menuSize (pairMenuSize (((g+1)+(g+1)*(K+K))+(1+(g+1))) (g+1)) (g+1)) (g+1) L:ℝ)*
            (coreRadix original R L:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)) ∧
          HasUniformFibers E (coreRadix original R L) Prod.snd ∧
          (∀j x y,x∈E → y∈E →
            degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^(schedule j).val)) E x ≤
              (coreRadix original R L)^2*
                degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^(schedule j).val)) E y) ∧
          (∀i j,HasUniformFibers E (coreRadix original R L)
              (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
            HasUniformFibers E (coreRadix original R L)
              (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val)) ∧
          (∀j,HasJointScale h R E a level (schedule j).val e zeta (seed/8) (seed/8) ∧
            HasBalancedScale h R E a level (schedule j).val seed) ∧
          (∀m : ℕ,boundaryWindow tau*(level:ℝ) ≤ m → (m:ℝ) ≤ (1-boundaryWindow tau)*(level:ℝ) →
            HasMiddleScale h R E a level m (tau/16)) ∧
          (∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E a level m f tau) ∧
          HasCandidateReferenceUpper h R a level schedule relativeDepth E (coreRadix original R L)
            localEta window budget epsilon := by
  obtain ⟨eRel,localEta,tauCap,deltaRef,heRel,heRelBound,hLocal,hTauCap,hDeltaRef,hDeltaRef1,Hnative⟩ :=
    exists_candidate_menu_angular_upper epsilon window budget hepsilon hwindow hbudget
  refine ⟨eRel,localEta,tauCap,deltaRef,heRel,heRelBound,hLocal,hTauCap,hDeltaRef,hDeltaRef1,?_⟩
  intro tau htau hTauCapBound
  obtain ⟨seed,e,zeta,L,g,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,Hsource⟩ :=
    exists_all_two_scale_extra_configuration hk tau htau (fun g => (g+1)+(g+1)*(K+K))
  refine ⟨seed,e,zeta,L,g,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,?_⟩
  intro etaBound deltaBound hetaBound hdeltaBound
  let cutoff := min deltaBound (min deltaRef ((2:ℝ)⁻¹^6))
  have hcutoff : 0 < cutoff := lt_min hdeltaBound (lt_min hDeltaRef (by positivity))
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hK,hvol,hnear,
    a,level,R,original,schedule,HB,hgl,hSchedule,Hselect⟩ := Hsource etaBound cutoff hetaBound hcutoff
  have hdeltaRef : D.thickness ≤ deltaRef :=
    (hsmall.le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hdeltaSix : D.thickness ≤ (2:ℝ)⁻¹^6 :=
    (hsmall.le.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hlevel : 6 ≤ level := depth_le_of_dyadic_cutoff level 6 HB.2.1 hdeltaSix
  refine ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall.trans_le (min_le_left _ _),hK,hvol,hnear,
    a,level,R,original,schedule,HB,hgl,hSchedule,?_⟩
  intro relativeDepth
  let Extra := NativeReferenceRelativeMenu.relations h R a
    (fun i => middleDepth (schedule i).val) (fun i j => 2^(relativeDepth i j))
  obtain ⟨E,hExtra,hCore,hCost,hPoint,hOld,hConditioned,hScales,hFirst,hPairs⟩ :=
    Hselect Extra
      (NativeReferenceRelativeMenu.relations_refl h R a _ _)
      (NativeReferenceRelativeMenu.relations_symm h R a _ _)
  refine ⟨E,hExtra,hCore,hCost,hPoint,hOld,hConditioned,hScales,hFirst,hPairs,?_⟩
  have hseedCap : seed ≤ tauCap := (show seed ≤ tau by linarith).trans hTauCapBound
  exact Hnative n D eta zeta seed a h hzeta.le hetaSeed.le hzseed hseedCap hdeltaRef
    original R level HB hlevel E hCore.1
    (factor (menuSize (pairMenuSize (((g+1)+(g+1)*(K+K))+(1+(g+1))) (g+1)) (g+1)) (g+1) L)
    (coreRadix original R L) (g+1) K schedule relativeDepth hCore.2.2.1 hExtra hCost

end NativeCandidateReferenceConfiguration
