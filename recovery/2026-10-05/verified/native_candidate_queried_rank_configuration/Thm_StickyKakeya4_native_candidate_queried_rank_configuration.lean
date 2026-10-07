import Theorems.Thm_StickyKakeya4_native_generic_query_rank
import Theorems.Thm_StickyKakeya4_native_candidate_reference_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeCandidateQueriedRankConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeAllTwoScaleConfiguration NativeActualMesoscopicRankConfiguration NativeRankExponentHierarchy
open NativeGenericReferenceData NativeGenericReferenceRank NativeGenericReferenceSecondStage NativeGenericQueryRank
open NativeCandidateReferenceConfiguration NativeMiddleGrainParentBudget
open scoped ENNReal

/-- The actual candidate-enriched original source followed by its genuine rank
cut and second refinement. Krelative and Kquery are fixed before the rank
parameters. eta0/c precede the relative engine; tau, seed, g, L and both source
cutoffs follow it. Every later E2 is a subset of this exact enlarged E1. -/
theorem exists_candidate_queried_rank_configuration (d Kquery Krelative : ℕ)
    (hk : 0 < extremalExponent) (eta0 c : ℝ)
    (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent/2) (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (epsilon window budget : ℝ) (hepsilon : 0 < epsilon) (hwindow : 0 < window) (hbudget : 0 < budget)
    (tauBound : ℝ) (hTauBound : 0 < tauBound) :
    ∃eRel localEta : ℝ,0 < eRel ∧ eRel ≤ 32*budget/(7*window) ∧ 0 < localEta ∧
    ∃(tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g L2 : ℕ),
      tau ≤ tauBound ∧ tau ≤ commonBudget eta0 c/1024 ∧ tau ≤ 1/2 ∧ tau ≤ c^3/8 ∧
      0 < seed ∧ seed ≤ tau/16384 ∧ 0 < e ∧ 0 < zeta ∧ zeta ≤ seed/256 ∧
      0 < L ∧ 0 < g ∧ 1/(g:ℝ) < rankWindow tau/4 ∧ 0 < L2 ∧
      ∀relativeDepth : (level : ℕ) → (Fin (g+1) → Fin (level+1)) → Fin (g+1) → Fin Krelative → ℕ,
      ∀etaBound deltaBound : ℝ,0 < etaBound → 0 < deltaBound →
      ∃(eta : ℝ) (n : ℕ) (D : FiniteScaleSource n) (h : IsWangZakharovNativeFiniteInput D eta),
        0 < eta ∧ eta < etaBound ∧ eta < seed/8 ∧ D.thickness < deltaBound ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-eta) ∧
        D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.dimension=menuSize (pairMenuSize
            (((g+1)+(g+1)*(Krelative+Krelative))+(1+(g+1))) (g+1)) (g+1) ∧
          HasCandidateReferenceUpper h ref.R ref.a ref.level ref.schedule
            (relativeDepth ref.level ref.schedule) ref.E1 (coreRadix ref.original ref.R L)
            localEta window budget epsilon ∧
          D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1 ∧
          HasQueriedRankSelection ref d Kquery L2 eta0 c (commonBudget eta0 c/4) := by
  obtain ⟨eRel,localEta,tauCap,deltaRef,heRel,heRelBound,hLocal,hTauCap,_hDeltaRef,_hDeltaRef1,Hcandidate⟩ :=
    exists_candidate_reference_configuration hk Krelative epsilon window budget hepsilon hwindow hbudget
  let t := commonBudget eta0 c
  have ht : 0 < t := commonBudget_pos he0 hc
  let tau := min tauBound (min tauCap (min (t/1024) (min (1/2) (c^3/8))))
  have htau : 0 < tau := lt_min hTauBound (lt_min hTauCap (lt_min (by positivity)
    (lt_min (by norm_num) (by positivity))))
  have hTauBound' : tau ≤ tauBound := min_le_left _ _
  have hInner := min_le_right tauBound (min tauCap (min (t/1024) (min (1/2) (c^3/8))))
  have hTauCap' : tau ≤ tauCap := hInner.trans (min_le_left _ _)
  have hTauRest : tau ≤ min (t/1024) (min (1/2) (c^3/8)) := hInner.trans (min_le_right _ _)
  have hTauT : tau ≤ t/1024 := hTauRest.trans (min_le_left _ _)
  have hTauRest' : tau ≤ min (1/2) (c^3/8) := hTauRest.trans (min_le_right _ _)
  have hTauHalf : tau ≤ 1/2 := hTauRest'.trans (min_le_left _ _)
  have hTauC : tau ≤ c^3/8 := hTauRest'.trans (min_le_right _ _)
  obtain ⟨seed,e,zeta,L,g,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,Hsource⟩ := Hcandidate tau htau hTauCap'
  obtain ⟨dRank,hdRank,Hrank⟩ := exists_rank_selection_cutoff hk eta0 c he0 heK hc hcsmall
    tau htau hTauT hTauHalf seed hseed hsTau g hg hgrid
  obtain ⟨L2,hL2,dSecond,hdSecond,Hsecond⟩ := exists_second_stage_cutoff (d+Kquery+Kquery+Kquery)
    eta0 c he0 hc hcsmall tau htau hTauT hTauHalf hTauC seed hsTau g hg hgrid
  obtain ⟨dQuery,hdQuery,Hquery⟩ := exists_query_depth_cutoff Kquery c hc hcsmall
  refine ⟨eRel,localEta,heRel,heRelBound,hLocal,tau,htau,seed,e,zeta,L,g,L2,
    hTauBound',hTauT,hTauHalf,hTauC,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,hL2,?_⟩
  intro relativeDepth etaBound deltaBound hetaBound hdeltaBound
  let etaCut := min etaBound ((commonBudget eta0 c/4)/4)
  let deltaCut := min deltaBound (min dRank (min dSecond dQuery))
  have hEtaCut : 0 < etaCut := lt_min hetaBound (by dsimp [t] at ht; positivity)
  have hDeltaCut : 0 < deltaCut := lt_min hdeltaBound (lt_min hdRank (lt_min hdSecond hdQuery))
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hK,hvol,hnear,
    a,level,R,original,schedule,HB,hgl,hSchedule,Hselect⟩ := Hsource etaCut deltaCut hEtaCut hDeltaCut
  have hEtaBound : eta < etaBound := hetaB.trans_le (min_le_left _ _)
  have hEtaSecond : eta ≤ (commonBudget eta0 c/4)/4 := (hetaB.trans_le (min_le_right _ _)).le
  have hCuts : D.thickness ≤ deltaBound ∧ D.thickness ≤ dRank ∧
      D.thickness ≤ dSecond ∧ D.thickness ≤ dQuery := by
    simpa only [deltaCut,le_min_iff] using hsmall.le
  obtain ⟨E,hExtra,hCore,hCost,hPoint,hOld,hConditioned,hScales,hFirst,hPairs,hCandidate⟩ :=
    Hselect (relativeDepth level schedule)
  let ref : Reference h tau htau seed e zeta L g := {
    a:=a, level:=level, R:=R, original:=original, E1:=E, schedule:=schedule,
    dimension:=menuSize (pairMenuSize (((g+1)+(g+1)*(Krelative+Krelative))+(1+(g+1))) (g+1)) (g+1),
    relations:=relationMenu h R a schedule (pairRelationMenu h R a schedule
      (NativeInitialExtraRelations.relations D a schedule
        (NativeReferenceRelativeMenu.relations h R a (fun i => middleDepth (schedule i).val)
          (fun i j => 2^(relativeDepth level schedule i j))))),
    backbone:=HB, grid_depth:=hgl, schedule_eq:=hSchedule, core:=hCore, cost:=hCost,
    point:=hPoint, parent_point:=hOld, conditioned:=hConditioned, scales:=hScales,
    middle:=hFirst, pairs:=hPairs }
  obtain ⟨hNearE,HrankE⟩ := Hrank n D eta h heta.le hetaSeed.le hCuts.2.1 e zeta L ref hnear
  have HsecondE := Hsecond n D eta h heta.le hEtaSecond hCuts.2.2.1 e zeta L ref HrankE
  have HqueryE := Hquery n D eta tau seed e zeta h htau L g ref d L2 eta0 (commonBudget eta0 c/4)
    hCuts.2.2.2 HsecondE
  exact ⟨eta,n,D,h,heta,hEtaBound,hetaSeed,hsmall.trans_le (min_le_left _ _),hK,hvol,hnear,
    ref,rfl,hCandidate,hNearE,HqueryE⟩

end NativeCandidateQueriedRankConfiguration
