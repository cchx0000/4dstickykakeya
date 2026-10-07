import Theorems.Thm_StickyKakeya4_native_retained_rank_cutoffs
import Theorems.Thm_StickyKakeya4_native_refined_row_relations

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7500000
noncomputable section

namespace NativeActualRetainedRankConfiguration
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

/-- The literal second incidence set, its actual costs, and the actual tuples.
The same original labels, backbone, representatives and stopping plane survive. -/
def HasSecondStageCore {n d g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau : ℝ) (htau : 0 < tau) (c2 : ℝ)
    (ell : Fin 4) (j : Fin (g+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let lambda := r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1))
  let F1 := factor (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L
  let G := retentionCost ((d+1)+(g+1)*(g+1)) 1 L2
  let F2 := factor ((d+1)+(g+1)*(g+1)) 1 L2
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
              q^(2*(ell.val+1)) ≤ (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det

/-- All geometric hierarchy and source cutoffs precede the actual source.
Every supplied finite symmetric/reflexive relation menu receives one actual
second refinement, with its cost and transverse tuples proved internally. -/
theorem exists_actual_retained_rank_configuration (d : ℕ) (hk : 0 < extremalExponent)
    (eta0 c : ℝ) (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent / 2)
    (hc : 0 < c) (hcsmall : c ≤ 1 / 2) (tauBound : ℝ) (hTauBound : 0 < tauBound) :
    ∃ (tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g L2 : ℕ) (c2 : ℝ),
      tau ≤ tauBound ∧ tau ≤ commonBudget eta0 c / 1024 ∧ tau ≤ 1 / 2 ∧
      0 < seed ∧ seed ≤ tau / 16384 ∧ 0 < e ∧ 0 < zeta ∧
      zeta ≤ seed / 256 ∧ 0 < L ∧ 0 < g ∧
      1 / (g : ℝ) < rankWindow tau / 4 ∧
      0 < L2 ∧ c2=commonBudget eta0 c/4 ∧
      ∀ etaBound deltaBound : ℝ, 0 < etaBound → 0 < deltaBound →
      ∃ (eta : ℝ) (n : ℕ) (D : FiniteScaleSource n)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0 < eta ∧ eta < etaBound ∧ eta < seed / 8 ∧ D.thickness < deltaBound ∧
        (∀ i, D.line i ∈ fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent - eta) ∧
        D.thickness ^ (-extremalExponent + eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n))
          (original : Fin n → Finset Index) (E1 : Finset (Fin n × Index))
          (schedule : Fin (g + 1) → Fin (level + 1)),
          HasOriginalBackbone D original R a level zeta ∧ g ≤ level ∧
          schedule = fullSchedule tau htau g level ∧
          IsCore D original R a eta zeta (menuSize (pairMenuSize (1 + (g + 1)) (g + 1)) (g + 1))
            (g + 1) L (relationMenu h R a schedule (pairRelationMenu h R a schedule
              (masterRelations D a schedule))) (fun j => 2 ^ (schedule j).val) E1 ∧
          (125 * 175616 * 16384 : ℝ) *
            (factor (menuSize (pairMenuSize (1 + (g + 1)) (g + 1)) (g + 1)) (g + 1) L : ℝ) *
            (coreRadix original R L : ℝ) ^ 2 * D.thickness ^ (-eta) ≤ D.thickness ^ (-(seed / 8)) ∧
          HasUniformFibers E1 (coreRadix original R L) Prod.snd ∧
          (∀ j x y, x ∈ E1 → y ∈ E1 →
            degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2 ^ (schedule j).val)) E1 x ≤
              (coreRadix original R L) ^ 2 *
                degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2 ^ (schedule j).val)) E1 y) ∧
          (∀ i j, HasUniformFibers E1 (coreRadix original R L)
              (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
            HasUniformFibers E1 (coreRadix original R L)
              (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val)) ∧
          (∀ j, HasJointScale h R E1 a level (schedule j).val e zeta (seed / 8) (seed / 8) ∧
            HasBalancedScale h R E1 a level (schedule j).val seed) ∧
          (∀ m : ℕ, boundaryWindow tau * (level : ℝ) ≤ m →
            (m : ℝ) ≤ (1 - boundaryWindow tau) * (level : ℝ) →
            HasMiddleScale h R E1 a level m (tau / 16)) ∧
          (∀ m f : ℕ, m ≤ f → f ≤ level → HasConditionalTwoScale h R E1 a level m f tau) ∧
          D.thickness ^ (-extremalExponent + seed / 4) ≤
            NativeIncidenceMultiplicityTower.multiplicity E1 ∧
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
                ∀ Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  HasSecondStageCore h original R E1 F P a level schedule L L2
                    eta0 c tau htau c2 ell j Rel := by
  have hc1 : c ≤ 1 := by linarith
  have hmin : 0 < min tauBound (c^3/8) := lt_min hTauBound (by positivity)
  obtain ⟨tau,htau,seed,e,zeta,L,g,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hbase⟩ :=
    exists_actual_mesoscopic_rank_configuration hk eta0 c he0 heK hc hcsmall
      (min tauBound (c^3/8)) hmin
  have htauOrig : tau ≤ tauBound := htauB.trans (min_le_left _ _)
  have htauC : tau ≤ c^3/8 := htauB.trans (min_le_right _ _)
  let c2 := commonBudget eta0 c/4
  have hc2 : 0 < c2 := div_pos (commonBudget_pos he0 hc) (by norm_num)
  have hgap : seed/8+c2 < commonBudget eta0 c := by
    have ht := commonBudget_pos he0 hc
    dsimp [c2]
    linarith
  let d2 := (d+1)+(g+1)*(g+1)
  obtain ⟨L2,hL2,dCost,hdCost,_hdCost1,hCost2⟩ :=
    exists_second_refinement_cost c2 hc2 d2 1
  obtain ⟨dHalf,hdHalf,_hdHalf1,hHalf⟩ :=
    exists_rank_half_mass_cutoff he0 hc g hgap
  obtain ⟨dRound,hdRound,_hdRound1,hRound⟩ :=
    exists_rank_rounding_cutoff hc hc1 htau htauC
  refine ⟨tau,htau,seed,e,zeta,L,g,L2,c2,htauOrig,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,rfl,?_⟩
  intro etaBound deltaBound heB hdB
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints⟩ :=
    hbase (min etaBound (c2/4)) (min deltaBound (min dCost (min dHalf (min dRound (1/8)))))
      (lt_min heB (by positivity))
      (lt_min hdB (lt_min hdCost (lt_min hdHalf (lt_min hdRound (by norm_num)))))
  have hetaB' : eta < etaBound := hetaB.trans_le (min_le_left _ _)
  have hetaC : eta ≤ c2/4 := (lt_min_iff.mp hetaB).2.le
  have hcuts : D.thickness ≤ deltaBound ∧ D.thickness ≤ dCost ∧
      D.thickness ≤ dHalf ∧ D.thickness ≤ dRound ∧ D.thickness ≤ 1/8 := by
    simpa only [le_min_iff] using hsmall.le
  refine ⟨eta,n,D,h,heta,hetaB',hetaSeed,hsmall.trans_le (min_le_left _ _),hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,?_⟩
  intro Rel hrefl hsym
  let w := rankWindow tau
  have hw : 0 < w := rankWindow_pos htau
  have hwTau : w ≤ tau/1000 := (min_le_left _ _).trans (min_le_left _ _)
  have hwsmall : w < 1/2 := by linarith
  let r := radius w hw.le g level j
  let lambda := r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1))
  let F1 := factor (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L
  let G := retentionCost d2 1 L2
  let F2 := factor d2 1 L2
  let Q1 := coreRadix original R L
  let Q2 := NativeSourceSizeBounds.radix F.card L2
  have hr : 0 < r := radius_pos w hw.le g level j
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hF1 : 0 < F1 := by
    dsimp [F1,factor,retentionCost,menuSize,pairMenuSize]
    positivity
  have hG : (0:ℝ) ≤ G := Nat.cast_nonneg _
  have hGF : (G:ℝ) ≤ F2 := by
    exact_mod_cast retained_cost_le_factor d2 1 L2 (by omega)
  have hForiginal : F ⊆ incidences original :=
    hFE1.trans (hCore.1.trans (filter_subset _ _))
  have hraw2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤
      D.thickness^(-c2) := hCost2 n D eta h hcuts.2.1 hetaC original hBackbone.1
        F hForiginal hFn
  let previous : Fin 4 := ⟨ell.val-1,by omega⟩
  have hprevious : previous.val+1=ell.val := by dsimp [previous]; omega
  obtain ⟨hbeta,hbeta1,hcompat,hgapRank⟩ := test_parameters he0 hc hcsmall previous ell hprevious
  have hlarge := large_level_of_grid w hw g level hg hgrid hgl
  obtain ⟨test,htest,hrq,hqr,hqlo⟩ := exists_mesoscopic_test_radius_of_cutoff
    w hw hwsmall g level hg hlarge hBackbone.2.1 j hjmenu
    (cutoff c ell) (cutoff c previous) (2*c) hbeta hbeta1 hrcut hcompat
    (hRound D.thickness h.1.2.1 hcuts.2.2.2.1 previous ell hprevious)
  let q := radius w hw.le g level test
  have hq : 0 < q := radius_pos w hw.le g level test
  obtain ⟨E2,hE2F,hE2ne,hE2old,hret2,hnear2,hU,hRows,hRich⟩ :=
    exists_refined_row_core h original hBackbone.1 hBackbone.2.2.1 hcuts.2.2.2.2
      hBackbone.2.1 R E1 F hCore.1 hCore.2.1 hFE1 F1 hF1 hCore.2.2.1
      lambda hlambda hrank L2 hL2 schedule (finePointMenu Rel)
      (finePointMenu_refl Rel hrefl) (finePointMenu_symm Rel hsym)
  obtain ⟨hCaller,hPoint2⟩ := finePointMenu_uniformities Rel E2 Q2 hU
  have hret2R : (F.card:ℝ) ≤ (G:ℝ)*E2.card := by exact_mod_cast hret2
  have hret : lambda*(E1.card:ℝ) ≤ (G:ℝ)*E2.card := hrank.trans hret2R
  have hbudget : q^(rankLoss eta0 c previous)*(G:ℝ)*(Q1:ℝ)^2*(Q2:ℝ)^2 ≤ lambda/2 :=
    hHalf D.thickness h.1.2.1 hcuts.2.2.1 ell F1 F2 Q1 Q2 hF1
      eta eta G r q (2*c) (rankLoss eta0 c previous) heta.le heta.le hG hGF
      hr (by dsimp [r]; linarith) hrcut hq.le (rankLoss_pos he0 hc previous).le hqr hgapRank
      hCost1 hraw2
  let allowed := fun i : Fin 4 => NativeRankMesoscopicRadiusMenu.allowed D.thickness
    w hw.le g level (cutoff c i)
  have Hfailed : ∀k∈F.image Prod.snd,∀i : Fin 4,i<ell →
      ∀t∈allowed i,∀Q : Submodule ℝ E4,Module.finrank ℝ Q ≤ i.val+1 →
      ((pointNear D E1 k (radius w hw.le g level t) Q).card:ℝ) <
        (radius w hw.le g level t)^(rankLoss eta0 c i)*((pointSet E1 k).card:ℝ) := by
    intro k hkF i hi t ht Q hQ
    obtain ⟨htM,htC⟩ := mem_filter.mp ht
    exact (hpoints k hkF).2.2.2 i hi t htM htC Q hQ
  have hPlane := previous_rank_menu_plane_rank D E1 F E2 hFE1 hE2F Q1 Q2 hPoint hPoint2
    lambda G hlambda hG hret ell previous hprevious P r
    (fun k hkF => (hpoints k hkF).1) hnearP allowed (radius w hw.le g level)
    (rankLoss eta0 c) test htest hq hrq Hfailed hbudget
  have hTuples := previous_rank_menu_transverse_chains D E1 F E2 hFE1 hE2F Q1 Q2 hPoint hPoint2
    lambda G hlambda hG hret ell previous hprevious allowed (radius w hw.le g level)
    (rankLoss eta0 c) test htest hq Hfailed hbudget
  exact ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hCaller,hPoint2,hRows,hRich,hraw2,hPlane,hTuples⟩

end NativeActualRetainedRankConfiguration
