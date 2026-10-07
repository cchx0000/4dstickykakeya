import Theorems.Thm_StickyKakeya4_native_retained_query_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7500000
noncomputable section

namespace NativeActualQueryRankConfiguration
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

def HasQuerySecondStageCore {n d K g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (queries : Fin K → ℕ × ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau : ℝ) (htau : 0 < tau) (c2 : ℝ)
    (ell : Fin 4) (j : Fin (g+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) : Prop :=
  (∀i,(queries i).2 ≤ (queries i).1 ∧ (queries i).1 ≤ level) ∧
  let r := radius (rankWindow tau) (rankWindow_pos htau).le g level j
  let lambda := r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1))
  let F1 := factor (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L
  let G := retentionCost ((d+K+K+K+1)+(g+1)*(g+1)) 1 L2
  let F2 := factor ((d+K+K+K+1)+(g+1)*(g+1)) 1 L2
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
        (∀i,HasUniformFibers E2 Q2 (fineQueryPair h R a level queries i)) ∧
        (∀i,HasUniformFibers E2 Q2 (shortQueryPair h R a level queries i)) ∧
        (∀i,HasUniformFibers E2 Q2 (rawQueryPoint D queries i)) ∧
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

/-- Decode a caller menu on its actual second-stage incidence set. Every
retention, richness, cost, plane and tuple field is preserved verbatim. -/
theorem decode_second_stage_queries {n d K g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (queries : Fin K → ℕ × ℕ)
    (hqueries : ∀i,(queries i).2 ≤ (queries i).1 ∧ (queries i).1 ≤ level)
    (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : HasSecondStageCore h original R E1 F P a level schedule L L2
      eta0 c tau htau c2 ell j (queryMenu h R a level queries Rel)) :
    HasQuerySecondStageCore h original R E1 F P a level queries schedule L L2
      eta0 c tau htau c2 ell j Rel := by
  obtain ⟨previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hU,hPoint2,hRows,hRich,hraw2,hPlane,hTuples⟩ := H
  obtain ⟨hOld,hFine,hShort,hRaw⟩ := queryMenu_uniformities h R a level queries Rel E2 _ hU
  exact ⟨hqueries,previous,hprevious,test,htest,hrq,hqr,hqlo,E2,hE2F,hE2ne,hE2old,hret2,hret,
    hnear2,hOld,hFine,hShort,hRaw,hPoint2,hRows,hRich,hraw2,hPlane,hTuples⟩

lemma stopping_depth_ge (m M : ℕ) (r : ℝ)
    (hidentity : 48*((2^m:ℕ):ℝ)*r=1)
    (hr : r ≤ 1/(48*((2^M:ℕ):ℝ))) : M ≤ m := by
  have hmul := mul_le_mul_of_nonneg_left hr (show 0 ≤ 48*((2^m:ℕ):ℝ) by positivity)
  rw [hidentity] at hmul
  have hM : (0:ℝ) < ((2^M:ℕ):ℝ) := by positivity
  have hp : (1:ℝ) ≤ ((2^m:ℕ):ℝ)/((2^M:ℕ):ℝ) := by
    calc
      _ ≤ 48*((2^m:ℕ):ℝ)*(1/(48*((2^M:ℕ):ℝ))) := hmul
      _ = _ := by field_simp
  have hN : ((2^M:ℕ):ℝ) ≤ ((2^m:ℕ):ℝ) := by
    simpa only [one_mul] using (le_div_iff₀ hM).mp hp
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp (by exact_mod_cast hN)

lemma grainDepth_strict_step (J stop : ℕ) (hJ : 0 < J)
    (hwide : J ≤ stop-min 6 stop) (i : Fin J) :
    grainDepth J stop i.castSucc < grainDepth J stop i.succ := by
  let len := stop-min 6 stop
  let lo := i.val*len/J
  have hlo : lo*J ≤ i.val*len := Nat.div_mul_le_self (i.val*len) J
  have hstep : lo+1 ≤ (i.val+1)*len/J := (Nat.le_div_iff_mul_le hJ).mpr (by dsimp [len] at *; nlinarith)
  change min 6 stop+lo < min 6 stop+(i.val+1)*len/J
  omega

lemma stopping_depth_six (m : ℕ) (r : ℝ)
    (hidentity : 48*((2^m:ℕ):ℝ)*r=1) (hr : r ≤ 1/3072) : 6 ≤ m := by
  have hmul := mul_le_mul_of_nonneg_left hr (show 0 ≤ 48*((2^m:ℕ):ℝ) by positivity)
  rw [hidentity] at hmul
  have hN : (64:ℝ) ≤ ((2^m:ℕ):ℝ) := by nlinarith
  have hNat : (2:ℕ)^6 ≤ 2^m := by
    norm_num only [Nat.reducePow]
    exact_mod_cast hN
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2:ℕ))).mp hNat

/-- The physical spatial scale at the stopping depth retains its exact
normalization relative to the direction-selection radius. -/
lemma stopping_physical_scale (m : ℕ) (r : ℝ)
    (hidentity : 48*((2^m:ℕ):ℝ)*r=1) : 64/((2^m:ℕ):ℝ)=3072*r := by
  apply (div_eq_iff (show ((2^m:ℕ):ℝ) ≠ 0 by positivity)).mpr
  nlinarith

/-- Fixed query count, before tau and the source; adaptive actual query depths,
after the rank cut. A harmless source cutoff also places the stopping depth
at least K+6, so its independent grain menu has strictly increasing depths
and physical widths at most one. -/
theorem exists_actual_query_rank_configuration (d K : ℕ) (hk : 0 < extremalExponent)
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
                K+6 ≤ (schedule j).val ∧
                ∀ queries : Fin K → ℕ × ℕ,
                  (∀i,(queries i).2 ≤ (queries i).1 ∧ (queries i).1 ≤ level) →
                ∀ Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
                  (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
                  HasQuerySecondStageCore h original R E1 F P a level queries schedule L L2
                    eta0 c tau htau c2 ell j Rel := by
  obtain ⟨tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,hc2,hbase⟩ :=
    exists_actual_retained_rank_configuration (d+K+K+K) hk eta0 c he0 heK hc hcsmall tauBound hTauBound
  obtain ⟨dGrain,hdGrain,_hdGrain1,hGrain⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < c^3/8 by positivity) (by norm_num : (0:ℝ)≤1) (by positivity : (0:ℝ)<1/(48*((2^(K+6):ℕ):ℝ)))
  refine ⟨tau,htau,seed,e,zeta,L,g,L2,c2,htauB,htauT,htauHalf,hseed,hseedTau,
    he,hzeta,hzseed,hL,hg,hgrid,hL2,hc2,?_⟩
  intro etaBound deltaBound heB hdB
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hSelect⟩ :=
    hbase etaBound (min deltaBound dGrain) heB (lt_min hdB hdGrain)
  have hsmallG : D.thickness ≤ dGrain := hsmall.le.trans (min_le_right _ _)
  have hpower : D.thickness^(c^3/8) ≤ 1/(48*((2^(K+6):ℕ):ℝ)) := by
    simpa only [one_mul] using hGrain D.thickness h.1.2.1 hsmallG
  have hrcap : radius (rankWindow tau) (rankWindow_pos htau).le g level j ≤ 1/(48*((2^(K+6):ℕ):ℝ)) :=
    hrcut.trans ((Real.rpow_le_rpow_of_exponent_ge h.1.2.1 h.1.2.2.1
      (cutoff_bounds hc (by linarith) ell).2.2).trans hpower)
  have hstop6 := stopping_depth_ge (schedule j).val (K+6) _ hidentity hrcap
  refine ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall.trans_le (min_le_left _ _),hK,hvol,hnear,
    a,level,R,original,E1,schedule,hBackbone,hgl,hSchedule,hCore,hCost1,
    hPoint,hOld,hConditioned,hScales,hMiddle,hAllPairs,hE1Near,
    ell,j,hell,hjmenu,hrcut,hrlo,hrhi,hidentity,hscale,hrsquare,
    F,hFE1,hFn,hrank,P,hnearP,hpoints,hstop6,?_⟩
  intro queries hqueries Rel hrefl hsym
  exact decode_second_stage_queries h original R E1 F P a level queries hqueries schedule L L2
    eta0 c tau htau c2 ell j Rel
    (hSelect (queryMenu h R a level queries Rel) (queryMenu_refl h R a level queries Rel hrefl)
      (queryMenu_symm h R a level queries Rel hsym))

/-- Specialize the finite query field to a separate J-level grain schedule
built from the actual selected stopping depth. J is not the master count g. -/
theorem select_grain_second_stage {n d J g : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (E1 F : Finset (Fin n × Index))
    (P : Index → Submodule ℝ E4) (a : ℝ) (level : ℕ)
    (schedule : Fin (g+1) → Fin (level+1)) (L L2 : ℕ)
    (eta0 c tau : ℝ) (htau : 0 < tau) (c2 : ℝ) (ell : Fin 4) (j : Fin (g+1))
    (H : ∀ queries : Fin (J+1) → ℕ × ℕ,
      (∀i,(queries i).2 ≤ (queries i).1 ∧ (queries i).1 ≤ level) →
      ∀ Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop,
      (∀i x,Rel i x x) → (∀i x y,Rel i x y → Rel i y x) →
      HasQuerySecondStageCore h original R E1 F P a level queries schedule L L2
        eta0 c tau htau c2 ell j Rel)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (hrefl : ∀i x,Rel i x x) (hsym : ∀i x y,Rel i x y → Rel i y x) :
    HasQuerySecondStageCore h original R E1 F P a level (grainQueries J (schedule j).val) schedule L L2
      eta0 c tau htau c2 ell j Rel :=
  H _ (grainQueries_valid J (schedule j).val (Nat.le_of_lt_succ (schedule j).isLt)) Rel hrefl hsym

end NativeActualQueryRankConfiguration
