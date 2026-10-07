import Theorems.Thm_StickyKakeya4_native_all_two_scale_configuration
import Theorems.Thm_StickyKakeya4_native_rank_mesoscopic_radius_menu
import Theorems.Thm_StickyKakeya4_native_rank_exponent_hierarchy
import Theorems.Thm_StickyKakeya4_native_reference_core_global_near
import Theorems.Thm_StickyKakeya4_native_rank_one_excluded_from_source_cost
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000
noncomputable section

namespace NativeActualMesoscopicRankConfiguration
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

/-- The exact clipped window already used by the full master schedule. -/
def rankWindow (tau : ℝ) : ℝ := min (boundaryWindow tau) ((tau / 16) / 1000)

lemma rankWindow_pos {tau : ℝ} (htau : 0 < tau) : 0 < rankWindow tau :=
  lt_min (boundaryWindow_pos htau) (by positivity)

lemma fullSchedule_eq_rankWindow (tau : ℝ) (htau : 0 < tau) (g level : ℕ) :
    fullSchedule tau htau g level =
      windowSchedule (rankWindow tau) (rankWindow_pos htau).le g level := rfl

/-- An actual positive-critical-exponent source, its unchanged full original
reference and all master estimates, together with a literal mesoscopic rank
cut of rank two, three, or four. The hierarchy is fixed before the master
tolerance, which also obeys an arbitrary previously chosen caller bound;
every additional cutoff is fixed before the source is requested.
The original core's near bound and the exclusion of rank one are derived. -/
theorem exists_actual_mesoscopic_rank_configuration (hk : 0 < extremalExponent)
    (eta0 c : ℝ) (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent / 2)
    (hc : 0 < c) (hcsmall : c ≤ 1 / 2) (tauBound : ℝ) (hTauBound : 0 < tauBound) :
    ∃ (tau : ℝ) (htau : 0 < tau) (seed e zeta : ℝ) (L g : ℕ),
      tau ≤ tauBound ∧ tau ≤ commonBudget eta0 c / 1024 ∧ tau ≤ 1 / 2 ∧
      0 < seed ∧ seed ≤ tau / 16384 ∧ 0 < e ∧ 0 < zeta ∧
      zeta ≤ seed / 256 ∧ 0 < L ∧ 0 < g ∧
      1 / (g : ℝ) < rankWindow tau / 4 ∧
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
                ∀ k ∈ F.image Prod.snd,
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
                          ((pointSet E1 k).card : ℝ) := by
  let t := commonBudget eta0 c
  have ht : 0 < t := commonBudget_pos he0 hc
  let tau := min tauBound (min (t / 1024) (1 / 2))
  have htau : 0 < tau := lt_min hTauBound (lt_min (by positivity) (by norm_num))
  have htauB : tau ≤ tauBound := min_le_left _ _
  have htauInner : tau ≤ min (t / 1024) (1 / 2) := min_le_right _ _
  have htauT : tau ≤ t / 1024 := htauInner.trans (min_le_left _ _)
  have htauHalf : tau ≤ 1 / 2 := htauInner.trans (min_le_right _ _)
  have hc1 : c ≤ 1 := by linarith
  obtain ⟨seed, e, zeta, L, g, hseed, hseedTau, he, hzeta, hzseed, hL, hg, hgrid, hbase⟩ :=
    exists_all_two_scale_configuration hk tau htau
  let w := rankWindow tau
  have hw : 0 < w := rankWindow_pos htau
  have hgridW : 1 / (g : ℝ) < w / 4 := hgrid
  have hwTau : w ≤ tau / 1000 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hwsmall : w < 1 / 8 := by linarith
  have hpower0 : 0 < cutoff c (0 : Fin 4) := (cutoff_bounds hc hc1 0).1
  have hG : (0 : ℝ) < 4 * ((g : ℝ) + 1) := by positivity
  have hmargin : t ≤ cutoff c (0 : Fin 4) * extremalExponent / 2 := rank_one_power_margin hc heK
  have hgap : seed / 8 < cutoff c (0 : Fin 4) * extremalExponent / 2 - seed - seed / 4 := by
    linarith
  obtain ⟨dRank, hdRank, _hdRank1, hExclude⟩ :=
    exists_actual_rank_one_exclusion (theta := seed) (nu := seed / 4) (b := seed / 8)
      hk hpower0 hG hgap
  obtain ⟨dGeom, hdGeom, _hdGeom1, hGeom⟩ := exists_positive_rpow_absorption_threshold
    (half_pos hw) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1 / 48)
  obtain ⟨dSquare, hdSquare, _hdSquare1, hSquare⟩ := exists_positive_rpow_absorption_threshold
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) < 1 / 147456)
  refine ⟨tau, htau, seed, e, zeta, L, g, htauB, htauT, htauHalf, hseed, hseedTau,
    he, hzeta, hzseed, hL, hg, hgridW, ?_⟩
  intro etaBound deltaBound heB hdB
  obtain ⟨eta, n, D, h, heta, hetaB, hetaSeed, hsmall, hK, hvol, hnear,
    a, level, R, original, E1, schedule, hBackbone, hgl, hSchedule, hCore, hCost,
    hPoint, hOld, hConditioned, hScales, hMiddle, hAllPairs⟩ :=
    hbase etaBound (min deltaBound (min dRank (min dGeom dSquare))) heB
      (lt_min hdB (lt_min hdRank (lt_min hdGeom hdSquare)))
  have hcuts : D.thickness ≤ deltaBound ∧ D.thickness ≤ dRank ∧
      D.thickness ≤ dGeom ∧ D.thickness ≤ dSquare := by
    simpa only [le_min_iff] using hsmall.le
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have horiginal := hBackbone.1
  have hdy := hBackbone.2.1
  have ha := hBackbone.2.2.1
  have hE1 : E1 ⊆ incidences original := hCore.1.trans (filter_subset _ _)
  have hFactor : 0 < factor (menuSize (pairMenuSize (1 + (g + 1)) (g + 1)) (g + 1)) (g + 1) L := by
    unfold factor NativeLocalPairUniformCore.retentionCost menuSize pairMenuSize
    positivity
  have hCoreNear := core_global_near h heta.le original horiginal R E1 _ _ L _ _ hCore hCost hnear
  have hE1Near : D.thickness ^ (-extremalExponent + seed / 4) ≤
      NativeIncidenceMultiplicityTower.multiplicity E1 := by
    exact (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith :
      -extremalExponent + eta + seed / 8 ≤ -extremalExponent + seed / 4)).trans hCoreNear
  have hlarge := large_level_of_grid w hw g level hg hgridW hgl
  have hgeom : D.thickness ^ (w / 2) ≤ 1 / 48 := by
    simpa only [one_mul] using hGeom D.thickness hd hcuts.2.2.1
  have hsquare : D.thickness ^ (1 / 2 : ℝ) ≤ 1 / 147456 := by
    simpa only [one_mul] using hSquare D.thickness hd hcuts.2.2.2
  obtain ⟨ell, j, hjmenu, hradius, hrlo, hrhi, hidentity, hscale, hrsquare,
    F, hFE1, hFn, hret, P, hnearP, hpoints⟩ :=
    NativeRankMesoscopicRadiusMenu.exists_mesoscopic_rank_retention D E1 hCore.2.1
      w hw hwsmall g level hg hgridW hlarge hdy hgeom hsquare
      (cutoff c) (rankLoss eta0 c)
      (fun i => ⟨(cutoff_bounds hc hc1 i).1, (cutoff_bounds hc hc1 i).2.1⟩)
      (rankLoss_pos he0 hc)
  have hScheduleW : schedule = windowSchedule w hw.le g level := by
    rw [hSchedule, fullSchedule_eq_rankWindow]
  have hFormal : HasUniformFibers E1 (coreRadix original R L)
      (formalPair D a (schedule j).val) := by
    intro x hx y hy
    have hh := hOld j x y hx hy
    change degree (fun _ : Fin n × Index => 1)
      (fun x y => formalPair D a (schedule j).val x = formalPair D a (schedule j).val y) E1 x ≤
      (coreRadix original R L) ^ 2 * degree (fun _ : Fin n × Index => 1)
        (fun x y => formalPair D a (schedule j).val x = formalPair D a (schedule j).val y) E1 y at hh
    simpa only [unit_degree_eq_fiber] using hh
  have hParent : ∀ p, (parentEdges D a (2 ^ (schedule j).val) E1 p).Nonempty →
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2 ^ (schedule j).val) E1 p) ≤
        D.thickness ^ (-seed) *
          (((2 ^ (schedule j).val : ℕ) : ℝ) * D.thickness / 64) ^ (-extremalExponent) := by
    intro p hp
    exact ((hScales j).2.2.2 p hp).2.2.2
  have hell : 1 ≤ ell.val := by
    by_contra hnot
    have hv : ell.val = 0 := by omega
    have hzero : ell = (0 : Fin 4) := Fin.ext hv
    have hdim : ∀ k ∈ F.image Prod.snd, Module.finrank ℝ (P k) ≤ 1 := by
      intro k hkF
      simpa only [hv, zero_add] using (hpoints k hkF).1
    have hradius0 : radius w hw.le g level j ≤ D.thickness ^ (cutoff c (0 : Fin 4)) := by
      simpa only [hzero] using hradius
    have hstop0 : rankLoss eta0 c (0 : Fin 4) ≤ extremalExponent / 2 := by
      simpa [NativeRankExponentHierarchy.rankLoss] using heK
    have hidentityS : 48 * ((2 ^ (schedule j).val : ℕ) : ℝ) * radius w hw.le g level j = 1 := by
      simpa only [hScheduleW] using hidentity
    have hret0 : (radius w hw.le g level j) ^ (rankLoss eta0 c (0 : Fin 4)) /
        (4 * ((g : ℝ) + 1)) * (E1.card : ℝ) ≤ (F.card : ℝ) := by
      simpa only [hzero] using hret
    exact hExclude n D eta a heta.le h hcuts.2.1 original horiginal ha E1 F hE1 hFE1
      (schedule j).val (coreRadix original R L)
      (factor (menuSize (pairMenuSize (1 + (g + 1)) (g + 1)) (g + 1)) (g + 1) L)
      hFactor hCost (radius w hw.le g level j) (rankLoss eta0 c (0 : Fin 4))
      (radius_pos w hw.le g level j) hrhi hrlo hradius0 hstop0 hidentityS P hdim hnearP
      hFormal hParent hret0 hE1Near
  refine ⟨eta, n, D, h, heta, hetaB, hetaSeed,
    hsmall.trans_le (min_le_left _ _), hK, hvol, hnear,
    a, level, R, original, E1, schedule, hBackbone, hgl, hSchedule, hCore, hCost,
    hPoint, hOld, hConditioned, hScales, hMiddle, hAllPairs, hE1Near,
    ell, j, hell, hjmenu, hradius, hrlo, hrhi, ?_, ?_, hrsquare,
    F, hFE1, hFn, hret, P, hnearP, hpoints⟩
  · simpa only [hScheduleW] using hidentity
  · simpa only [hScheduleW] using hscale

end NativeActualMesoscopicRankConfiguration
