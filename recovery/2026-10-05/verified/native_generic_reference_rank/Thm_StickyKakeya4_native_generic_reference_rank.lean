import Theorems.Thm_StickyKakeya4_native_generic_reference_data
import Theorems.Thm_StickyKakeya4_native_rank_mesoscopic_radius_menu
import Theorems.Thm_StickyKakeya4_native_rank_exponent_hierarchy
import Theorems.Thm_StickyKakeya4_native_reference_core_global_near
import Theorems.Thm_StickyKakeya4_native_rank_one_excluded_from_source_cost
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6500000
noncomputable section

namespace NativeGenericReferenceRank
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization
open NativeFixedCompactKakeyaExponent NativeJointUniformCoarseRelations NativeJointQuantitativeMenu
open NativeBalancedConfiguration NativeFixedSizeScaleMenu NativeLocalMenuInterpolation
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativeMiddleTwoScaleConfiguration NativeMasterPointRelations NativeAllTwoScaleConfiguration
open NativeDirectionRankDichotomy NativeIncidentRankSelection NativeRankRadiusMenu
open NativeRankExponentHierarchy NativeReferenceCoreGlobalNear NativeRankOneExcludedFromSourceCost
open NativeGenericReferenceData NativeActualMesoscopicRankConfiguration
open SelfUniform
open scoped BigOperators ENNReal

/-- The actual rank cut and its point-varying planes, relative to an unchanged
reference E1. This predicate contains no first-stage retention-factor choice. -/
def HasRankSelection {n g : ℕ} (D : FiniteScaleSource n) (_a : ℝ) (level : ℕ)
    (E1 : Finset (Fin n × Index)) (schedule : Fin (g+1) → Fin (level+1))
    (tau : ℝ) (htau : 0 < tau) (eta0 c : ℝ) : Prop :=
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
                          ((pointSet E1 k).card : ℝ)

/-- All rank-selection cutoffs are chosen before the original source. The
proof reads the actual generic reference record and never invokes a new source. -/
theorem exists_rank_selection_cutoff (hk : 0 < extremalExponent)
    (eta0 c : ℝ) (he0 : 0 < eta0) (heK : eta0 ≤ extremalExponent/2)
    (hc : 0 < c) (hcsmall : c ≤ 1/2)
    (tau : ℝ) (htau : 0 < tau) (htauT : tau ≤ commonBudget eta0 c/1024) (htauHalf : tau ≤ 1/2)
    (seed : ℝ) (hseed : 0 < seed) (hseedTau : seed ≤ tau/16384)
    (g : ℕ) (hg : 0 < g) (hgrid : 1/(g:ℝ) < rankWindow tau/4) :
    ∃delta0 : ℝ,0 < delta0 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0 ≤ eta → eta ≤ seed/8 → D.thickness ≤ delta0 →
      ∀(e zeta : ℝ) (L : ℕ) (ref : Reference h tau htau seed e zeta L g),
        D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal →
        D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1 ∧
        HasRankSelection D ref.a ref.level ref.E1 ref.schedule tau htau eta0 c := by
  let t := commonBudget eta0 c
  have hc1 : c ≤ 1 := by linarith
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
  refine ⟨min dRank (min dGeom dSquare),lt_min hdRank (lt_min hdGeom hdSquare),?_⟩
  intro n D eta h heta hetaSeed hsmall e zeta L ref hnear
  have hcuts : D.thickness ≤ dRank ∧ D.thickness ≤ dGeom ∧ D.thickness ≤ dSquare := by
    simpa only [le_min_iff] using hsmall
  let a := ref.a
  let level := ref.level
  let R := ref.R
  let original := ref.original
  let E1 := ref.E1
  let schedule := ref.schedule
  have hBackbone := ref.backbone
  have hgl := ref.grid_depth
  have hCore := ref.core
  have hCost := ref.cost
  have hOld := ref.parent_point
  have hScales := ref.scales
  have hd := h.1.2.1
  have horiginal := hBackbone.1
  have hdy := hBackbone.2.1
  have ha := hBackbone.2.2.1
  have hE1 : E1 ⊆ incidences original := hCore.1.trans (filter_subset _ _)
  have hFactor := NativeGenericReferenceData.factor_pos ref
  have hE1Near := NativeGenericReferenceData.global_near ref heta hetaSeed hnear
  have hlarge := large_level_of_grid w hw g level hg hgridW hgl
  have hgeom : D.thickness ^ (w / 2) ≤ 1 / 48 := by
    simpa only [one_mul] using hGeom D.thickness hd hcuts.2.1
  have hsquare : D.thickness ^ (1 / 2 : ℝ) ≤ 1 / 147456 := by
    simpa only [one_mul] using hSquare D.thickness hd hcuts.2.2
  obtain ⟨ell, j, hjmenu, hradius, hrlo, hrhi, hidentity, hscale, hrsquare,
    F, hFE1, hFn, hret, P, hnearP, hpoints⟩ :=
    NativeRankMesoscopicRadiusMenu.exists_mesoscopic_rank_retention D E1 hCore.2.1
      w hw hwsmall g level hg hgridW hlarge hdy hgeom hsquare
      (cutoff c) (rankLoss eta0 c)
      (fun i => ⟨(cutoff_bounds hc hc1 i).1, (cutoff_bounds hc hc1 i).2.1⟩)
      (rankLoss_pos he0 hc)
  have hScheduleW : ref.schedule = windowSchedule w hw.le g ref.level :=
    ref.schedule_eq.trans (fullSchedule_eq_rankWindow tau htau g ref.level)
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
      simpa only [schedule,hScheduleW] using hidentity
    have hret0 : (radius w hw.le g level j) ^ (rankLoss eta0 c (0 : Fin 4)) /
        (4 * ((g : ℝ) + 1)) * (E1.card : ℝ) ≤ (F.card : ℝ) := by
      simpa only [hzero] using hret
    exact hExclude n D eta a heta h hcuts.1 original horiginal ha E1 F hE1 hFE1
      (schedule j).val (coreRadix original R L)
      (factor ref.dimension (g + 1) L)
      hFactor hCost (radius w hw.le g level j) (rankLoss eta0 c (0 : Fin 4))
      (radius_pos w hw.le g level j) hrhi hrlo hradius0 hstop0 hidentityS P hdim hnearP
      hFormal hParent hret0 hE1Near
  refine ⟨hE1Near,ell,j,hell,hjmenu,hradius,hrlo,hrhi,?_,?_,hrsquare,
    F,hFE1,hFn,hret,P,hnearP,hpoints⟩
  · simpa only [schedule,hScheduleW] using hidentity
  · simpa only [schedule,hScheduleW] using hscale

end NativeGenericReferenceRank
