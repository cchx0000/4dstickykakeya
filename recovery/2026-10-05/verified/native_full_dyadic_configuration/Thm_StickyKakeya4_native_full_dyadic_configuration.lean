import Theorems.Thm_StickyKakeya4_native_full_depth_extension

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeFullDyadicConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentDensityCore NativeLocalMenuInterpolation
open NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance NativeBoundaryDepths
open NativeFullDepthExtension NativeJointUniformCoarseRelations NativeBalancedConfiguration
open NativeUnitParentNormalization
open scoped ENNReal BigOperators

/-- Genuine fixed-compact near-extremizers admit one original R and one
exact incidence core E whose full physical coarse and all active original
parent multiplicities obey the requested powers at EVERY depth 0,...,level.
The only source selection is the frozen middle-configuration theorem; the
boundary extension changes neither R nor E. -/
theorem exists_full_configuration (hk : 0 < extremalExponent)
    (tau : ℝ) (htau : 0 < tau) :
    ∃ (e zeta : ℝ) (L g : ℕ), 0 < e ∧ 0 < zeta ∧ zeta ≤ tau/8192 ∧ 0 < L ∧ 0 < g ∧
      1/(g:ℝ) < min (boundaryWindow tau) ((tau/4)/1000)/4 ∧
      ∀ etaBound deltaBound : ℝ,0 < etaBound → 0 < deltaBound →
      ∃ (eta : ℝ) (n : ℕ) (D : FiniteScaleSource n)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0 < eta ∧ eta < etaBound ∧ eta < tau/256 ∧ D.thickness < deltaBound ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-eta) ∧
        D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n))
          (original : Fin n → Finset Index) (E : Finset (Fin n × Index))
          (schedule : Fin (g+1) → Fin (level+1)),
          HasOriginalBackbone D original R a level zeta ∧ g ≤ level ∧
          schedule=canonicalSchedule (boundaryWindow tau) (tau/4)
            (boundaryWindow_pos htau) (by positivity) g level ∧
          IsCore D original R a eta zeta (menuSize (g+1) (g+1)) (g+1) L
            (relationMenu h R a schedule (fun j => parentPointRel D a (2^(schedule j).val)))
            (fun j => 2^(schedule j).val) E ∧
          (∀j,HasJointScale h R E a level (schedule j).val e zeta (((tau/4)/8)/8) (((tau/4)/8)/8) ∧
            HasBalancedScale h R E a level (schedule j).val ((tau/4)/8)) ∧
          ∀m : Fin (level+1),HasMiddleScale h R E a level m.val tau := by
  let v := boundaryWindow tau
  let t := tau/4
  have hv : 0 < v := boundaryWindow_pos htau
  have hvquarter : v ≤ 1/4 := boundaryWindow_le_quarter tau
  have hvhalf : v < 1/2 := hvquarter.trans_lt (by norm_num)
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨e,zeta,L,g,he,hz,hzSmall,hL,hg,hgrid,hbase⟩ :=
    exists_middle_configuration hk t v ht hv hvhalf
  have hzTarget : zeta ≤ tau/8192 := by
    change zeta ≤ (tau/4)/2048 at hzSmall
    linarith
  obtain ⟨dc,hdc,_hdc1,hconstantCut⟩ := exists_positive_rpow_absorption_threshold ht
    (by norm_num : (0:ℝ) ≤ (64:ℝ)^3) (by norm_num : (0:ℝ) < 1)
  refine ⟨e,zeta,L,g,he,hz,hzTarget,hL,hg,hgrid,?_⟩
  intro etaBound deltaBound heB hdB
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSmall,hsmall,hK,hvol,hnear,
    a,level,R,original,E,schedule,hbackbone,hglevel,hschedule,hEcore,hScales,hMiddle⟩ :=
    hbase etaBound (min deltaBound dc) heB (lt_min hdB hdc)
  have hd := h.1.2.1
  have hdy := hbackbone.2.1
  have hetaTarget : eta < tau/256 := by
    change eta < (tau/4)/64 at hetaSmall
    linarith
  have hconstant : (64:ℝ)^3 ≤ D.thickness^(-t) := by
    have hh := hconstantCut D.thickness hd (hsmall.le.trans (min_le_right _ _))
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd t)).mpr hh
  let w := min v (t/1000)
  have hw : 0 < w := lt_min hv (by positivity)
  have hlargeW := large_level_of_grid w hw g level hg hgrid hglevel
  have hlarge : 4 ≤ v*(level:ℝ) := hlargeW.trans
    (mul_le_mul_of_nonneg_right (min_le_left v (t/1000)) (Nat.cast_nonneg level))
  have hvLoss : v ≤ tau/1000 := boundaryWindow_le_loss tau
  have hbudget : 2*t+20*v ≤ tau := by
    change 2*(tau/4)+20*v ≤ tau
    nlinarith only [hvLoss,htau]
  have hE : E ⊆ incidences original := hEcore.1.trans (filter_subset _ _)
  have hER : ∀z∈E,z.1∈R := fun z hzE => (mem_filter.mp (hEcore.1 hzE)).2
  have hfull := full_from_middle h original hbackbone.1 hbackbone.2.2.1 R E hE hER
    hEcore.2.1 level hdy v t tau hv hvquarter ht.le hlarge hbudget hconstant hMiddle
  exact ⟨eta,n,D,h,heta,hetaB,hetaTarget,hsmall.trans_le (min_le_left _ _),hK,hvol,hnear,
    a,level,R,original,E,schedule,hbackbone,hglevel,hschedule,hEcore,hScales,
    fun m => hfull m.val (Nat.le_of_lt_succ m.isLt)⟩

end NativeFullDyadicConfiguration
