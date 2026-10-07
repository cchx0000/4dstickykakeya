import Theorems.Thm_StickyKakeya4_native_middle_two_scale_configuration
import Theorems.Thm_StickyKakeya4_native_two_scale_boundary_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeAllTwoScaleConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeFixedSizeScaleMenu NativeLocalMenuInterpolation NativeMiddleWindowBalance
open NativeTwoScaleConfiguration NativeConditionedPairMenu NativeMiddleTwoScaleConfiguration
open NativeTwoScaleBoundaryBalance NativeMasterPointRelations
open scoped BigOperators ENNReal

def boundaryWindow (tau : ℝ) : ℝ := min (tau/1000) (1/8)

lemma boundaryWindow_pos {tau : ℝ} (htau : 0 < tau) : 0 < boundaryWindow tau :=
  lt_min (by positivity) (by norm_num)

def fullSchedule (tau : ℝ) (htau : 0 < tau) (g level : ℕ) : Fin (g+1) → Fin (level+1) :=
  canonicalSchedule (boundaryWindow tau) (tau/16) (boundaryWindow_pos htau) (by positivity) g level

/-- Actual all-depth conditional multiplicity matching. A single original
near source and a single incidence core simultaneously work for EVERY dyadic
pair 0≤m≤f≤level. The middle construction is invoked once, then both boundaries
are handled deterministically on its unchanged R, E, and global representatives. -/
theorem exists_all_two_scale_configuration (hk : 0 < extremalExponent)
    (tau : ℝ) (htau : 0 < tau) :
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
          (original : Fin n → Finset Index) (E : Finset (Fin n × Index))
          (schedule : Fin (g+1) → Fin (level+1)),
          HasOriginalBackbone D original R a level zeta ∧ g ≤ level ∧
          schedule=fullSchedule tau htau g level ∧
          IsCore D original R a eta zeta (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L
            (relationMenu h R a schedule (pairRelationMenu h R a schedule
              (masterRelations D a schedule)))
            (fun j => 2^(schedule j).val) E ∧
          (125*175616*16384:ℝ)*(factor (menuSize (pairMenuSize (1+(g+1)) (g+1)) (g+1)) (g+1) L:ℝ)*
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
          ∀m f : ℕ,m ≤ f → f ≤ level → HasConditionalTwoScale h R E a level m f tau := by
  let w := boundaryWindow tau
  let loss := tau/16
  have hw : 0 < w := boundaryWindow_pos htau
  have hw8 : w ≤ 1/8 := min_le_right _ _
  have hwTau : w ≤ tau/1000 := min_le_left _ _
  have hwsmall : w < 1/2 := hw8.trans_lt (by norm_num)
  have hloss : 0 < loss := by dsimp [loss]; positivity
  obtain ⟨seed,e,zeta,L,g,hseed,hsLoss,he,hzeta,hzseed,hL,hg,hgrid,hbase⟩ :=
    exists_middle_two_scale_configuration hk loss w hloss hw hwsmall
  have hsTau : seed ≤ tau/16384 := by dsimp [loss] at hsLoss; linarith
  obtain ⟨dc,hdc,_hdc1,hconstantCut⟩ := exists_positive_rpow_absorption_threshold hloss
    (by norm_num : (0:ℝ) ≤ 729) (by norm_num : (0:ℝ)<1)
  refine ⟨seed,e,zeta,L,g,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,?_⟩
  intro etaBound deltaBound heB hdB
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hK,hvol,hnear,
    a,level,R,original,E,schedule,hBackbone,hgl,hSchedule,hCore,hCost,hPoint,hOld,hConditioned,
    hScales,hFirst,hMiddle⟩ := hbase etaBound (min deltaBound dc) heB (lt_min hdB hdc)
  have hd := h.1.2.1
  have horiginal := hBackbone.1
  have hdy := hBackbone.2.1
  have ha := hBackbone.2.2.1
  have hE : E⊆incidences original := hCore.1.trans (filter_subset _ _)
  have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hCore.1 hz)).2
  have hconstant : (729:ℝ) ≤ D.thickness^(-loss) := by
    have hh := hconstantCut D.thickness hd (hsmall.le.trans (min_le_right _ _))
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd loss)).mpr hh
  have hgridW : 1/(g:ℝ) < w/4 := hgrid.trans_le
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hlarge := large_level_of_grid w hw g level hg hgridW hgl
  have hdiag : 48*w ≤ tau := by linarith
  have hmargin : 2*loss+32*w ≤ tau := by dsimp [loss]; linarith
  refine ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall.trans_le (min_le_left _ _),hK,hvol,hnear,
    a,level,R,original,E,schedule,hBackbone,hgl,hSchedule,hCore,hCost,hPoint,hOld,hConditioned,hScales,hFirst,?_⟩
  intro m f hmf hfl
  exact all_pair_bounds h original horiginal ha R E hE hER level hdy w loss tau hw hw8 hlarge
    hconstant hdiag hmargin hMiddle m f hmf hfl

end NativeAllTwoScaleConfiguration
