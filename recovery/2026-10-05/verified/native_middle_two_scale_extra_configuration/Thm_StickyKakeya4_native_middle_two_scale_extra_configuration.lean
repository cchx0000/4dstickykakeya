import Theorems.Thm_StickyKakeya4_native_middle_two_scale_balance
import Theorems.Thm_StickyKakeya4_native_initial_extra_relations

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeMiddleTwoScaleExtraConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeFixedSizeScaleMenu NativeScaleMenuSuccessor NativeLocalMenuInterpolation
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativePairScaleBudget NativeTwoAxisConditionalTransfer NativeMiddleTwoScaleBalance NativeMasterPointRelations
open scoped BigOperators ENNReal

/-- The initial source factory accepts an arbitrary fixed number of additional
relations, including one candidate-parent/relative menu per scheduled depth.
The cardinal function is fixed before the grid and source; the actual relations
are chosen after the original backbone, before the unique E1 selection.
All retention and cost fields retain the actual enlarged core dimension. -/
theorem exists_middle_two_scale_extra_configuration (hk : 0 < extremalExponent)
    (tau window : ℝ) (htau : 0 < tau) (hw : 0 < window) (hwsmall : window < 1/2) (extraCount : ℕ → ℕ) :
    ∃ (seed e zeta : ℝ) (L g : ℕ),0 < seed ∧ seed ≤ tau/1024 ∧
      0 < e ∧ 0 < zeta ∧ zeta ≤ seed/256 ∧ 0 < L ∧ 0 < g ∧
      1/(g:ℝ) < min window (tau/1000)/4 ∧
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
          schedule=canonicalSchedule window tau hw htau g level ∧
          ∀Extra : Fin (extraCount g) → (Fin n × Index) → (Fin n × Index) → Prop,
          (∀i x,Extra i x x) → (∀i x y,Extra i x y → Extra i y x) →
          ∃E : Finset (Fin n × Index),
          (∀i x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Extra i) E x ≤
            (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Extra i) E y) ∧
          IsCore D original R a eta zeta (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L
            (relationMenu h R a schedule (pairRelationMenu h R a schedule
              (NativeInitialExtraRelations.relations D a schedule Extra)))
            (fun j => 2^(schedule j).val) E ∧
          (125*175616*16384:ℝ)*(factor (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L:ℝ)*
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
          (∀m : ℕ,window*(level:ℝ) ≤ m → (m:ℝ) ≤ (1-window)*(level:ℝ) →
            HasMiddleScale h R E a level m tau) ∧
          ∀m f : ℕ,m ≤ f → window*(level:ℝ) ≤ m → (f:ℝ) ≤ (1-window)*(level:ℝ) →
            HasConditionalTwoScale h R E a level m f tau := by
  let w := min window (tau/1000)
  let b := tau/16
  have hw0 : 0 < w := lt_min hw (by positivity)
  have hw0small : w < 1/2 := (min_le_left _ _).trans_lt hwsmall
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨g,dm,hg,hdm,hgrid,hmenu⟩ := exists_source_window_menu w hw0 hw0small
  obtain ⟨seed,e,zeta,L,hseed,hsb,he,_hzeq,hzeta,hzseed,hL,hbase⟩ :=
    exists_two_scale_configuration hk b (w/2) hb (half_pos hw0) (extraCount g+(1+(g+1))) (g+1) (by omega)
  have hsTau : seed ≤ tau/1024 := by dsimp [b] at hsb; linarith
  have hsB : seed ≤ b := by linarith
  obtain ⟨dc,hdc,_hdc1,hconstantCut⟩ := exists_positive_rpow_absorption_threshold hseed
    (by norm_num : (0:ℝ) ≤ 729) (by norm_num : (0:ℝ)<1)
  refine ⟨seed,e,zeta,L,g,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,?_⟩
  intro etaBound deltaBound heB hdB
  let cutoff := min deltaBound (min dm (min ((2:ℝ)⁻¹^g) dc))
  have hcut : 0 < cutoff := lt_min hdB (lt_min hdm (lt_min (by positivity) hdc))
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hK,hvol,hnear,
    a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase etaBound cutoff heB hcut
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hcuts : D.thickness ≤ deltaBound ∧ D.thickness ≤ dm ∧
      D.thickness ≤ (2:ℝ)⁻¹^g ∧ D.thickness ≤ dc := by
    simpa only [cutoff,le_min_iff] using hsmall.le
  have hgl := depth_le_of_dyadic_cutoff level g hdy hcuts.2.2.1
  let schedule := windowSchedule w hw0.le g level
  refine ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall.trans_le (min_le_left _ _),hK,hvol,hnear,
    a,level,R,original,schedule,⟨horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H⟩,
    hgl,rfl,?_⟩
  intro Extra hExtraRefl hExtraSymm
  let Rel := NativeInitialExtraRelations.relations D a schedule Extra
  have hmenuPower := (hmenu D.thickness level hdy hcuts.2.1).1
  obtain ⟨E,hEcore,hcost,hCaller,hCoarseAll,hScales,hPairs⟩ := hcore schedule
    (fun j => (hmenuPower j).1) (fun j => (hmenuPower j).2) Rel
    (NativeInitialExtraRelations.relations_refl D a schedule Extra hExtraRefl)
    (NativeInitialExtraRelations.relations_symm D a schedule Extra hExtraSymm)
  obtain ⟨hExtra,hMaster⟩ := NativeInitialExtraRelations.caller_uniformities D a schedule Extra E
    (coreRadix original R L) hCaller
  obtain ⟨hOld,hPoint⟩ := master_uniformities D a schedule E (coreRadix original R L) hMaster
  have hF : 0 < factor (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L := by
    unfold factor NativeLocalPairUniformCore.retentionCost menuSize pairMenuSize
    positivity
  have hQ := radix_sq_le_of_transfer_cost hd hd1 heta.le
    (factor (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L)
    (coreRadix original R L) hF hcost
  have hQ4 := (radix_four_cost hd hd1 heta.le
    (factor (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L)
    (coreRadix original R L) hF hcost).1
  have hQCost : (729:ℝ)*(coreRadix original R L:ℝ)^4 ≤ D.thickness^(-b) := by
    calc
      _ ≤ (41472:ℝ)*(coreRadix original R L:ℝ)^4 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ D.thickness^(-(2*(seed/8))) := hQ4
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  have hconstantSeed : (729:ℝ) ≤ D.thickness^(-seed) := by
    have hh := hconstantCut D.thickness hd hcuts.2.2.2
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd seed)).mpr hh
  have hconstant : (729:ℝ) ≤ D.thickness^(-b) := hconstantSeed.trans
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hsB))
  have hgridSmall : 1/(g:ℝ) ≤ tau/4000 := by
    have hwTau : w ≤ tau/1000 := min_le_right _ _
    nlinarith
  have htwo : 2/(g:ℝ)=2*(1/(g:ℝ)) := by ring
  have hkgrid : (1/(g:ℝ))*extremalExponent ≤ 3*(1/(g:ℝ)) := by
    exact (mul_le_mul_of_nonneg_left extremalExponent_le_three (by positivity)).trans_eq (by ring)
  have hmarginL : seed+(1/(g:ℝ))*extremalExponent ≤ tau := by nlinarith
  have hmarginU : seed+seed/8+(2/(g:ℝ))*extremalExponent ≤ tau := by rw [htwo]; nlinarith
  have hmarginC : 2*seed+(2/(g:ℝ))*(4+extremalExponent) ≤ tau := by rw [htwo]; nlinarith
  have hmarginPair : 2*b+16*(2/(g:ℝ)) ≤ tau := by rw [htwo]; dsimp [b]; nlinarith
  have hdiag : 12*w ≤ tau := by have hh : w ≤ tau/1000 := min_le_right _ _; nlinarith
  have hEA : E⊆incidences original := hEcore.1.trans (filter_subset _ _)
  have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hEcore.1 hz)).2
  have hConditioned := core_conditioned_uniformities h original R E L schedule Rel hEcore
  have hOldMenu : ∀j p,(parentEdges D a (2^(schedule j).val) E p).Nonempty →
      D.thickness^seed*(localScale D.thickness (schedule j).val)^(-extremalExponent) ≤
        edgeMultiplicity (parentEdges D a (2^(schedule j).val) E p) ∧
      edgeMultiplicity (parentEdges D a (2^(schedule j).val) E p) ≤
        D.thickness^(-seed)*(localScale D.thickness (schedule j).val)^(-extremalExponent) := by
    intro j p hp
    exact ((hScales j).2.2.2 p hp).2.2
  refine ⟨E,hExtra,hEcore,hcost,hPoint,hOld,hConditioned,hScales,?_,?_⟩
  · intro m hlo hhi
    have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
    have hwWindow : w ≤ window := min_le_left _ _
    have hwLevels := mul_le_mul_of_nonneg_right hwWindow hln
    have hwLevel0 : 0 ≤ w*(level:ℝ) := mul_nonneg hw0.le hln
    have hwindowLevel0 : 0 ≤ window*(level:ℝ) := mul_nonneg hw.le hln
    have hlo0 : w*(level:ℝ) ≤ m := by nlinarith
    have hhi0 : (m:ℝ) ≤ (1-w)*(level:ℝ) := by nlinarith
    have hm : m ≤ level := by
      have hh : (m:ℝ) ≤ level := by nlinarith
      exact_mod_cast hh
    have hpower := depth_window_powers (w:=w) level m hdy (by nlinarith) (by nlinarith)
    refine ⟨?_,?_,?_⟩
    · exact middle_coarse_lower h original horiginal ha R E hEA hER level hdy
        w hw0 hw0small g hg hgl hgrid seed tau hconstantSeed hmarginC
        (fun j => (hScales j).2.1) m hm hlo0 hhi0
    · exact coarse_upper_of_admission (gamma:=seed/8) (loss:=seed/8) (target:=tau)
        h R E level m hdy hm (by positivity) (by linarith) (hCoarseAll m hpower.1 hpower.2)
    · intro p hp
      exact middle_old_parent_bounds D hd hd1 a E level hdy w hw0 hw0small g
        (coreRadix original R L) hg hgl hgrid seed (seed/8) tau hQ hmarginL hmarginU hOld hOldMenu m hlo0 hhi0 p hp
  · intro m f hmf hmlo hfhi
    have hln : (0:ℝ) ≤ level := Nat.cast_nonneg _
    have hwLevels := mul_le_mul_of_nonneg_right (show w ≤ window from min_le_left _ _) hln
    apply middle_pair_bounds h original horiginal ha R E hEA hER level hdy w hw0 hw0small g
      (coreRadix original R L) hg hgl hgrid b tau hQCost hconstant hdiag hmarginPair
      hConditioned hPairs m f hmf
    · exact hwLevels.trans hmlo
    · nlinarith

end NativeMiddleTwoScaleExtraConfiguration
