import Theorems.Thm_StickyKakeya4_native_conditioned_pair_menu
import Theorems.Thm_StickyKakeya4_native_conditional_relative_upper
import Theorems.Thm_StickyKakeya4_native_balanced_configuration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

noncomputable section
namespace NativeTwoScaleConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentDensityCore NativeLocalParentSource
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeConditionedPairMenu NativePairScaleBudget NativeConditionalRelativeUpper
open NativeActualRelativeCoarseAdmission NativeUnitParentNormalization NativeFixedCompactKakeyaExponent
open NativeNearTargetLoss SelfUniform
open scoped ENNReal BigOperators

/-- The scheduled depth separation is exactly the original real-power gap
needed for the relative coarse window. -/
lemma depth_gap_power {delta w : ℝ} {level m f : ℕ}
    (hdy : delta=(2:ℝ)⁻¹^level) (hgap : w*(level:ℝ) ≤ (f:ℝ)-(m:ℝ)) :
    ((2^m:ℕ):ℝ)/((2^f:ℕ):ℝ) ≤ delta^w := by
  have hd : delta=(2:ℝ)^(-(level:ℝ)) := by
    simp only [hdy,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,inv_pow]
  have hr : ((2^m:ℕ):ℝ)/((2^f:ℕ):ℝ)=(2:ℝ)^((m:ℝ)-(f:ℝ)) := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_natCast,Real.rpow_natCast]
    norm_cast
  rw [hr,hd,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  linarith

/-- The actual global fine coarse shadow, conditionally shaded by one old
coarser parent, has the relative extremal power. All global representatives
are fixed on the same original R. -/
def HasConditionalTwoScale {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m f : ℕ) (tau : ℝ) : Prop :=
  let relative := (64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ))
  ∀p,(parentEdges D a (2^m) E p).Nonempty →
    let M := (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E p))).toReal
    D.thickness^tau*relative^(-extremalExponent) ≤ M ∧
      M ≤ D.thickness^(-tau)*relative^(-extremalExponent)

/-- Finite two-scale source construction. Four conditioned relations per
ordered scale pair are appended before ONE selection of E. Relative admission
uses the literal local source, its full backbone, and all its literal cells.
The original conditional physical lower uses the exact old incidence tower;
no inverse time menu, second original R, or output certificate is assumed. -/
theorem exists_two_scale_configuration (hk : 0 < extremalExponent)
    (tau w : ℝ) (htau : 0 < tau) (hw : 0 < w)
    (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (seed e zeta : ℝ) (L : ℕ),0 < seed ∧ seed ≤ tau/64 ∧
      0 < e ∧ zeta=w*e/32 ∧ 0 < zeta ∧ zeta ≤ seed/256 ∧ 0 < L ∧
      ∀ etaBound deltaBound : ℝ,0 < etaBound → 0 < deltaBound →
      ∃ (eta : ℝ) (n : ℕ) (D : FiniteScaleSource n)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0 < eta ∧ eta < etaBound ∧ eta < seed/8 ∧ D.thickness < deltaBound ∧
        (∀i,D.line i∈fixedCompactClass) ∧
        volume (sourceUnion D) ≤ (ENNReal.ofReal D.thickness).rpow (extremalExponent-eta) ∧
        D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)) (original : Fin n → Finset Index),
          (∀i,D.shading i = wzCellShading (mesh D) original i) ∧
          D.thickness = (2:ℝ)⁻¹^level ∧
          (∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
          R.Nonempty ∧ n ≤ 2*R.card ∧
          wzTotalShadingVolume D ≤ 2*NativeOriginalPrunedMass.shadingMass D R ∧
          (ENNReal.ofReal D.thickness).rpow zeta*NativeOriginalPrunedMass.tubeMass D R ≤
            NativeOriginalPrunedMass.shadingMass D R ∧
          (∀ U : Set E4, Convex ℝ U →
            ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card:ℝ≥0∞) ≤
              (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
          (∀ (ell : Fin (level+1)) (p : Parent),
            (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
              D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
                ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
                D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) ∧
          ∀ schedule : Fin g → Fin (level+1),
            (∀j,1/((2^(schedule j).val:ℕ):ℝ) ≤ D.thickness^w) →
            (∀j,D.thickness/(1/((2^(schedule j).val:ℕ):ℝ)) ≤ D.thickness^w) →
            ∀ (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
              (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
              ∃ E, IsCore D original R a eta zeta (menuSize (pairMenuSize d g) g) g L
                (relationMenu h R a schedule (pairRelationMenu h R a schedule Rel)) (fun j => 2^(schedule j).val) E ∧
                (125*175616*16384:ℝ)*(factor (menuSize (pairMenuSize d g) g) g L:ℝ)*(coreRadix original R L:ℝ)^2*
                  D.thickness^(-eta) ≤ D.thickness^(-(seed/8)) ∧
                (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
                  (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
                (∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^w →
                  D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^w →
                    HasCoarseScale h R E a level m e zeta (seed/8) (seed/8)) ∧
                (∀j,
                  HasJointScale h R E a level (schedule j).val e zeta (seed/8) (seed/8) ∧
                  HasBalancedScale h R E a level (schedule j).val seed ) ∧
                ∀i j : Fin g,(schedule i).val ≤ (schedule j).val →
                  ((2^(schedule i).val:ℕ):ℝ)/((2^(schedule j).val:ℕ):ℝ) ≤ D.thickness^w →
                  HasConditionalTwoScale h R E a level (schedule i).val (schedule j).val tau := by
  obtain ⟨eC,dEngine,heC,heSmall,hdEngine,hEngine⟩ := exists_relative_upper_engine tau w htau hw
  let seed := min (tau/64) (w^2*eC/256)
  have hseed : 0 < seed := lt_min (by positivity) (by positivity)
  have hsTau : seed ≤ tau/64 := min_le_left _ _
  have hsScale : seed ≤ w^2*eC/256 := min_le_right _ _
  have hDG : 0 < pairMenuSize d g+g := by unfold pairMenuSize; omega
  obtain ⟨e,zeta,L,he,hzeq,hzeta,hzSeed,hL,hbase⟩ :=
    exists_balanced_configuration hk seed w hseed hw (pairMenuSize d g) g hDG
  have hMargins := parameter_margins htau hw heC heSmall hsTau hsScale hzeq hzSeed
  obtain ⟨dProfile,hdProfile,_hdProfile1,hProfileBudget⟩ :=
    exists_relative_population_budget w (w/2) eC zeta (half_pos hw) heC hzeta.le hMargins.2.1
  refine ⟨seed,e,zeta,L,hseed,hsTau,he,hzeq,hzeta,hzSeed,hL,?_⟩
  intro etaBound deltaBound heB hdB
  obtain ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall,hK,hvol,hnear,a,level,R,original,
    horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase etaBound (min deltaBound (min dEngine dProfile)) heB
      (lt_min hdB (lt_min hdEngine hdProfile))
  have hrest := hsmall.le.trans (min_le_right _ _)
  have hDEngine := hrest.trans (min_le_left _ _)
  have hDProfile := hrest.trans (min_le_right _ _)
  refine ⟨eta,n,D,h,heta,hetaB,hetaSeed,hsmall.trans_le (min_le_left _ _),hK,hvol,hnear,
    a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro schedule hcoarse hfine Rel hrefl hsym
  let T := pairRelationMenu h R a schedule Rel
  obtain ⟨E,hEcore,hCost,hCaller,hCoarseAll,hScales⟩ :=
    hcore schedule hcoarse hfine T
      (pairRelationMenu_refl h R a schedule Rel hrefl)
      (pairRelationMenu_symm h R a schedule Rel hsym)
  refine ⟨E,hEcore,hCost,?_,hCoarseAll,hScales,?_⟩
  · intro j x y hx hy
    simpa only [T,pairRelationMenu,Fin.addCases_left] using
      hCaller (Fin.castAdd (g*g+(g*g+(g*g+g*g))) j) x y hx hy
  intro i j hmf hgap
  let m := (schedule i).val
  let f := (schedule j).val
  let rad := coreRadix original R L
  let F := factor (menuSize (pairMenuSize d g) g) g L
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hF : 0 < F := by
    have hh : 0 < menuSize (pairMenuSize d g) g+g+g := by unfold menuSize; omega
    dsimp [F,factor,NativeLocalPairUniformCore.retentionCost]
    positivity
  have hCosts := radix_four_cost hd hd1 heta.le F rad hF hCost
  have hCost41472 : (41472:ℝ)*(rad:ℝ)^4 ≤ D.thickness^(-(seed/4)) := by
    simpa only [show 2*(seed/8)=seed/4 by ring] using hCosts.1
  have hE : E⊆incidences original := hEcore.1.trans (filter_subset _ _)
  have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hEcore.1 hz)).2
  obtain ⟨hJointM,hBalancedM⟩ := hScales i
  obtain ⟨_hJointF,hBalancedF⟩ := hScales j
  obtain ⟨HG,HX,HR,HY⟩ := pairRelationMenu_uniformities h R a schedule Rel E rad hCaller i j
  change ∀p,(parentEdges D a (2^m) E p).Nonempty → _
  intro p hp
  let Ep := parentEdges D a (2^m) E p
  have hEp : Ep⊆incidences original := (filter_subset _ _).trans hE
  have hlabels : ∀z∈Ep,z.1∈parentLabels D R a (2^m) p := by
    intro z hz
    obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨hER z hzE,hzp⟩
  have hQ : (parentLabels D R a (2^m) p).Nonempty := by
    obtain ⟨z,hz⟩ := hp
    exact ⟨z.1,hlabels z hz⟩
  obtain ⟨hGP,hGX,hRP,hRX⟩ := conditional_pair_uniformities h R E a level m f rad HG HX HR HY p hQ
  obtain ⟨hS,hSK,_hTrace,_hSupper,_hOldUpper⟩ := hJointM.2.2 p hp
  have hmwindow : ((2^m:ℕ):ℝ)*D.thickness ≤ D.thickness^w := by
    simpa only [div_div_eq_mul_div,div_one,mul_comm] using hfine i
  have hfwindow : ((2^f:ℕ):ℝ)*D.thickness ≤ D.thickness^w := by
    simpa only [div_div_eq_mul_div,div_one,mul_comm] using hfine j
  have hRho : (64/((2^m:ℕ):ℝ)) ≤ 1 := by
    obtain ⟨Qm,hsep,_hQP,_hQne,hC,_hCK,hthick,_hShade,_hComp,_hUpper⟩ := hJointM.1
    have hh := hC.1.2.2.1
    rwa [hthick] at hh
  have hDeltaLocal : D.thickness ≤ (source h R Ep a m p).thickness := by
    change D.thickness ≤ ((2^m:ℕ):ℝ)*D.thickness/64
    calc
      _ = (64/((2^m:ℕ):ℝ))*(((2^m:ℕ):ℝ)*D.thickness/64) :=
        (NativeSameSourceMultiplicityBalance.actual_scale_product (delta:=D.thickness) (by positivity : 0<2^m)).symm
      _ ≤ 1*(((2^m:ℕ):ℝ)*D.thickness/64) := mul_le_mul_of_nonneg_right hRho (by positivity)
      _ = _ := one_mul _
  have hProf := hProfileBudget D.thickness hd hDProfile (2^m) (by positivity) hmwindow
  have hUpper := hEngine n D eta h hDEngine original horiginal a ha R Ep hEp level m f hdy
    hmf (Nat.le_of_lt_succ (schedule j).isLt) p hQ hlabels zeta e seed hzeta.le hsTau H hS hSK
    hMargins.1 hProf hDeltaLocal hmwindow hfwindow hgap rad hRP hRX hCost41472
  have hLower := NativeConditionalCoarseBounds.physical_lower h original horiginal ha R E hE hER
    level m f hdy hmf (Nat.le_of_lt_succ (schedule j).isLt) p rad
    (hBalancedM.2.2 p hp).2.2.1
    (fun q hq => (hBalancedF.2.2 q hq).2.2.2) hGP hGX hCosts.2
  have hLower' := lower_with_target_loss hd hd1
    (by positivity : (0:ℝ)<64/((2^(f-m+6):ℕ):ℝ))
    (show 2*seed+2*(seed/8) ≤ tau by linarith [hMargins.2.2.1]) hLower
  change D.thickness^tau*((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent) ≤ _ ∧ _
  rw [←(relative_scale_eq hmf).2]
  exact ⟨hLower',hUpper⟩

end NativeTwoScaleConfiguration
