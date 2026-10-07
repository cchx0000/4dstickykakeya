/- UNVERIFIED fixed-source Reference construction.
The source is provided by actual remembered shading and union estimates;
this module never chooses another extremizing source. Source-only staging.
No Lean check or independent imported-axiom readback has run. -/
import Theorems.Thm_StickyKakeya4_native_extra_queried_rank_configuration
import Theorems.Thm_StickyKakeya4_native_fixed_compact_multiplicity
import Theorems.Thm_StickyKakeya4_native_joint_absorbed_near_balance
import Theorems.Thm_StickyKakeya4_native_original_cell_presentation_unique

/- Source unit native_fixed_source_reference_body.UNVERIFIED.lean
   SHA256 420b4f2dad155d75f2753fd96da8c5bbdc20136cb7eded5ddbb21fff16fee8db -/
/- UNVERIFIED deterministic fixed-source extraction. No Lean/compiler check has run.
This is an intermediate construction layer. Its real near-multiplicity premise
must be proved from the actual shading and union bounds of the GIVEN D by the
public source reader. This file never selects a new near-extremizing source.
All parameters and cutoffs precede D; each backbone precedes the actual Extra
relations, and one actual E is selected only after every relation is installed.

Proof bodies are extracted from the existing balanced, two-scale, middle-extra,
and all-extra configuration producers, with their source-selection branch removed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeFixedSourceReference
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeFixedCompactKakeyaExponent SelfUniform
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeBalancedConfiguration
open NativeJointAbsorbedNearBalance NativeNearTargetLoss NativeLocalParentSource
open NativeFixedSizeScaleMenu NativeScaleMenuSuccessor NativeLocalMenuInterpolation
open NativeMiddleWindowBalance NativeTwoScaleConfiguration NativeConditionedPairMenu
open NativePairScaleBudget NativeTwoAxisConditionalTransfer NativeMiddleTwoScaleBalance
open NativeConditionalRelativeUpper NativeActualRelativeCoarseAdmission
open NativeTwoScaleBoundaryBalance NativeMasterPointRelations
open NativeAllTwoScaleConfiguration NativeMiddleTwoScaleExtraConfiguration
open NativeGenericReferenceData NativeExtraQueriedRankConfiguration
open scoped BigOperators ENNReal

/-- The universal branch of balanced configuration, on the supplied source.
Source assumptions are native input, compactness, quantitative cutoffs, and the
genuine global multiplicity lower. No source union or local profile is assumed. -/
theorem fixed_balanced_configuration
    (tau window : ℝ) (htau : 0 < tau) (hw : 0 < window)
    (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (e zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      0 < e ∧ zeta=window*e/32 ∧ 0 < zeta ∧ zeta ≤ tau/256 ∧ 0 < L ∧
      0 < eta0 ∧ eta0 ≤ tau/8 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → 0  ≤  eta → eta  ≤  eta0 →
        D.thickness  ≤  delta0 →
        D.thickness^(-extremalExponent+eta)  ≤  (NativeFiniteKakeyaCounts.multiplicity D).toReal →
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)) (original : Fin n → Finset Index),
          (∀i,D.shading i = wzCellShading (mesh D) original i) ∧
          D.thickness = (2:ℝ)⁻¹^level ∧
          (∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
          R.Nonempty ∧ n  ≤  2*R.card ∧
          wzTotalShadingVolume D  ≤  2*NativeOriginalPrunedMass.shadingMass D R ∧
          (ENNReal.ofReal D.thickness).rpow zeta*NativeOriginalPrunedMass.tubeMass D R  ≤ 
            NativeOriginalPrunedMass.shadingMass D R ∧
          (∀ U : Set E4, Convex ℝ U →
            ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card:ℝ ≥ 0∞)  ≤ 
              (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
          (∀ (ell : Fin (level+1)) (p : Parent),
            (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
              D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3  ≤ 
                ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ)  ≤ 
                D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) ∧
          ∀ schedule : Fin g → Fin (level+1),
            (∀j,1/((2^(schedule j).val:ℕ):ℝ)  ≤  D.thickness^window) →
            (∀j,D.thickness/(1/((2^(schedule j).val:ℕ):ℝ))  ≤  D.thickness^window) →
            ∀ (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
              (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
              ∃ E, IsCore D original R a eta zeta (menuSize d g) g L
                (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E ∧
                (125*175616*16384:ℝ)*(factor (menuSize d g) g L:ℝ)*(coreRadix original R L:ℝ)^2*
                  D.thickness^(-eta)  ≤  D.thickness^(-(tau/8)) ∧
                (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x  ≤ 
                  (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
                (∀m : ℕ,1/((2^m:ℕ):ℝ)  ≤  D.thickness^window →
                  D.thickness/(1/((2^m:ℕ):ℝ))  ≤  D.thickness^window →
                    HasCoarseScale h R E a level m e zeta (tau/8) (tau/8)) ∧
                ∀j,
                  HasJointScale h R E a level (schedule j).val e zeta (tau/8) (tau/8) ∧
                  HasBalancedScale h R E a level (schedule j).val tau := by
  have ht8 : 0 < tau/8 := by positivity
  obtain ⟨e,zeta,L,eta0,delta0,he,hzeq,hzeta,hztheta,hL,_hlarge,heta0,_hetaz,hdelta0,hbase⟩ :=
    joint_absorbed_near_balance (tau/8) window (tau/8) ht8 hw ht8 d g hdg
  have hzsmall : zeta  ≤  tau/256 := by linarith
  refine ⟨e,zeta,L,min eta0 (tau/8),delta0,he,hzeq,hzeta,hzsmall,hL,
    lt_min heta0 ht8,min_le_right _ _,hdelta0,?_⟩
  intro n D eta h hK _heta hetaSmall hsmall hnearReal
  have heta0' : eta  ≤  eta0 := hetaSmall.trans (min_le_left _ _)
  have heta8 : eta  ≤  tau/8 := hetaSmall.trans (min_le_right _ _)
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hK hsmall heta0' eta hnearReal
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro schedule hcoarse hfine Rel hrefl hsym
  obtain ⟨E,hEcore,hcost,hOld,hcoarseAll,hscales⟩ := hcore schedule hcoarse hfine Rel hrefl hsym
  refine ⟨E,hEcore,hcost,hOld,hcoarseAll,?_⟩
  intro j
  obtain ⟨hjoint,hpure⟩ := hscales j
  exact ⟨hjoint,pure_near_to_balanced h R E level (schedule j).val hdy
    (Nat.le_of_lt_succ (schedule j).isLt) htau heta8 hzsmall hjoint hpure⟩

/-- The exact two-scale proof, parameterized by a fixed source. -/
theorem fixed_two_scale_configuration
    (tau w : ℝ) (htau : 0 < tau) (hw : 0 < w)
    (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (seed e zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      0 < seed ∧ seed  ≤  tau/64 ∧
      0 < e ∧ zeta=w*e/32 ∧ 0 < zeta ∧ zeta  ≤  seed/256 ∧ 0 < L ∧
      0 < eta0 ∧ eta0  ≤  seed/8 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → 0  ≤  eta → eta  ≤  eta0 →
        D.thickness  ≤  delta0 →
        D.thickness^(-extremalExponent+eta)  ≤  (NativeFiniteKakeyaCounts.multiplicity D).toReal →
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)) (original : Fin n → Finset Index),
          (∀i,D.shading i = wzCellShading (mesh D) original i) ∧
          D.thickness = (2:ℝ)⁻¹^level ∧
          (∀i,wzGraphTime (D.line i) a-mark (D.line i) ∈ Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
          R.Nonempty ∧ n  ≤  2*R.card ∧
          wzTotalShadingVolume D  ≤  2*NativeOriginalPrunedMass.shadingMass D R ∧
          (ENNReal.ofReal D.thickness).rpow zeta*NativeOriginalPrunedMass.tubeMass D R  ≤ 
            NativeOriginalPrunedMass.shadingMass D R ∧
          (∀ U : Set E4, Convex ℝ U →
            ((R.filter (fun i => markedUnitTube (D.line i) D.thickness ⊆ U)).card:ℝ ≥ 0∞)  ≤ 
              (ENNReal.ofReal D.thickness).rpow (-zeta)*volume U*R.card) ∧
          (∀ (ell : Fin (level+1)) (p : Parent),
            (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
              D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3  ≤ 
                ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ)  ≤ 
                D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) ∧
          ∀ schedule : Fin g → Fin (level+1),
            (∀j,1/((2^(schedule j).val:ℕ):ℝ)  ≤  D.thickness^w) →
            (∀j,D.thickness/(1/((2^(schedule j).val:ℕ):ℝ))  ≤  D.thickness^w) →
            ∀ (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
              (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
              ∃ E, IsCore D original R a eta zeta (menuSize (pairMenuSize d g) g) g L
                (relationMenu h R a schedule (pairRelationMenu h R a schedule Rel)) (fun j => 2^(schedule j).val) E ∧
                (125*175616*16384:ℝ)*(factor (menuSize (pairMenuSize d g) g) g L:ℝ)*(coreRadix original R L:ℝ)^2*
                  D.thickness^(-eta)  ≤  D.thickness^(-(seed/8)) ∧
                (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x  ≤ 
                  (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
                (∀m : ℕ,1/((2^m:ℕ):ℝ)  ≤  D.thickness^w →
                  D.thickness/(1/((2^m:ℕ):ℝ))  ≤  D.thickness^w →
                    HasCoarseScale h R E a level m e zeta (seed/8) (seed/8)) ∧
                (∀j,
                  HasJointScale h R E a level (schedule j).val e zeta (seed/8) (seed/8) ∧
                  HasBalancedScale h R E a level (schedule j).val seed ) ∧
                ∀i j : Fin g,(schedule i).val  ≤  (schedule j).val →
                  ((2^(schedule i).val:ℕ):ℝ)/((2^(schedule j).val:ℕ):ℝ)  ≤  D.thickness^w →
                  HasConditionalTwoScale h R E a level (schedule i).val (schedule j).val tau := by
  obtain ⟨eC,dEngine,heC,heSmall,hdEngine,hEngine⟩ := exists_relative_upper_engine tau w htau hw
  let seed := min (tau/64) (w^2*eC/256)
  have hseed : 0 < seed := lt_min (by positivity) (by positivity)
  have hsTau : seed  ≤  tau/64 := min_le_left _ _
  have hsScale : seed  ≤  w^2*eC/256 := min_le_right _ _
  have hDG : 0 < pairMenuSize d g+g := by unfold pairMenuSize; omega
  obtain ⟨e,zeta,L,eta0,db,he,hzeq,hzeta,hzSeed,hL,heta0,hetaSeed,hdb,hbase⟩ :=
    fixed_balanced_configuration seed w hseed hw (pairMenuSize d g) g hDG
  have hMargins := parameter_margins htau hw heC heSmall hsTau hsScale hzeq hzSeed
  obtain ⟨dProfile,hdProfile,_hdProfile1,hProfileBudget⟩ :=
    exists_relative_population_budget w (w/2) eC zeta (half_pos hw) heC hzeta.le hMargins.2.1
  refine ⟨seed,e,zeta,L,eta0,min db (min dEngine dProfile),hseed,hsTau,he,hzeq,hzeta,hzSeed,hL,
    heta0,hetaSeed,lt_min hdb (lt_min hdEngine hdProfile),?_⟩
  intro n D eta h hK heta hetaSmall hsmall hnear
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hK heta hetaSmall (hsmall.trans (min_le_left _ _)) hnear
  have hrest := hsmall.trans (min_le_right _ _)
  have hDEngine := hrest.trans (min_le_left _ _)
  have hDProfile := hrest.trans (min_le_right _ _)
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
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
  have hCosts := radix_four_cost hd hd1 heta F rad hF hCost
  have hCost41472 : (41472:ℝ)*(rad:ℝ)^4  ≤  D.thickness^(-(seed/4)) := by
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
  have hmwindow : ((2^m:ℕ):ℝ)*D.thickness  ≤  D.thickness^w := by
    simpa only [div_div_eq_mul_div,div_one,mul_comm] using hfine i
  have hfwindow : ((2^f:ℕ):ℝ)*D.thickness  ≤  D.thickness^w := by
    simpa only [div_div_eq_mul_div,div_one,mul_comm] using hfine j
  have hRho : (64/((2^m:ℕ):ℝ))  ≤  1 := by
    obtain ⟨Qm,hsep,_hQP,_hQne,hC,_hCK,hthick,_hShade,_hComp,_hUpper⟩ := hJointM.1
    have hh := hC.1.2.2.1
    rwa [hthick] at hh
  have hDeltaLocal : D.thickness  ≤  (source h R Ep a m p).thickness := by
    change D.thickness  ≤  ((2^m:ℕ):ℝ)*D.thickness/64
    calc
      _ = (64/((2^m:ℕ):ℝ))*(((2^m:ℕ):ℝ)*D.thickness/64) :=
        (NativeSameSourceMultiplicityBalance.actual_scale_product (delta:=D.thickness) (by positivity : 0<2^m)).symm
      _  ≤  1*(((2^m:ℕ):ℝ)*D.thickness/64) := mul_le_mul_of_nonneg_right hRho (by positivity)
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
    (show 2*seed+2*(seed/8)  ≤  tau by linarith [hMargins.2.2.1]) hLower
  change D.thickness^tau*((64/((2^f:ℕ):ℝ))/(64/((2^m:ℕ):ℝ)))^(-extremalExponent)  ≤  _ ∧ _
  rw [←(relative_scale_eq hmf).2]
  exact ⟨hLower',hUpper⟩

/-- Install all caller, master, conditioned, and physical relations before
selecting the sole core. The middle interpolation keeps D, R and E fixed. -/
theorem fixed_middle_two_scale_extra_configuration
    (tau window : ℝ) (htau : 0 < tau) (hw : 0 < window) (hwsmall : window < 1/2)
    (extraCount : ℕ → ℕ) :
    ∃ (seed e zeta : ℝ) (L g : ℕ) (eta0 delta0 : ℝ),
      0 < seed ∧ seed  ≤  tau/1024 ∧
      0 < e ∧ 0 < zeta ∧ zeta  ≤  seed/256 ∧ 0 < L ∧ 0 < g ∧
      1/(g:ℝ) < min window (tau/1000)/4 ∧
      0 < eta0 ∧ eta0  ≤  seed/8 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → 0  ≤  eta → eta  ≤  eta0 →
        D.thickness  ≤  delta0 →
        D.thickness^(-extremalExponent+eta)  ≤  (NativeFiniteKakeyaCounts.multiplicity D).toReal →
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n))
          (original : Fin n → Finset Index)
          (schedule : Fin (g+1) → Fin (level+1)),
          HasOriginalBackbone D original R a level zeta ∧ g  ≤  level ∧
          schedule=canonicalSchedule window tau hw htau g level ∧
          ∀Extra : Fin (extraCount g) → (Fin n × Index) → (Fin n × Index) → Prop,
          (∀i x,Extra i x x) → (∀i x y,Extra i x y → Extra i y x) →
          ∃E : Finset (Fin n × Index),
          (∀i x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Extra i) E x  ≤ 
            (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Extra i) E y) ∧
          IsCore D original R a eta zeta (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L
            (relationMenu h R a schedule (pairRelationMenu h R a schedule
              (NativeInitialExtraRelations.relations D a schedule Extra)))
            (fun j => 2^(schedule j).val) E ∧
          (125*175616*16384:ℝ)*(factor (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L:ℝ)*
            (coreRadix original R L:ℝ)^2*D.thickness^(-eta)  ≤  D.thickness^(-(seed/8)) ∧
          HasUniformFibers E (coreRadix original R L) Prod.snd ∧
          (∀j x y,x∈E → y∈E →
            degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^(schedule j).val)) E x  ≤ 
              (coreRadix original R L)^2*
                degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^(schedule j).val)) E y) ∧
          (∀i j,HasUniformFibers E (coreRadix original R L)
              (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
            HasUniformFibers E (coreRadix original R L)
              (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val)) ∧
          (∀j,HasJointScale h R E a level (schedule j).val e zeta (seed/8) (seed/8) ∧
            HasBalancedScale h R E a level (schedule j).val seed) ∧
          (∀m : ℕ,window*(level:ℝ)  ≤  m → (m:ℝ)  ≤  (1-window)*(level:ℝ) →
            HasMiddleScale h R E a level m tau) ∧
          ∀m f : ℕ,m  ≤  f → window*(level:ℝ)  ≤  m → (f:ℝ)  ≤  (1-window)*(level:ℝ) →
            HasConditionalTwoScale h R E a level m f tau := by
  let w := min window (tau/1000)
  let b := tau/16
  have hw0 : 0 < w := lt_min hw (by positivity)
  have hw0small : w < 1/2 := (min_le_left _ _).trans_lt hwsmall
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨g,dm,hg,hdm,hgrid,hmenu⟩ := exists_source_window_menu w hw0 hw0small
  obtain ⟨seed,e,zeta,L,eta0,db,hseed,hsb,he,_hzeq,hzeta,hzseed,hL,heta0,hetaSeed,hdb,hbase⟩ :=
    fixed_two_scale_configuration b (w/2) hb (half_pos hw0) (extraCount g+(1+(g+1))) (g+1) (by omega)
  have hsTau : seed  ≤  tau/1024 := by dsimp [b] at hsb; linarith
  have hsB : seed  ≤  b := by linarith
  obtain ⟨dc,hdc,_hdc1,hconstantCut⟩ := exists_positive_rpow_absorption_threshold hseed
    (by norm_num : (0:ℝ)  ≤  729) (by norm_num : (0:ℝ)<1)
  let cutoff := min db (min dm (min ((2:ℝ)⁻¹^g) dc))
  have hcut : 0 < cutoff := lt_min hdb (lt_min hdm (lt_min (by positivity) hdc))
  refine ⟨seed,e,zeta,L,g,eta0,cutoff,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hcut,?_⟩
  intro n D eta h hK heta hetaSmall hsmall hnear
  have hcuts : D.thickness  ≤  db ∧ D.thickness  ≤  dm ∧
      D.thickness  ≤  (2:ℝ)⁻¹^g ∧ D.thickness  ≤  dc := by
    simpa only [cutoff,le_min_iff] using hsmall
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hK heta hetaSmall hcuts.1 hnear
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hgl := depth_le_of_dyadic_cutoff level g hdy hcuts.2.2.1
  let schedule := windowSchedule w hw0.le g level
  refine ⟨a,level,R,original,schedule,⟨horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H⟩,
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
  have hQ := radix_sq_le_of_transfer_cost hd hd1 heta
    (factor (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L)
    (coreRadix original R L) hF hcost
  have hQ4 := (radix_four_cost hd hd1 heta
    (factor (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L)
    (coreRadix original R L) hF hcost).1
  have hQCost : (729:ℝ)*(coreRadix original R L:ℝ)^4  ≤  D.thickness^(-b) := by
    calc
      _  ≤  (41472:ℝ)*(coreRadix original R L:ℝ)^4 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _  ≤  D.thickness^(-(2*(seed/8))) := hQ4
      _  ≤  _ := Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  have hconstantSeed : (729:ℝ)  ≤  D.thickness^(-seed) := by
    have hh := hconstantCut D.thickness hd hcuts.2.2.2
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd seed)).mpr hh
  have hconstant : (729:ℝ)  ≤  D.thickness^(-b) := hconstantSeed.trans
    (Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_le_neg hsB))
  have hgridSmall : 1/(g:ℝ)  ≤  tau/4000 := by
    have hwTau : w  ≤  tau/1000 := min_le_right _ _
    nlinarith
  have htwo : 2/(g:ℝ)=2*(1/(g:ℝ)) := by ring
  have hkgrid : (1/(g:ℝ))*extremalExponent  ≤  3*(1/(g:ℝ)) := by
    exact (mul_le_mul_of_nonneg_left extremalExponent_le_three (by positivity)).trans_eq (by ring)
  have hmarginL : seed+(1/(g:ℝ))*extremalExponent  ≤  tau := by nlinarith
  have hmarginU : seed+seed/8+(2/(g:ℝ))*extremalExponent  ≤  tau := by rw [htwo]; nlinarith
  have hmarginC : 2*seed+(2/(g:ℝ))*(4+extremalExponent)  ≤  tau := by rw [htwo]; nlinarith
  have hmarginPair : 2*b+16*(2/(g:ℝ))  ≤  tau := by rw [htwo]; dsimp [b]; nlinarith
  have hdiag : 12*w  ≤  tau := by have hh : w  ≤  tau/1000 := min_le_right _ _; nlinarith
  have hEA : E⊆incidences original := hEcore.1.trans (filter_subset _ _)
  have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hEcore.1 hz)).2
  have hConditioned := core_conditioned_uniformities h original R E L schedule Rel hEcore
  have hOldMenu : ∀j p,(parentEdges D a (2^(schedule j).val) E p).Nonempty →
      D.thickness^seed*(localScale D.thickness (schedule j).val)^(-extremalExponent)  ≤ 
        edgeMultiplicity (parentEdges D a (2^(schedule j).val) E p) ∧
      edgeMultiplicity (parentEdges D a (2^(schedule j).val) E p)  ≤ 
        D.thickness^(-seed)*(localScale D.thickness (schedule j).val)^(-extremalExponent) := by
    intro j p hp
    exact ((hScales j).2.2.2 p hp).2.2
  refine ⟨E,hExtra,hEcore,hcost,hPoint,hOld,hConditioned,hScales,?_,?_⟩
  · intro m hlo hhi
    have hln : (0:ℝ)  ≤  level := Nat.cast_nonneg _
    have hwWindow : w  ≤  window := min_le_left _ _
    have hwLevels := mul_le_mul_of_nonneg_right hwWindow hln
    have hwLevel0 : 0  ≤  w*(level:ℝ) := mul_nonneg hw0.le hln
    have hwindowLevel0 : 0  ≤  window*(level:ℝ) := mul_nonneg hw.le hln
    have hlo0 : w*(level:ℝ)  ≤  m := by nlinarith
    have hhi0 : (m:ℝ)  ≤  (1-w)*(level:ℝ) := by nlinarith
    have hm : m  ≤  level := by
      have hh : (m:ℝ)  ≤  level := by nlinarith
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
    have hln : (0:ℝ)  ≤  level := Nat.cast_nonneg _
    have hwLevels := mul_le_mul_of_nonneg_right (show w  ≤  window from min_le_left _ _) hln
    apply middle_pair_bounds h original horiginal ha R E hEA hER level hdy w hw0 hw0small g
      (coreRadix original R L) hg hgl hgrid b tau hQCost hconstant hdiag hmarginPair
      hConditioned hPairs m f hmf
    · exact hwLevels.trans hmlo
    · nlinarith

/-- Boundary extension of the fixed-source middle producer. Its original
backbone and schedule are returned before the caller supplies actual Extra. -/
theorem fixed_all_two_scale_extra_configuration
    (tau : ℝ) (htau : 0 < tau) (extraCount : ℕ → ℕ) :
    ∃ (seed e zeta : ℝ) (L g : ℕ) (eta0 delta0 : ℝ),
      0 < seed ∧ seed  ≤  tau/16384 ∧
      0 < e ∧ 0 < zeta ∧ zeta  ≤  seed/256 ∧ 0 < L ∧ 0 < g ∧
      1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4 ∧
      0 < eta0 ∧ eta0  ≤  seed/8 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → 0  ≤  eta → eta  ≤  eta0 →
        D.thickness  ≤  delta0 →
        D.thickness^(-extremalExponent+eta)  ≤  (NativeFiniteKakeyaCounts.multiplicity D).toReal →
        ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n))
          (original : Fin n → Finset Index)
          (schedule : Fin (g+1) → Fin (level+1)),
          HasOriginalBackbone D original R a level zeta ∧ g  ≤  level ∧
          schedule=fullSchedule tau htau g level ∧
          ∀Extra : Fin (extraCount g) → (Fin n × Index) → (Fin n × Index) → Prop,
          (∀i x,Extra i x x) → (∀i x y,Extra i x y → Extra i y x) →
          ∃E : Finset (Fin n × Index),
          (∀i x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Extra i) E x  ≤ 
            (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Extra i) E y) ∧
          IsCore D original R a eta zeta (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L
            (relationMenu h R a schedule (pairRelationMenu h R a schedule
              (NativeInitialExtraRelations.relations D a schedule Extra)))
            (fun j => 2^(schedule j).val) E ∧
          (125*175616*16384:ℝ)*(factor (menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1)) (g+1) L:ℝ)*
            (coreRadix original R L:ℝ)^2*D.thickness^(-eta)  ≤  D.thickness^(-(seed/8)) ∧
          HasUniformFibers E (coreRadix original R L) Prod.snd ∧
          (∀j x y,x∈E → y∈E →
            degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^(schedule j).val)) E x  ≤ 
              (coreRadix original R L)^2*
                degree (fun _ : Fin n × Index => 1) (parentPointRel D a (2^(schedule j).val)) E y) ∧
          (∀i j,HasUniformFibers E (coreRadix original R L)
              (conditionedGlobalPair h R a level (schedule i).val (schedule j).val) ∧
            HasUniformFibers E (coreRadix original R L)
              (conditionedGlobalPoint h R a level (schedule i).val (schedule j).val)) ∧
          (∀j,HasJointScale h R E a level (schedule j).val e zeta (seed/8) (seed/8) ∧
            HasBalancedScale h R E a level (schedule j).val seed) ∧
          (∀m : ℕ,boundaryWindow tau*(level:ℝ)  ≤  m → (m:ℝ)  ≤  (1-boundaryWindow tau)*(level:ℝ) →
            HasMiddleScale h R E a level m (tau/16)) ∧
          ∀m f : ℕ,m  ≤  f → f  ≤  level → HasConditionalTwoScale h R E a level m f tau := by
  let w := boundaryWindow tau
  let loss := tau/16
  have hw : 0 < w := boundaryWindow_pos htau
  have hw8 : w  ≤  1/8 := min_le_right _ _
  have hwTau : w  ≤  tau/1000 := min_le_left _ _
  have hwsmall : w < 1/2 := hw8.trans_lt (by norm_num)
  have hloss : 0 < loss := by dsimp [loss]; positivity
  obtain ⟨seed,e,zeta,L,g,eta0,db,hseed,hsLoss,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdb,hbase⟩ :=
    fixed_middle_two_scale_extra_configuration loss w hloss hw hwsmall extraCount
  have hsTau : seed  ≤  tau/16384 := by dsimp [loss] at hsLoss; linarith
  obtain ⟨dc,hdc,_hdc1,hconstantCut⟩ := exists_positive_rpow_absorption_threshold hloss
    (by norm_num : (0:ℝ)  ≤  729) (by norm_num : (0:ℝ)<1)
  refine ⟨seed,e,zeta,L,g,eta0,min db dc,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,lt_min hdb hdc,?_⟩
  intro n D eta h hK heta hetaSmall hsmall hnear
  obtain ⟨a,level,R,original,schedule,hBackbone,hgl,hSchedule,hSelect⟩ :=
    hbase n D eta h hK heta hetaSmall (hsmall.trans (min_le_left _ _)) hnear
  refine ⟨a,level,R,original,schedule,hBackbone,hgl,hSchedule,?_⟩
  intro Extra hExtraRefl hExtraSymm
  obtain ⟨E,hExtra,hCore,hCost,hPoint,hOld,hConditioned,hScales,hFirst,hMiddle⟩ :=
    hSelect Extra hExtraRefl hExtraSymm
  have hd := h.1.2.1
  have horiginal := hBackbone.1
  have hdy := hBackbone.2.1
  have ha := hBackbone.2.2.1
  have hE : E⊆incidences original := hCore.1.trans (filter_subset _ _)
  have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hCore.1 hz)).2
  have hconstant : (729:ℝ)  ≤  D.thickness^(-loss) := by
    have hh := hconstantCut D.thickness hd (hsmall.trans (min_le_right _ _))
    rw [Real.rpow_neg hd.le,←one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hd loss)).mpr hh
  have hgridW : 1/(g:ℝ) < w/4 := hgrid.trans_le
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hlarge := large_level_of_grid w hw g level hg hgridW hgl
  have hdiag : 48*w  ≤  tau := by linarith
  have hmargin : 2*loss+32*w  ≤  tau := by dsimp [loss]; linarith
  refine ⟨E,hExtra,hCore,hCost,hPoint,hOld,hConditioned,hScales,hFirst,?_⟩
  intro m f hmf hfl
  exact all_pair_bounds h original horiginal ha R E hE hER level hdy w loss tau hw hw8 hlarge
    hconstant hdiag hmargin hMiddle m f hmf hfl

/-- Intermediate packaging for the final actual shading/union reader.
The hnear argument is deliberately on this fixed D; the final public caller
must derive it from its genuine source estimates, not ask for it as a certificate.
The raw helper above fixes the backbone before evaluating the menu factory. -/
theorem exists_fixed_source_reference
    (tau : ℝ) (htau : 0 < tau) (extraCount : ℕ → ℕ) :
    ∃ (seed e zeta : ℝ) (L g : ℕ) (eta0 delta0 : ℝ),
      0 < seed ∧ seed  ≤  tau/16384 ∧
      0 < e ∧ 0 < zeta ∧ zeta  ≤  seed/256 ∧ 0 < L ∧ 0 < g ∧
      1/(g:ℝ) < min (boundaryWindow tau) ((tau/16)/1000)/4 ∧
      0 < eta0 ∧ eta0  ≤  seed/8 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → 0  ≤  eta → eta  ≤  eta0 →
        D.thickness  ≤  delta0 →
        D.thickness^(-extremalExponent+eta)  ≤  (NativeFiniteKakeyaCounts.multiplicity D).toReal →
        ∀menu : MenuFactory g (extraCount g),MenuRefl menu → MenuSymm menu →
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.dimension=menuSize (pairMenuSize
            (extraCount g+(1+(g+1))) (g+1)) (g+1) ∧
          HasCallerUniformities ref menu := by
  obtain ⟨seed,e,zeta,L,g,eta0,delta0,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdelta0,Hsource⟩ :=
    fixed_all_two_scale_extra_configuration tau htau extraCount
  refine ⟨seed,e,zeta,L,g,eta0,delta0,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdelta0,?_⟩
  intro n D eta h hK heta hetaSmall hsmall hnear
  obtain ⟨a,level,R,original,schedule,HB,hgl,hSchedule,Hselect⟩ :=
    Hsource n D eta h hK heta hetaSmall hsmall hnear
  intro menu hMenuRefl hMenuSymm
  let Extra := menu n D eta h a level R original schedule
  obtain ⟨E,hExtra,hCore,hCost,hPoint,hOld,hConditioned,hScales,hFirst,hPairs⟩ :=
    Hselect Extra (hMenuRefl n D eta h a level R original schedule)
      (hMenuSymm n D eta h a level R original schedule)
  let ref : Reference h tau htau seed e zeta L g := {
    a:=a, level:=level, R:=R, original:=original, E1:=E, schedule:=schedule,
    dimension:=menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1),
    relations:=relationMenu h R a schedule (pairRelationMenu h R a schedule
      (NativeInitialExtraRelations.relations D a schedule Extra)),
    backbone:=HB, grid_depth:=hgl, schedule_eq:=hSchedule, core:=hCore, cost:=hCost,
    point:=hPoint, parent_point:=hOld, conditioned:=hConditioned, scales:=hScales,
    middle:=hFirst, pairs:=hPairs }
  exact ⟨ref,rfl,hExtra⟩

end NativeFixedSourceReference

end -- anonymous noncomputable source-unit section

/- Source unit native_fixed_source_near_body.UNVERIFIED.lean
   SHA256 0b7bfcf99b53b6d24426bda5becd2aff64beb4f8d786e5c4f292c0eba00f0ae5 -/
/- UNVERIFIED fixed-source multiplicity reader. Its premises are actual
shading/union bounds and the remaining scalar payment, not a desired near
multiplicity conclusion. It will be joined to the deterministic Reference
constructor without choosing another source. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeFixedSourceReference
open Classical Finset MeasureTheory StickyKakeya4 NativeFiniteKakeyaCounts
open NativeFixedCompactKakeyaExponent
open scoped ENNReal

/-- Positive actual shading and a finite actual union imply genuine finite,
positive denominator. These are proved before converting multiplicity toReal. -/
theorem union_pos_of_shading_lower {n : ℕ} {D : FiniteScaleSource n} {eta L : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hL : 0< L)
    (hshade : ENNReal.ofReal L ≤ wzTotalShadingVolume D) :
    0< volume (sourceUnion D) := by
  have hW : ∀i,D.weight i=1 := h.1.2.2.2.2.2.1
  have htotal := total_shading_le_card_mul_union D hW
  by_contra hnot
  have hz : volume (sourceUnion D)=0 := le_antisymm (le_of_not_gt hnot) (show (0:ℝ ≥ 0∞)  ≤  volume (sourceUnion D) from bot_le)
  rw [hz,mul_zero] at htotal
  have hbad : ENNReal.ofReal L ≤ 0 := hshade.trans htotal
  have hpos : (0:ℝ ≥ 0∞) < ENNReal.ofReal L := ENNReal.ofReal_pos.mpr hL
  exact (not_lt_of_ge hbad) hpos

/-- The same source's actual count-derived shading lower and actual union
upper give its near-extremal multiplicity. U can be the literal remembered
unionConstant(KXY), and L the remembered relation's exact shading lower. -/
theorem native_near_of_volume_bounds {n : ℕ} {D : FiniteScaleSource n} {eta L U : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hU : 0< U)
    (hshade : ENNReal.ofReal L ≤ wzTotalShadingVolume D)
    (hunion : volume (sourceUnion D) ≤ ENNReal.ofReal (U*D.thickness^extremalExponent))
    (hpaid : U*D.thickness^eta ≤ L) :
    D.thickness^(-extremalExponent+eta) ≤ (multiplicity D).toReal := by
  have hd : 0< D.thickness := h.1.2.1
  have hL : 0< L := (mul_pos hU (Real.rpow_pos_of_pos hd eta)).trans_le hpaid
  have hUnionPos := union_pos_of_shading_lower h hL hshade
  have hUnionTop : volume (sourceUnion D)≠⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hunion
  have hShadeTop : wzTotalShadingVolume D≠⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (NativeFixedCompactMultiplicity.total_shading_upper h)
  have hden : 0<(volume (sourceUnion D)).toReal := ENNReal.toReal_pos hUnionPos.ne' hUnionTop
  have hlo : L ≤ (wzTotalShadingVolume D).toReal := by
    have hh := ENNReal.toReal_mono hShadeTop hshade
    simpa only [ENNReal.toReal_ofReal hL.le] using hh
  have hup : (volume (sourceUnion D)).toReal ≤ U*D.thickness^extremalExponent := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hunion
    simpa only [ENNReal.toReal_ofReal (mul_pos hU (Real.rpow_pos_of_pos hd _)).le] using hh
  have hpower : D.thickness^(-extremalExponent+eta)*(U*D.thickness^extremalExponent)=
      U*D.thickness^eta := by
    calc
      _ = U*(D.thickness^(-extremalExponent+eta)*D.thickness^extremalExponent) := by ring
      _ = U*D.thickness^((-extremalExponent+eta)+extremalExponent) := by rw [←Real.rpow_add hd]
      _ = U*D.thickness^eta := by congr 2; ring
  have hprod : D.thickness^(-extremalExponent+eta)*(volume (sourceUnion D)).toReal ≤ 
      (wzTotalShadingVolume D).toReal := by
    calc
      _  ≤  D.thickness^(-extremalExponent+eta)*(U*D.thickness^extremalExponent) :=
        mul_le_mul_of_nonneg_left hup (Real.rpow_nonneg hd.le _)
      _ = U*D.thickness^eta := hpower
      _  ≤  L := hpaid
      _  ≤  _ := hlo
  rw [NativeFiniteKakeyaCounts.multiplicity,ENNReal.toReal_div]
  exact (le_div_iff₀ hden).mpr hprod

end NativeFixedSourceReference

end -- anonymous noncomputable source-unit section

/- Source unit native_fixed_source_reference_public.UNVERIFIED.lean
   SHA256 c5195b78b23e7176f91e04e2e6fd9dea5a5f09009114b3b5013ca13e322871b9 -/
/- UNVERIFIED public fixed-source entrance from actual volume bounds. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeFixedSourceReference
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeFixedCompactKakeyaExponent NativeGenericReferenceData
open NativeExtraQueriedRankConfiguration NativeJointUniformCoarseRelations NativeConditionedPairMenu
open NativeAllTwoScaleConfiguration NativeUnitParentNormalization

/-- All analytic/menu choices precede the given source. Actual shading and
union estimates, with their scalar payment, are the only near-extremality
inputs. The source D is retained literally. Its chosen cell presentation is
proved equal to the supplied original cells, so every later E1 edge retains
the inherited remembered-height and higher-plane witnesses on those cells.
This does not assert lower-profile inheritance under subsequent cuts. -/
theorem exists_reference_from_volume_bounds
    (tau : ℝ) (htau : 0< tau) (extraCount : ℕ → ℕ) :
    ∃(seed e zeta : ℝ) (L g : ℕ) (eta0 delta0 : ℝ),
      0< seed ∧ seed ≤ tau/16384 ∧ 0< e ∧ 0< zeta ∧ zeta ≤ seed/256 ∧ 0< L ∧ 0< g ∧
      1/(g:ℝ)< min (boundaryWindow tau) ((tau/16)/1000)/4 ∧
      0< eta0 ∧ eta0 ≤ seed/8 ∧ 0< delta0 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i∈fixedCompactClass) → 0 ≤ eta → eta ≤ eta0 → D.thickness ≤ delta0 →
        ∀(shadeLower unionCost : ℝ),0< unionCost →
        ENNReal.ofReal shadeLower ≤ wzTotalShadingVolume D →
        volume (sourceUnion D) ≤ ENNReal.ofReal (unionCost*D.thickness^extremalExponent) →
        unionCost*D.thickness^eta ≤ shadeLower →
        ∀cells : Fin n → Finset Index,
        (∀i,D.shading i=wzCellShading (mesh D) cells i) →
        ∀menu : MenuFactory g (extraCount g),MenuRefl menu → MenuSymm menu →
        ∃ref : Reference h tau htau seed e zeta L g,
          ref.dimension=menuSize (pairMenuSize (extraCount g+(1+(g+1))) (g+1)) (g+1) ∧
          HasCallerUniformities ref menu ∧ ref.original=cells ∧
          ref.E1⊆incidences cells ∧
          D.thickness^(-extremalExponent+eta) ≤ (NativeFiniteKakeyaCounts.multiplicity D).toReal ∧
          D.thickness^(-extremalExponent+seed/4) ≤ NativeIncidenceMultiplicityTower.multiplicity ref.E1 := by
  obtain ⟨seed,e,zeta,L,g,eta0,delta0,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdelta0,H⟩ := exists_fixed_source_reference tau htau extraCount
  refine ⟨seed,e,zeta,L,g,eta0,delta0,hseed,hsTau,he,hzeta,hzseed,hL,hg,hgrid,
    heta0,hetaSeed,hdelta0,?_⟩
  intro n D eta h hK heta hetaSmall hsmall shadeLower unionCost hU hShade hUnion hPay
    cells hCells menu hMenuRefl hMenuSymm
  have hnear := native_near_of_volume_bounds h hU hShade hUnion hPay
  obtain ⟨ref,hDimension,hCaller⟩ := H n D eta h hK heta hetaSmall hsmall hnear menu hMenuRefl hMenuSymm
  have hOriginal : ref.original=cells := by
    apply NativeOriginalCellPresentationUnique.cells_eq_of_shading_eq (s:=mesh D) (half_pos h.1.2.1)
    intro i
    exact (ref.backbone.1 i).symm.trans (hCells i)
  have hSubset : ref.E1⊆incidences cells := by
    rw [←hOriginal]
    exact ref.core.1.trans (filter_subset _ _)
  exact ⟨ref,hDimension,hCaller,hOriginal,hSubset,hnear,
    NativeGenericReferenceData.global_near ref heta (hetaSmall.trans hetaSeed) hnear⟩

end NativeFixedSourceReference

end -- anonymous noncomputable source-unit section
