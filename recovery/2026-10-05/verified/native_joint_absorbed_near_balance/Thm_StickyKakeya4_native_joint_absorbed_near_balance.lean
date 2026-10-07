import Theorems.Thm_StickyKakeya4_native_joint_quantitative_menu
import Theorems.Thm_StickyKakeya4_native_actual_all_parent_near_balance
import Theorems.Thm_StickyKakeya4_native_near_power_cleanup
import Theorems.Thm_StickyKakeya4_native_old_parent_near_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeJointAbsorbedNearBalance
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization
open NativeLocalParentSource NativeSameSourceMultiplicityBalance NativeSameSourceBalanceAbsorption
open NativeActualSameSourceNearBalance NativeActualAllParentNearBalance NativeAllParentNearBalance
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeNearPowerCleanup
open NativeFixedCompactKakeyaExponent SelfUniform NativeOldParentNearLower
open scoped BigOperators ENNReal

/-- Pure power lower bounds on the actual full coarse source and every actual
local parent, after all finite-menu costs are paid from original geometry. -/
def HasPureNearScale {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ)
    (nearTheta gamma zeta loss : ℝ) : Prop :=
  D.thickness^(nearTheta+eta+2*zeta+loss)*(64/((2^m:ℕ):ℝ))^(-extremalExponent) ≤
    (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E)).toReal ∧
  ∀p,(parentEdges D a (2^m) E p).Nonempty →
    D.thickness^(nearTheta+gamma+eta+3*zeta+loss)*(((2^m:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) ≤
      (NativeFiniteKakeyaCounts.multiplicity (source h R (parentEdges D a (2^m) E p) a m p)).toReal ∧
    D.thickness^(nearTheta+gamma+2*zeta+loss)*(((2^m:ℕ):ℝ)*D.thickness/64)^(-extremalExponent) ≤
      NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E p)

/-- Source-facing pure near balance, with one R and one E. All finite costs
are absorbed using original source cardinality before selecting the source;
no output profile, density, or matching certificate is supplied. -/
theorem joint_absorbed_near_balance
    (epsilon window theta : ℝ) (hepsilon : 0 < epsilon)
    (hw : 0 < window) (htheta : 0 < theta) (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (e zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      0 < e ∧ zeta=window*e/32 ∧ 0 < zeta ∧ zeta≤theta/32 ∧ 0 < L ∧
      16/zeta<(L:ℝ) ∧ 0 < eta0 ∧ eta0≤zeta/16 ∧ 0 < delta0 ∧
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        (∀i,D.line i ∈ fixedCompactClass) → D.thickness ≤ delta0 → eta ≤ eta0 →
        ∀ nearTheta : ℝ, D.thickness^(-extremalExponent+nearTheta) ≤
          (NativeFiniteKakeyaCounts.multiplicity D).toReal →
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
            (∀j,1/((2^(schedule j).val:ℕ):ℝ) ≤ D.thickness^window) →
            (∀j,D.thickness/(1/((2^(schedule j).val:ℕ):ℝ)) ≤ D.thickness^window) →
            ∀ (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
              (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
              ∃ E, IsCore D original R a eta zeta (menuSize d g) g L
                (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E ∧
                (125*175616*16384:ℝ)*(factor (menuSize d g) g L:ℝ)*(coreRadix original R L:ℝ)^2*
                  D.thickness^(-eta) ≤ D.thickness^(-theta) ∧
                (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
                  (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
                (∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^window →
                  D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^window →
                    HasCoarseScale h R E a level m e zeta theta epsilon) ∧
                ∀j,
                  HasJointScale h R E a level (schedule j).val e zeta theta epsilon ∧
                  HasPureNearScale h R E a level (schedule j).val nearTheta theta zeta epsilon := by
  obtain ⟨e,zeta,L,eta0,db,he,hzeq,hzeta,hztheta,hL,hlarge,heta0,hetaz,hdb,hbase⟩ :=
    joint_quantitative_relations epsilon window theta hepsilon hw htheta d g hdg
  obtain ⟨d6,hd6,hcut6⟩ := exists_balance_cutoff hzeta (factor (menuSize d g) g L) L hL hlarge
  obtain ⟨d8,hd8,hcut8⟩ := exists_all_parent_balance_cutoff hzeta (factor (menuSize d g) g L) L hL hlarge
  refine ⟨e,zeta,L,eta0,min db (min d6 d8),he,hzeq,hzeta,hztheta,hL,hlarge,
    heta0,hetaz,lt_min hdb (lt_min hd6 hd8),?_⟩
  intro n D eta h hDK hsmall heta nearTheta hnear
  have hrest := hsmall.trans (min_le_right _ _)
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hDK (hsmall.trans (min_le_left _ _)) heta
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro schedule hcoarse hfine Rel hrefl hsym
  obtain ⟨E,hEcore,hcost,hOld,hcoarseAll,hscales⟩ := hcore schedule hcoarse hfine Rel hrefl hsym
  refine ⟨E,hEcore,hcost,hOld,hcoarseAll,?_⟩
  have hmenu : 0 < menuSize d g+g := by unfold menuSize; omega
  have hA : retained original R⊆incidences original := filter_subset _ _
  have hAne : (retained original R).Nonempty := hEcore.2.1.mono hEcore.1
  have hc6 := hcut6 n D eta h (hrest.trans (min_le_left _ _)) original horiginal
    (retained original R) hA hAne
  have hc8 := hcut8 n D eta h (hrest.trans (min_le_right _ _)) original horiginal
    (retained original R) hA hAne
  intro j
  obtain ⟨hjoint,hpair,hpoint,hformal,_hbridge,_hcomp⟩ := hscales j
  have hd := h.1.2.1
  have hr : (0:ℝ)<64/((2^(schedule j).val:ℕ):ℝ) := by positivity
  have hlocal : ∀p,(parentEdges D a (2^(schedule j).val) E p).Nonempty →
      (NativeFiniteKakeyaCounts.multiplicity
        (source h R (parentEdges D a (2^(schedule j).val) E p) a (schedule j).val p)).toReal ≤
          (((2^(schedule j).val:ℕ):ℝ)*D.thickness/64)^(-extremalExponent-epsilon) := by
    intro p hp
    obtain ⟨hinput,_hfixed,_htrace,hupper,_hparent⟩ := hjoint.2.2 p hp
    have heps : (0:ℝ)<((2^(schedule j).val:ℕ):ℝ)*D.thickness/64 := hinput.1.2.1
    have hfinite : (ENNReal.ofReal (((2^(schedule j).val:ℕ):ℝ)*D.thickness/64)).rpow
        (-extremalExponent-epsilon) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr heps) ENNReal.ofReal_ne_top
    have hh := ENNReal.toReal_mono hfinite hupper
    simpa only [ENNReal.rpow_eq_pow,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal heps.le] using hh
  have hcoarseReal : (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level (schedule j).val E)).toReal ≤
        D.thickness^(-theta)*(64/((2^(schedule j).val:ℕ):ℝ))^(-extremalExponent-epsilon) := by
    have hfinite : (ENNReal.ofReal D.thickness).rpow (-theta)*
        (ENNReal.ofReal (64/((2^(schedule j).val:ℕ):ℝ))).rpow (-extremalExponent-epsilon) ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top)
        (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top)
    have hh := ENNReal.toReal_mono hfinite hjoint.2.1
    simpa only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,←ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hd.le,ENNReal.toReal_ofReal hr.le] using hh
  have hb := actual_same_source_near_balance h original horiginal ha R E
    (menuSize d g) g L level hmenu hdy (relationMenu h R a schedule Rel)
    schedule hEcore j hnear hpair hpoint hlocal hcoarseReal
  have heps : (0:ℝ)<((2^(schedule j).val:ℕ):ℝ)*D.thickness/64 := by positivity
  have hscale := actual_scale_product (delta:=D.thickness) (by positivity : 0<2^(schedule j).val)
  have hr1 : (64/((2^(schedule j).val:ℕ):ℝ))≤1 := by
    obtain ⟨Q,hsep,_hQP,_hQne,hC,_hCK,hthick,_hshade,_hcompare,_hupper⟩ := hjoint.1
    have hh := hC.1.2.2.1
    rwa [hthick] at hh
  refine ⟨hjoint,?_,?_⟩
  · exact absorb_and_remove_error (power:=nearTheta+eta) (costLoss:=2*zeta)
      hd hr heps hscale hr1 hepsilon.le ENNReal.toReal_nonneg hb.1 hc6
  intro p hp
  have hlo := actual_all_parent_near_lower h original horiginal ha R E
    (menuSize d g) g L level hmenu hdy (relationMenu h R a schedule Rel)
    schedule hEcore j hnear hpair hpoint hformal hcoarseReal p hp
  have heps1 : ((2^(schedule j).val:ℕ):ℝ)*D.thickness/64≤1 := (hjoint.2.2 p hp).1.1.2.2.1
  refine ⟨absorb_and_remove_error (power:=nearTheta+theta+eta) (costLoss:=3*zeta)
    hd heps hr (by simpa only [mul_comm] using hscale)
    heps1 hepsilon.le ENNReal.toReal_nonneg hlo hc8,?_⟩
  have hOldLower := actual_old_parent_near_lower h original horiginal ha R E
    (menuSize d g) g L level hmenu hdy (relationMenu h R a schedule Rel)
    schedule hEcore j hnear hpair hpoint hformal hcoarseReal p hp
  have hF : 0<factor (menuSize d g) g L := by
    have hb : 0 < menuSize d g+g+g := by omega
    unfold factor NativeLocalPairUniformCore.retentionCost
    positivity
  have hOldCost := (old_cost_le_balance (factor (menuSize d g) g L) (coreRadix original R L) hF).trans hc6
  exact absorb_and_remove_error (power:=nearTheta+theta) (costLoss:=2*zeta)
    hd heps hr (by simpa only [mul_comm] using hscale) heps1 hepsilon.le
    (multiplicity_nonneg _) hOldLower hOldCost

end NativeJointAbsorbedNearBalance
