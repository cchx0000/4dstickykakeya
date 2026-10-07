import Theorems.Thm_StickyKakeya4_native_joint_absorbed_near_balance
import Theorems.Thm_StickyKakeya4_native_near_target_loss

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeBalancedConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization NativeLocalParentSource NativeFixedCompactKakeyaExponent
open NativeJointUniformCoarseRelations NativeJointQuantitativeMenu NativeJointAbsorbedNearBalance
open NativeSameSourceMultiplicityBalance NativeNearTargetLoss SelfUniform
open scoped BigOperators ENNReal

/-- Both actual physical scales match the fixed compact extremal exponent,
up to the requested original-delta tolerance, on one unchanged E. -/
def HasBalancedScale {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ) (tau : ℝ) : Prop :=
  let rho := 64/((2^m:ℕ):ℝ)
  let eps := ((2^m:ℕ):ℝ)*D.thickness/64
  let C := (NativeFiniteKakeyaCounts.multiplicity (NativeFullCoarseShadow.fullSource h R a level m E)).toReal
  D.thickness^tau*rho^(-extremalExponent) ≤ C ∧ C≤D.thickness^(-tau)*rho^(-extremalExponent) ∧
  ∀p,(parentEdges D a (2^m) E p).Nonempty →
    let S := (NativeFiniteKakeyaCounts.multiplicity (source h R (parentEdges D a (2^m) E p) a m p)).toReal
    D.thickness^tau*eps^(-extremalExponent) ≤ S ∧ S≤D.thickness^(-tau)*eps^(-extremalExponent) ∧
    D.thickness^tau*eps^(-extremalExponent) ≤ NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E p) ∧
    NativeIncidenceMultiplicityTower.multiplicity (parentEdges D a (2^m) E p) ≤
      D.thickness^(-tau)*eps^(-extremalExponent)

/-- Explicit parameter margins convert the derived pure near bounds into
the same requested tolerance on both complementary physical scales. -/
theorem pure_near_to_balanced {n : ℕ} {D : FiniteScaleSource n} {eta a e zeta tau : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hm : m≤level)
    (htau : 0<tau) (heta : eta≤tau/8) (hzeta : zeta≤tau/256)
    (hjoint : HasJointScale h R E a level m e zeta (tau/8) (tau/8))
    (hnear : HasPureNearScale h R E a level m eta (tau/8) zeta (tau/8)) :
    HasBalancedScale h R E a level m tau := by
  have hd := h.1.2.1
  have hd1 := h.1.2.2.1
  have hr : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  have heps : (0:ℝ)<((2^m:ℕ):ℝ)*D.thickness/64 := by positivity
  have hscale := actual_scale_product (delta:=D.thickness) (by positivity : 0<2^m)
  have hr1 : (64/((2^m:ℕ):ℝ))≤1 := by
    obtain ⟨Q,hsep,_hQP,_hQne,hC,_hCK,hthick,_hshade,_hcompare,_hupper⟩ := hjoint.1
    have hh := hC.1.2.2.1
    rwa [hthick] at hh
  have heps1 : ((2^m:ℕ):ℝ)*D.thickness/64≤1 := by
    have hh : ((2^m:ℕ):ℝ)*D.thickness≤1 := by
      rw [NativeLocalParentScales.relative_scale hdy hm]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hdr : D.thickness≤64/((2^m:ℕ):ℝ) := by
    calc
      _ = (64/((2^m:ℕ):ℝ))*(((2^m:ℕ):ℝ)*D.thickness/64) := hscale.symm
      _ ≤ (64/((2^m:ℕ):ℝ))*1 := mul_le_mul_of_nonneg_left heps1 hr.le
      _ = _ := mul_one _
  have hde : D.thickness≤((2^m:ℕ):ℝ)*D.thickness/64 := by
    calc
      _ = (64/((2^m:ℕ):ℝ))*(((2^m:ℕ):ℝ)*D.thickness/64) := hscale.symm
      _ ≤ 1*(((2^m:ℕ):ℝ)*D.thickness/64) := mul_le_mul_of_nonneg_right hr1 heps.le
      _ = _ := one_mul _
  have hcoarseReal : (NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level m E)).toReal ≤
        D.thickness^(-(tau/8))*(64/((2^m:ℕ):ℝ))^(-extremalExponent-tau/8) := by
    have hfinite : (ENNReal.ofReal D.thickness).rpow (-(tau/8))*
        (ENNReal.ofReal (64/((2^m:ℕ):ℝ))).rpow (-extremalExponent-tau/8) ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top)
        (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top)
    have hh := ENNReal.toReal_mono hfinite hjoint.2.1
    simpa only [ENNReal.rpow_eq_pow,ENNReal.toReal_mul,←ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal hd.le,ENNReal.toReal_ofReal hr.le] using hh
  refine ⟨lower_with_target_loss hd hd1 hr (show eta+eta+2*zeta+tau/8≤tau by linarith) hnear.1,
    upper_with_target_loss (gamma:=tau/8) (loss:=tau/8) hd hd1 hr hdr (by positivity) (by linarith) hcoarseReal,?_⟩
  intro p hp
  have hlo := lower_with_target_loss hd hd1 heps (show eta+tau/8+eta+3*zeta+tau/8≤tau by linarith)
    (hnear.2 p hp).1
  have hOldLower := lower_with_target_loss hd hd1 heps
    (show eta+tau/8+2*zeta+tau/8≤tau by linarith) (hnear.2 p hp).2
  obtain ⟨_hinput,_hfixed,_htrace,hupper,hparent⟩ := hjoint.2.2 p hp
  have hfinite : (ENNReal.ofReal (((2^m:ℕ):ℝ)*D.thickness/64)).rpow (-extremalExponent-tau/8) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr heps) ENNReal.ofReal_ne_top
  have hupperReal : (NativeFiniteKakeyaCounts.multiplicity
      (source h R (parentEdges D a (2^m) E p) a m p)).toReal ≤
        D.thickness^(-(0:ℝ))*(((2^m:ℕ):ℝ)*D.thickness/64)^(-extremalExponent-tau/8) := by
    have hh := ENNReal.toReal_mono hfinite hupper
    simpa only [neg_zero,Real.rpow_zero,one_mul,ENNReal.rpow_eq_pow,
      ←ENNReal.toReal_rpow,ENNReal.toReal_ofReal heps.le] using hh
  exact ⟨hlo,upper_with_target_loss (gamma:=0) (loss:=tau/8) hd hd1 heps hde (by positivity) (by linarith) hupperReal,
    hOldLower,upper_with_target_loss (gamma:=tau/8) (loss:=tau/8) hd hd1 heps hde
      (by positivity) (by linarith) hparent⟩

/-- Genuine fixed-compact near-extremizers yield one original R and one E
with actual native upper bounds and two-sided matched multiplicities at every
scheduled scale and every active parent. The only analytic assumption is
positivity of the FIXED compact exponent, not an unrestricted exponent identity. -/
theorem exists_balanced_configuration (hk : 0<extremalExponent)
    (tau window : ℝ) (htau : 0<tau) (hw : 0<window)
    (d g : ℕ) (hdg : 0<d+g) :
    ∃ (e zeta : ℝ) (L : ℕ),0<e ∧ zeta=window*e/32 ∧ 0<zeta ∧ zeta≤tau/256 ∧ 0<L ∧
      ∀ etaBound deltaBound : ℝ,0<etaBound → 0<deltaBound →
      ∃ (eta : ℝ) (n : ℕ) (D : FiniteScaleSource n)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0<eta ∧ eta<etaBound ∧ eta<tau/8 ∧ D.thickness<deltaBound ∧
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
            (∀j,1/((2^(schedule j).val:ℕ):ℝ) ≤ D.thickness^window) →
            (∀j,D.thickness/(1/((2^(schedule j).val:ℕ):ℝ)) ≤ D.thickness^window) →
            ∀ (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop),
              (∀j x,Rel j x x) → (∀j x y,Rel j x y → Rel j y x) →
              ∃ E, IsCore D original R a eta zeta (menuSize d g) g L
                (relationMenu h R a schedule Rel) (fun j => 2^(schedule j).val) E ∧
                (125*175616*16384:ℝ)*(factor (menuSize d g) g L:ℝ)*(coreRadix original R L:ℝ)^2*
                  D.thickness^(-eta) ≤ D.thickness^(-(tau/8)) ∧
                (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
                  (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
                (∀m : ℕ,1/((2^m:ℕ):ℝ) ≤ D.thickness^window →
                  D.thickness/(1/((2^m:ℕ):ℝ)) ≤ D.thickness^window →
                    HasCoarseScale h R E a level m e zeta (tau/8) (tau/8)) ∧
                ∀j,
                  HasJointScale h R E a level (schedule j).val e zeta (tau/8) (tau/8) ∧
                  HasBalancedScale h R E a level (schedule j).val tau := by
  have ht8 : 0<tau/8 := by positivity
  obtain ⟨e,zeta,L,eta0,delta0,he,hzeq,hzeta,hztheta,hL,_hlarge,heta0,_hetaz,hdelta0,hbase⟩ :=
    joint_absorbed_near_balance (tau/8) window (tau/8) ht8 hw ht8 d g hdg
  have hzsmall : zeta≤tau/256 := by linarith
  refine ⟨e,zeta,L,he,hzeq,hzeta,hzsmall,hL,?_⟩
  intro etaBound deltaBound heB hdB
  obtain ⟨eta,heta,hetaSmall,n,D,hd,hsmall,h,hK,hvol,hnear,hupper⟩ :=
    NativeFixedCompactMultiplicity.exists_matched_normalized_source hk
      (lt_min heB (lt_min heta0 ht8)) (lt_min hdB hdelta0) ht8
  have heta0' : eta≤eta0 := (hetaSmall.le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have heta8 : eta<tau/8 := (hetaSmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hfinite : NativeFiniteKakeyaCounts.multiplicity D≠⊤ := ne_top_of_le_ne_top
    (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top) hupper
  have hnearReal : D.thickness^(-extremalExponent+eta) ≤
      (NativeFiniteKakeyaCounts.multiplicity D).toReal := by
    have hh := ENNReal.toReal_mono hfinite hnear
    simpa only [ENNReal.rpow_eq_pow,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal hd.le] using hh
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hK (hsmall.le.trans (min_le_right _ _)) heta0' eta hnearReal
  refine ⟨eta,n,D,h,heta,hetaSmall.trans_le (min_le_left _ _),heta8,hsmall.trans_le (min_le_left _ _),
    hK,hvol,hnearReal,a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro schedule hcoarse hfine Rel hrefl hsym
  obtain ⟨E,hEcore,hcost,hOld,hcoarseAll,hscales⟩ := hcore schedule hcoarse hfine Rel hrefl hsym
  refine ⟨E,hEcore,hcost,hOld,hcoarseAll,?_⟩
  intro j
  obtain ⟨hjoint,hpure⟩ := hscales j
  exact ⟨hjoint,pure_near_to_balanced h R E level (schedule j).val hdy
    (Nat.le_of_lt_succ (schedule j).isLt) htau heta8.le hzsmall hjoint hpure⟩

end NativeBalancedConfiguration
