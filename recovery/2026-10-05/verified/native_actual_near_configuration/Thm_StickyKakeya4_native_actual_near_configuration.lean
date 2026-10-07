import Theorems.Thm_StickyKakeya4_native_joint_actual_near_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeActualNearConfiguration
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization
open NativeJointUniformCoarseRelations NativeJointActualNearBalance
open NativeFixedCompactKakeyaExponent SelfUniform
open scoped BigOperators ENNReal

/-- An actual fixed-compact normalized near-extremizer supplies every source
premise of the same-E joint near construction. Thus neither an original near
source nor a matched output profile is assumed as a caller certificate. -/
theorem exists_actual_near_configuration (hk : 0 < extremalExponent)
    (epsilon window theta : ℝ) (hepsilon : 0 < epsilon)
    (hw : 0 < window) (htheta : 0 < theta) (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (e zeta : ℝ) (L : ℕ),0 < e ∧ zeta=window*e/32 ∧ 0 < zeta ∧ 0 < L ∧
      ∀ etaBound deltaBound : ℝ,0<etaBound → 0<deltaBound →
      ∃ (eta : ℝ) (n : ℕ) (D : FiniteScaleSource n)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0<eta ∧ eta<etaBound ∧ D.thickness<deltaBound ∧
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
                  D.thickness^(-eta) ≤ D.thickness^(-theta) ∧
                (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
                  (coreRadix original R L)^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
                ∀j,
                  HasJointScale h R E a level (schedule j).val e zeta theta epsilon ∧
                  HasNearScale h R E a level (schedule j).val eta theta epsilon
                    (factor (menuSize d g) g L) (coreRadix original R L) := by
  obtain ⟨e,zeta,L,eta0,delta0,he,hzeq,hzeta,hL,heta0,hdelta0,hbase⟩ :=
    joint_actual_near_balance epsilon window theta hepsilon hw htheta d g hdg
  refine ⟨e,zeta,L,he,hzeq,hzeta,hL,?_⟩
  intro etaBound deltaBound heB hdB
  obtain ⟨eta,heta,hetaSmall,n,D,hd,hsmall,h,hK,hvol,hnear,hupper⟩ :=
    NativeFixedCompactMultiplicity.exists_matched_normalized_source hk
      (lt_min heB heta0) (lt_min hdB hdelta0) hepsilon
  have hfinite : NativeFiniteKakeyaCounts.multiplicity D≠⊤ := ne_top_of_le_ne_top
    (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top) hupper
  have hnearReal : D.thickness^(-extremalExponent+eta) ≤
      (NativeFiniteKakeyaCounts.multiplicity D).toReal := by
    have hh := ENNReal.toReal_mono hfinite hnear
    simpa only [ENNReal.rpow_eq_pow,←ENNReal.toReal_rpow,ENNReal.toReal_ofReal hd.le] using hh
  refine ⟨eta,n,D,h,heta,hetaSmall.trans_le (min_le_left _ _),hsmall.trans_le (min_le_left _ _),
    hK,hvol,hnearReal,?_⟩
  exact hbase n D eta h hK (hsmall.le.trans (min_le_right _ _))
    (hetaSmall.le.trans (min_le_right _ _)) eta hnearReal

end NativeActualNearConfiguration
