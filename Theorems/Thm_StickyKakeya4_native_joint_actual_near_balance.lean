import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations
import Theorems.Thm_StickyKakeya4_native_actual_all_parent_near_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeJointActualNearBalance
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentDensityCore
open NativeUnitParentNormalization
open NativeLocalParentSource NativeSameSourceMultiplicityBalance NativeSameSourceBalanceAbsorption
open NativeActualSameSourceNearBalance NativeActualAllParentNearBalance
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent SelfUniform
open scoped BigOperators ENNReal

/-- The actual physical near bounds, with their complete finite losses. -/
def HasNearScale {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (level m : ℕ)
    (nearTheta gamma loss : ℝ) (F rad : ℕ) : Prop :=
  let rho := 64/((2^m:ℕ):ℝ)
  let eps := ((2^m:ℕ):ℝ)*D.thickness/64
  D.thickness^(nearTheta+eta)*eps^loss*rho^(-extremalExponent) ≤
    (balanceCost*(F:ℝ)^2*(rad:ℝ)^6)*(NativeFiniteKakeyaCounts.multiplicity
      (NativeFullCoarseShadow.fullSource h R a level m E)).toReal ∧
  ∀p,(parentEdges D a (2^m) E p).Nonempty →
    D.thickness^(nearTheta+gamma+eta)*rho^loss*eps^(-extremalExponent) ≤
      (balanceCost*(F:ℝ)^2*(rad:ℝ)^8)*(NativeFiniteKakeyaCounts.multiplicity
        (source h R (parentEdges D a (2^m) E p) a m p)).toReal

/-- Source-facing same-E near-extremal balance. One joint construction gives
both actual upper bounds, all physical and formal label uniformities, the
full physical coarse lower, and a physical local lower on EVERY active parent.
No output density, admission, or matching-multiplicity certificate is assumed. -/
theorem joint_actual_near_balance
    (epsilon window theta : ℝ) (hepsilon : 0 < epsilon)
    (hw : 0 < window) (htheta : 0 < theta) (d g : ℕ) (hdg : 0 < d+g) :
    ∃ (e zeta : ℝ) (L : ℕ) (eta0 delta0 : ℝ),
      0 < e ∧ zeta=window*e/32 ∧ 0 < zeta ∧ 0 < L ∧
      0 < eta0 ∧ 0 < delta0 ∧
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
                ∀j,
                  HasJointScale h R E a level (schedule j).val e zeta theta epsilon ∧
                  HasNearScale h R E a level (schedule j).val nearTheta theta epsilon
                    (factor (menuSize d g) g L) (coreRadix original R L) := by
  obtain ⟨e,zeta,L,eta0,delta0,he,hzeq,hzeta,hL,heta0,hdelta0,hbase⟩ :=
    joint_uniform_coarse_relations epsilon window theta hepsilon hw htheta d g hdg
  refine ⟨e,zeta,L,eta0,delta0,he,hzeq,hzeta,hL,heta0,hdelta0,?_⟩
  intro n D eta h hDK hsmall heta nearTheta hnear
  obtain ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,hcore⟩ :=
    hbase n D eta h hDK hsmall heta
  refine ⟨a,level,R,original,horiginal,hdy,ha,hR,hhalf,hshade,hdensity,hCW,H,?_⟩
  intro schedule hcoarse hfine Rel hrefl hsym
  obtain ⟨E,hEcore,hcost,hOld,hscales⟩ := hcore schedule hcoarse hfine Rel hrefl hsym
  refine ⟨E,hEcore,hcost,hOld,?_⟩
  have hmenu : 0 < menuSize d g+g := by unfold menuSize; omega
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
  refine ⟨hjoint,hb.1,?_⟩
  intro p hp
  exact actual_all_parent_near_lower h original horiginal ha R E
    (menuSize d g) g L level hmenu hdy (relationMenu h R a schedule Rel)
    schedule hEcore j hnear hpair hpoint hformal hcoarseReal p hp

end NativeJointActualNearBalance
