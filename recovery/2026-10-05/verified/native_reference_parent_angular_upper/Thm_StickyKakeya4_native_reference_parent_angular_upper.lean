import Theorems.Thm_StickyKakeya4_native_reference_parent_population
import Theorems.Thm_StickyKakeya4_native_reference_parent_admission_budget
import Theorems.Thm_StickyKakeya4_native_bounded_reference_relative_upper

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeReferenceParentAngularUpper
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalParentSource NativeMiddleWindowBalance
open NativeCubicalIncidenceCounts NativeReferenceParentPopulation NativeReferenceParentAdmissionBudget
open NativeBoundedReferenceRelativeUpper NativeNormalizedCellSourceUpper NativeUnitParentNormalization
open NativeRelativeCoarseReadback NativeJointUniformCoarseRelations NativeNormalizedCellAngularMenu
open NativeFixedCompactKakeyaExponent

/-- The quantifier order is rank cutoff first, then epsilon/window/budget
and this engine, then tau/seed, then the SINGLE original source and enlarged
E1 core. Actual first-stage retention supplies native admission on E1p.
All later E2p/S angular unions inherit its upper by inclusion. -/
theorem exists_reference_parent_angular_upper (epsilon window budget : ℝ)
    (hepsilon : 0 < epsilon) (hwindow : 0 < window) (hbudget : 0 < budget) :
    ∃e localEta seedCap delta0 : ℝ,
      0 < e ∧ e ≤ 32*budget/(7*window) ∧ 0 < localEta ∧ 0 < seedCap ∧ 0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
        0 ≤ zeta → eta ≤ seed/8 → zeta ≤ seed/256 → seed ≤ seedCap → D.thickness ≤ delta0 →
      ∀(original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ),
        HasOriginalBackbone D original R a level zeta →
      ∀E1 : Finset (Fin n × Index),E1⊆retained original R →
      ∀F Q m : ℕ,m ≤ level → D.thickness ≤ (64/((2^m:ℕ):ℝ))^2 →
        (incidences original).card ≤ F*E1.card →
        (∀x y,x∈E1 → y∈E1 →
          (parentEdges D a (2^m) E1 (parentLabel D a (2^m) x.1)).card ≤
            Q^2*(parentEdges D a (2^m) E1 (parentLabel D a (2^m) y.1)).card) →
        (125*175616*16384:ℝ)*(F:ℝ)*(Q:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-(seed/8)) →
      ∀p : Parent,(parentEdges D a (2^m) E1 p).Nonempty →
        let E := parentEdges D a (2^m) E1 p
        IsWangZakharovNativeFiniteInput (source h R E a m p) localEta ∧
        (∀i,(source h R E a m p).line i∈fixedCompactClass) ∧
        ∀hp : (parentLabels D R a (2^m) p).Nonempty,
        ∀s : ℕ,s ≤ level-m+6 →
          1/((2^s:ℕ):ℝ) ≤ (source h R E a m p).thickness^window →
          (source h R E a m p).thickness/(1/((2^s:ℕ):ℝ)) ≤ (source h R E a m p).thickness^window →
          HasUniformFibers E Q (doublePair h R a m p hp (2^s)) →
          HasUniformFibers E Q (fun z => (doublePair h R a m p hp (2^s) z).2) →
        ∀T⊆E,∀q : Index,((angularMenu D a m (2^s) p T q).card:ℝ) ≤
          81*(Q:ℝ)^4*(source h R E a m p).thickness^(-budget)*
            (64/((2^s:ℕ):ℝ))^(-extremalExponent-epsilon) := by
  obtain ⟨e,localEta,sigma0,he,heBound,hLocal,hSigma0,Hupper⟩ :=
    exists_bounded_reference_engine epsilon window budget hepsilon hwindow hbudget
  have hProfile : 0 < window*e/32 := by positivity
  obtain ⟨delta0,hd0,hd01,Hbudget⟩ := exists_first_stage_admission_cutoff localEta (window*e/32)
    sigma0 hLocal hProfile hSigma0
  let seedCap := min localEta (window*e/32)
  refine ⟨e,localEta,seedCap,delta0,he,heBound,hLocal,lt_min hLocal hProfile,hd0,hd01,?_⟩
  intro n D eta zeta seed a h hzeta heta hzseed hseed hsmall original R level HB E1 hE1
    F Q m hm hsquare hret Hparent Hcost p hp
  let E := parentEdges D a (2^m) E1 p
  have hE : E⊆incidences original := (filter_subset _ _).trans (hE1.trans (filter_subset _ _))
  have hlabels : ∀z∈E,z.1∈parentLabels D R a (2^m) p := by
    intro z hz
    obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨(mem_filter.mp (hE1 hzE)).2,hzp⟩
  have hParent : (parentLabels D R a (2^m) p).Nonempty := ⟨hp.choose.1,hlabels hp.choose hp.choose_spec⟩
  have hpop := reference_parent_population h original R level HB (hsmall.trans hd01) E1 hE1 F Q m hm
    hret Hparent Hcost p hp
  have hDelta : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  obtain ⟨hSigma,had,hcw,hden,hprof⟩ := Hbudget D.thickness (64/((2^m:ℕ):ℝ)) eta zeta seed
    h.1.2.1 hsmall hDelta hsquare heta hzseed (hseed.trans (min_le_left _ _)) (hseed.trans (min_le_right _ _))
  have hthick : (source h R E a m p).thickness=D.thickness/(64/((2^m:ℕ):ℝ)) := by
    rw [source_thickness]
    field_simp
  rw [←hthick] at hSigma had hcw hden hprof
  have hpopulation : 0 < D.thickness^(seed/8+2*zeta) := Real.rpow_pos_of_pos h.1.2.1 _
  obtain ⟨hS,hSK⟩ := source_native_from_population h hzeta original R level HB m hm p E hE hlabels hParent
    (D.thickness^(seed/8+2*zeta)) hpopulation hpop had hcw hden
  refine ⟨hS,hSK,?_⟩
  intro hpR s hs hcoarse hfine hPair hPoint T hTE q
  exact Hupper n D eta zeta a h hzeta original R level HB m hm p E hE hlabels hpR
    localEta hS hSK le_rfl hSigma hprof s hs hcoarse hfine Q hPair hPoint T hTE q

end NativeReferenceParentAngularUpper
