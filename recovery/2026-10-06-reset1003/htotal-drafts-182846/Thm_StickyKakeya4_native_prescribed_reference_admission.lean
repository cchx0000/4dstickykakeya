/- UNVERIFIED source draft. No strict Lean check has run on this file. -/
import Theorems.Thm_StickyKakeya4_native_reference_parent_population
import Theorems.Thm_StickyKakeya4_native_reference_parent_admission_budget
import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission
import Theorems.Thm_StickyKakeya4_native_reference_admission_invariance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
noncomputable section
namespace NativePrescribedReferenceAdmission
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalParentSource NativeMiddleWindowBalance
open NativeReferenceParentPopulation NativeReferenceParentAdmissionBudget
open NativeNormalizedCellSourceUpper NativeActualRelativeCoarseAdmission
open NativeReferenceAdmissionInvariance

/-- Native accuracy and the original-label population accuracy can both
be prescribed before tau/seed, below the final effective pruning threshold. -/
theorem exists_accuracy (zMin window eB : ℝ)
    (hz : 0 < zMin) (hw : 0 < window) (heB : 0 < eB) :
    ∃etaNative profileExp : ℝ,
      0 < etaNative ∧ etaNative ≤ zMin ∧ etaNative ≤ window*eB/256 ∧
      0 < profileExp ∧ profileExp ≤ zMin ∧ profileExp ≤ window*eB/16 := by
  refine ⟨min zMin (window*eB/256),min zMin (window*eB/16),
    lt_min hz (by positivity),min_le_left _ _,min_le_right _ _,
    lt_min hz (by positivity),min_le_left _ _,min_le_right _ _⟩

/-- Re-admit the SAME E1 parent with a prescribed accuracy. The first
core's actual enlarged factor F, its original parent equality, and H1 are
used internally. This changes no source datum, reference family, shading,
or representative; it does not rely on the opaque accuracy returned by
the earlier angular engine. The seed and cutoff restrictions precede D. -/
theorem exists_prescribed_parent_admission (etaNative profileExp sigma0 : ℝ)
    (hetaNative : 0 < etaNative) (hprofile : 0 < profileExp) (hsigma0 : 0 < sigma0) :
    ∃delta0 : ℝ,0 < delta0 ∧ delta0 ≤ 1/8 ∧
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),
      0 ≤ zeta → eta ≤ seed/8 → zeta ≤ seed/256 →
      seed ≤ etaNative → seed ≤ profileExp → D.thickness ≤ delta0 →
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
      IsWangZakharovNativeFiniteInput (source h R E a m p) etaNative ∧
      (∀i,(source h R E a m p).line i∈fixedCompactClass) ∧
      (source h R E a m p).thickness ≤ sigma0 ∧
      (64:ℝ)^3*(source h R E a m p).thickness^profileExp ≤ D.thickness^zeta ∧
      OriginalPopulationLaw (source h R E a m p) univ 0 profileExp (level-m+6) ∧
      IsWangZakharovNativeFiniteInput (source h R E1 a m p) etaNative ∧
      OriginalPopulationLaw (source h R E1 a m p) univ 0 profileExp (level-m+6) := by
  obtain ⟨delta0,hd0,hd01,Hbudget⟩ :=
    exists_first_stage_admission_cutoff etaNative profileExp sigma0 hetaNative hprofile hsigma0
  refine ⟨delta0,hd0,hd01,?_⟩
  intro n D eta zeta seed a h hzeta heta hzseed hseedNative hseedProfile hsmall
    original R level HB E1 hE1 F Q m hm hsquare hret Hparent Hcost p hp E
  have hE : E⊆incidences original :=
    (filter_subset _ _).trans (hE1.trans (filter_subset _ _))
  have hlabels : ∀z∈E,z.1∈parentLabels D R a (2^m) p := by
    intro z hz
    obtain ⟨hzE,hzp⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨(mem_filter.mp (hE1 hzE)).2,hzp⟩
  have hParent : (parentLabels D R a (2^m) p).Nonempty :=
    ⟨hp.choose.1,hlabels hp.choose hp.choose_spec⟩
  have hpop := reference_parent_population h original R level HB (hsmall.trans hd01)
    E1 hE1 F Q m hm hret Hparent Hcost p hp
  have hDelta : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  obtain ⟨hSigma,had,hcw,hden,hprof⟩ := Hbudget D.thickness (64/((2^m:ℕ):ℝ))
    eta zeta seed h.1.2.1 hsmall hDelta hsquare heta hzseed hseedNative hseedProfile
  have hthick : (source h R E a m p).thickness=D.thickness/(64/((2^m:ℕ):ℝ)) := by
    rw [source_thickness]
    field_simp
  rw [←hthick] at hSigma had hcw hden hprof
  obtain ⟨hNative,hcompact⟩ := source_native_from_population h hzeta original R level HB
    m hm p E hE hlabels hParent (D.thickness^(seed/8+2*zeta))
    (Real.rpow_pos_of_pos h.1.2.1 _) hpop had hcw hden
  have hLaw := source_population_law h R E a zeta profileExp hzeta level HB.2.1
    HB.2.2.2.2.2.2.2.2 m hm p hNative hprof
  have hEq : source h R E a m p=source h R E1 a m p := source_parent_eq h R E1 a m p
  exact ⟨hNative,hcompact,hSigma,hprof,hLaw,hEq ▸ hNative,hEq ▸ hLaw⟩

end NativePrescribedReferenceAdmission
