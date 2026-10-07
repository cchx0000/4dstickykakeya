import Theorems.Thm_StickyKakeya4_native_normalized_cell_source_upper
import Theorems.Thm_StickyKakeya4_native_normalized_cell_angular_menu
import Theorems.Thm_StickyKakeya4_native_actual_relative_coarse_admission
import Theorems.Thm_StickyKakeya4_native_actual_local_admission
import Theorems.Thm_StickyKakeya4_native_joint_local_coarse_upper
import Theorems.Thm_StickyKakeya4_native_middle_window_balance

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8500000

noncomputable section
namespace NativeNormalizedCellSourceAngular
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeCubicalIncidenceCounts NativeLocalParentSource
open NativeMiddleWindowBalance NativeActualLocalAdmission NativeActualRelativeCoarseAdmission
open NativeNormalizedCellRelativeCore NativeRelativeCoarseReadback NativeJointUniformCoarseRelations
open NativeFixedCompactKakeyaExponent NativeJointLocalCoarseUpper
open NativeUnitParentNormalization
open scoped ENNReal

/-- Complete actual angular-union upper from the unchanged original source. The local loss and all cutoffs precede D; all source admission and geometry are derived. -/
theorem exists_source_angular_upper {epsilon window : ℝ}
    (hepsilon : 0 < epsilon) (hwindow : 0 < window) :
    ∃ e eta0 eps0 : ℝ,0<e ∧ 0<eta0 ∧ 0<eps0 ∧
      ∀ localEta : ℝ,0<localEta → localEta≤eta0 →
      ∀ (n : ℕ) (D : FiniteScaleSource n) (eta zeta a : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta),0≤zeta →
      ∀ (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ),
        HasOriginalBackbone D original R a level zeta →
      ∀ m : ℕ,m≤level → ∀ (p : Parent) (E : Finset (Fin n × Index)),
        E⊆incidences original → (∀z∈E,z.1∈parentLabels D R a (2^m) p) →
      ∀ hp : (parentLabels D R a (2^m) p).Nonempty,
      ∀ population : ℝ,0<population →
        population*(parentLabels D R a (2^m) p).card ≤ D.thickness*E.card →
        (2048:ℝ)^3*(source h R E a m p).thickness^localEta ≤ D.thickness^zeta →
        (373248*512^4:ℝ)*(source h R E a m p).thickness^localEta ≤ D.thickness^(eta+zeta) →
        (1024*175616*NativeOriginalPrunedMass.volumeConstant)*
          (source h R E a m p).thickness^localEta ≤ population →
        (source h R E a m p).thickness ≤ eps0 →
        (64:ℝ)^3*(source h R E a m p).thickness^(window*e/32) ≤ D.thickness^zeta →
      ∀ ell : ℕ,ell≤level-m+6 →
        1/((2^ell:ℕ):ℝ) ≤ (source h R E a m p).thickness^window →
        (source h R E a m p).thickness/(1/((2^ell:ℕ):ℝ)) ≤ (source h R E a m p).thickness^window →
      ∀ Q : ℕ,HasUniformFibers E Q (doublePair h R a m p hp (2^ell)) →
        HasUniformFibers E Q (fun z => (doublePair h R a m p hp (2^ell) z).2) →
      ∀ q : Index,
        ((NativeNormalizedCellAngularMenu.angularMenu D a m (2^ell) p E q).card:ℝ) ≤
          81*(Q:ℝ)^4*(source h R E a m p).thickness^(-(7*(window*e/32)))*
            (64/((2^ell:ℕ):ℝ))^(-extremalExponent-epsilon) := by
  obtain ⟨e,eta0,eps0,he,heta0,heps0,hUpper⟩ :=
    NativeNormalizedCellSourceUpper.exists_source_normalized_degree_upper hepsilon hwindow
  refine ⟨e,eta0,eps0,he,heta0,heps0,?_⟩
  intro localEta hlocalEta heta n D eta zeta a h hzeta original R level Hbackbone m hm p E hE hlabels hp
    population hpopulation hpop had hcw hden hsmall hbudget ell hell hcoarse hfine Q hPair hPoint q
  exact (Nat.cast_le.mpr (NativeNormalizedCellAngularMenu.angular_menu_le_degree D a m (2^ell) p E q)).trans
    (hUpper localEta hlocalEta heta n D eta zeta a h hzeta original R level Hbackbone m hm p E hE hlabels hp
      population hpopulation hpop had hcw hden hsmall hbudget ell hell hcoarse hfine Q hPair hPoint q)

end NativeNormalizedCellSourceAngular
