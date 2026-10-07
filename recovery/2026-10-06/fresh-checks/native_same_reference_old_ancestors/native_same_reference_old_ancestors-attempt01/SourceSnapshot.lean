import Theorems.Thm_StickyKakeya4_native_same_reference_chart_bounds
import Theorems.Thm_StickyKakeya4_native_capped_old_ancestors

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeSameReferenceOldAncestors
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentSource NativeMiddleWindowBalance NativeFullCoarseShadow
open NativeUnitParentNormalization NativeCappedOldAncestors NativeSameReferenceChartBounds
open NativeOriginalCellChartGeometry

/-- The same original HB and existing admitted E1-parent source supply a
capped old ancestor for the actual final full family. No occupied chart-cell
lower law, ball-to-cell conversion, or replacement R is an input. -/
theorem from_original_backbone {n : ℕ} {D : FiniteScaleSource n}
    {eta localEta a zeta e sigma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta)
    (original : Fin n → Finset Index) (R : Finset (Fin n)) (level : ℕ)
    (HB : HasOriginalBackbone D original R a level zeta)
    (Eref : Finset (Fin n × Index)) (m b : ℕ) (hmb : m+b ≤ level) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h R Eref a m p) localEta)
    (hbudget : (64:ℝ)^3*(source h R Eref a m p).thickness^e ≤ D.thickness^zeta)
    (selected : Finset (Fin (parentLabels D R a (2^m) p).card × Index))
    (O : E4 ≃ₗᵢ[ℝ] E4) (hO : ∀ x : E4, O x (3:Fin 4)=x (3:Fin 4))
    (c : E4) (hc : ‖c‖ ≤ 1/2) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    let S := source h R Eref a m p
    let Q := (univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image (parentLabel S 0 (2^b))
    let C := MarkedIsometricFiniteTransport.source
      (fullSource hReferenceNative univ 0 (level-m+6) b selected) O c
    ∃ k ≤ b, let L := S.thickness^(2*e)*(((2^b:ℕ):ℝ)/((2^k:ℕ):ℝ))^3
      (∀ i : Fin Q.card, L ≤
        (((univ : Finset (Fin Q.card)).filter
            (fun j => oldAncestor S univ 0 b k j=oldAncestor S univ 0 b k i)).card:ℝ)) ∧
      sigma^3 ≤ (21^3*S.thickness^(-(2*e)))*L*C.thickness^3 ∧
      ∀ i j, oldAncestor S univ 0 b k i=oldAncestor S univ 0 b k j →
        (∀ v : Fin 3, |slope (C.line i) v-slope (C.line j) v| ≤ sigma) ∧
          ∀ v : Fin 3, |intercept (C.line i) v-intercept (C.line j) v| ≤ sigma := by
  intro S Q C
  have H := population_through h original R level HB Eref m b hmb p hbudget
  have hcommon := NativeActualRelativeCoarseAdmission.source_common_height_zero
    h R Eref a m p hReferenceNative
  have hcompact (i : Fin (parentLabels D R a (2^m) p).card) : S.line i∈fixedCompactClass := by
    have hi := (mem_parentLabels D R a (2^m) p _).mp
      (NativePaddedCellSource.originalLabel_mem (parentLabels D R a (2^m) p) i)
    exact NativeLocalParentGeometry.mem_fixedCompactClass D a (2^m) p _ hi.2
  exact exists_full_source_ancestors hReferenceNative hcompact hcommon univ (level-m+6) b selected
    H O hO c hc hsigma hsigma1

end NativeSameReferenceOldAncestors
