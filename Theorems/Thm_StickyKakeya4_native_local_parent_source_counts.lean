import Theorems.Thm_StickyKakeya4_native_local_parent_source
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeLocalParentSourceCounts
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeLocalParentSource
open scoped BigOperators

lemma card_filter_originalLabel {n : ℕ} (Q : Finset (Fin n))
    (P : Fin n → Prop) [DecidablePred P] :
    ((univ : Finset (Fin Q.card)).filter
      (fun i => P (NativePaddedCellSource.originalLabel Q i))).card = (Q.filter P).card := by
  simpa only [Finset.card_filter] using sum_originalLabel (M:=ℕ) Q (fun i => if P i then 1 else 0)

/-- Exact actual-carrier ball counts, expressed on the full original Q. -/
lemma source_carrierBallCount {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a (2^m) p).card) (r : ℝ) :
    wzCarrierBallCount (source h R E a m p) i r =
      ((parentLabels D R a (2^m) p).filter (fun j => dist
        (direction (NativeLocalParentGeometry.line D a (2^m) p j),
          offset (NativeLocalParentGeometry.line D a (2^m) p j))
        (direction (NativeLocalParentGeometry.line D a (2^m) p
          (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i)),
          offset (NativeLocalParentGeometry.line D a (2^m) p
          (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i))) ≤ r)).card := by
  exact card_filter_originalLabel (parentLabels D R a (2^m) p) (fun j => dist
    (direction (NativeLocalParentGeometry.line D a (2^m) p j),
      offset (NativeLocalParentGeometry.line D a (2^m) p j))
    (direction (NativeLocalParentGeometry.line D a (2^m) p
      (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i)),
      offset (NativeLocalParentGeometry.line D a (2^m) p
      (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i))) ≤ r)

/-- Exact actual contained-tube counts, expressed on the full original Q. -/
lemma source_containedTubeCount {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (E : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent) (U : Set E4) :
    wzContainedTubeCount (source h R E a m p) U =
      ((parentLabels D R a (2^m) p).filter (fun j =>
        markedUnitTube (NativeLocalParentGeometry.line D a (2^m) p j)
          (((2^m:ℕ):ℝ)*D.thickness/64) ⊆ U)).card := by
  exact card_filter_originalLabel (parentLabels D R a (2^m) p) (fun j =>
    markedUnitTube (NativeLocalParentGeometry.line D a (2^m) p j)
      (((2^m:ℕ):ℝ)*D.thickness/64) ⊆ U)

end NativeLocalParentSourceCounts
