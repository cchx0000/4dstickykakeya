/- RECONSTRUCTED 2026-10-06 from visible conversation context. UNVERIFIED.
Includes the Oct 5 21:23--21:24 explicit slope, one-step Fin sum, and rational-sum fixes.
Those fixes had not been rechecked after attempt 01 failed. -/
import Theorems.Thm_StickyKakeya4_native_relative_coarse_readback
import Theorems.Thm_StickyKakeya4_native_slab_parent_normalization

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
noncomputable section
namespace NativeCurrentSourceDirections
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeLocalParentSource NativeLocalParentGeometry
open NativeRelativeParentLabels NativeDirectionRankDichotomy NativeReferenceXYGridLinear
open NativeGrainHeightProjectionTransport NativeSlabParentNormalization
open scoped BigOperators

/-- The graph vector of the current local source is the exact original
parent direction map, with no spatial contraction factor in the slope. -/
lemma local_source_slopeVector {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (T : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a (2^m) p).card) :
    slopeVector (source h R T a m p) i=parentDirection (2^m) p
      (slopeVector D (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i)) := by
  rw [parentDirection_slopeVector]
  ext v
  refine Fin.lastCases ?_ (fun j => ?_) v
  · simp only [slopeVector,ActualSlopeSource.heightPoint_last,northSlopeLift_last]
  · simp only [slopeVector,ActualSlopeSource.heightPoint_castSucc,
      northSlopeLift_castSucc,source_line,slope_line]

/-- Coarse padding changes intercepts and points but keeps its actual
representative's graph vector exactly. -/
lemma coarse_source_slopeVector {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a : ℝ) (level b : ℕ)
    (Q : Finset Parent) (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hsep : ∀p∈Q,∀q∈Q,p≠q → 64/((2^b:ℕ):ℝ) ≤
      dist (direction (D.line (rep p))) (direction (D.line (rep q))))
    (i : Fin Q.card) :
    slopeVector (NativeCoarseCellSource.source h a level b Q rep E hsep) i=
      slopeVector D (rep (NativeCoarseCellSource.parentIndex Q i)) := by
  unfold slopeVector
  congr 1
  ext j
  simp only [NativeOriginalCellChartGeometry.slope,NativeCoarseCellSource.source_line,
    NativeCoarseRepresentativeGeometry.direction_zero_parent h]

/-- Selecting the actual full-backbone representative in the same relative
phase cell moves graph directions by at most 3/M. -/
lemma relative_graph_distance {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N M : ℕ) (hM : 0 < M) (p : Parent) (i j : Fin n)
    (hr : relativeLabel D a N p M j=relativeLabel D a N p M i) :
    dist (parentDirection N p (slopeVector D j))
      (parentDirection N p (slopeVector D i)) ≤ 3/(M:ℝ) := by
  have hc (v : Fin 3) : |localSlope D N p j v-localSlope D N p i v| ≤ 1/(M:ℝ) := by
    have hh := NativeNormalizedParentCarrierMetric.same_floor_mul_close
      (slope (NativeLocalParentGeometry.line D a N p j) v)
      (slope (NativeLocalParentGeometry.line D a N p i) v) M hM
      (congrFun (congrArg Prod.fst hr) v)
    simpa only [slope_line] using hh
  rw [dist_eq_norm,parentDirection_slopeVector,parentDirection_slopeVector]
  apply (euclidean_norm_le_sum _).trans
  rw [Fin.sum_univ_castSucc]
  simp only [PiLp.sub_apply,northSlopeLift_last,
    sub_self,abs_zero,add_zero,northSlopeLift_castSucc]
  rw [Fin.sum_univ_three]
  calc
    _ ≤ 1/(M:ℝ)+1/(M:ℝ)+1/(M:ℝ) := add_le_add (add_le_add (hc 0) (hc 1)) (hc 2)
    _ = _ := by ring

/-- Existing near-plane information on a current original edge transports
to its actual relative representative with the explicit 3/M angular error. -/
lemma representative_infDist {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (N M : ℕ) (hM : 0 < M) (p : Parent) (i j : Fin n)
    (hr : relativeLabel D a N p M j=relativeLabel D a N p M i)
    (P : Submodule ℝ E4) (e : ℝ)
    (hi : Metric.infDist (parentDirection N p (slopeVector D i)) (P:Set E4)≤e) :
    Metric.infDist (parentDirection N p (slopeVector D j)) (P:Set E4)≤e+3/(M:ℝ) := by
  have hh := Metric.infDist_le_infDist_add_dist
    (x:=parentDirection N p (slopeVector D j))
    (y:=parentDirection N p (slopeVector D i)) (s:=(P:Set E4))
  have hd := relative_graph_distance D a N M hM p i j hr
  linarith

end NativeCurrentSourceDirections
