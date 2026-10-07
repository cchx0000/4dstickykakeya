/- Fresh source-facing representative direction readback. -/
import Theorems.Thm_StickyKakeya4_native_full_reference_slope_cap
import Theorems.Thm_StickyKakeya4_native_incident_affine_anchor_geometry
import Theorems.Thm_StickyKakeya4_native_local_parent_source

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section
namespace NativeFullReferenceDirectionDrift
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalCellChartGeometry NativeCoarseDirectionThinning NativeCoarseCellSource
open NativeFullCoarseShadow NativeFullReferenceSlopeCap NativeCoarseRepresentativeGeometry
open NativeIncidentAffineAnchorGeometry NativeLocalParentSource NativeLocalParentGeometry
open NativeHorizontalGrainSlice NativeHorizontalGraphCoordinates
open scoped BigOperators

/-- The literal horizontal graph slope, with height zero. -/
def horizontalSlope (l : MarkedLine) : E4 :=
  ActualSlopeSource.heightPoint (WithLp.toLp 2 (slope l)) 0

/-- Actual equal phase parents control the full horizontal slope vector.
This finite geometry does not require any native hypothesis on D. -/
theorem same_parent_horizontal_distance {n : ℕ} (D : FiniteScaleSource n)
    (a : ℝ) (N : ℕ) (hN : 0 < N) (i j : Fin n)
    (hp : parentLabel D a N i = parentLabel D a N j) :
    dist (horizontalSlope (D.line i)) (horizontalSlope (D.line j)) ≤ 3 / (N : ℝ) := by
  have hc (v : Fin 3) : |slope (D.line i) v - slope (D.line j) v| ≤ 1 / (N : ℝ) :=
    NativeNormalizedParentCarrierMetric.same_floor_mul_close _ _ N hN
      (congrFun (congrArg Prod.fst hp) v)
  rw [dist_eq_norm]
  let v := horizontalSlope (D.line i) - horizontalSlope (D.line j)
  have hs (k : Fin 3) : (slope (D.line i) k - slope (D.line j) k)^2 ≤ (1/(N:ℝ))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc k) 2
  have hsq : ‖v‖^2 ≤ 3*(1/(N:ℝ))^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
    simp only [v, horizontalSlope, PiLp.sub_apply, ActualSlopeSource.heightPoint_last,
      ActualSlopeSource.heightPoint_castSucc,
      sub_self, zero_pow (by decide : 2 ≠ 0), add_zero, Fin.sum_univ_three]
    linarith only [hs 0, hs 1, hs 2]
  have hpos : 0 ≤ 1/(N:ℝ) := by positivity
  have hn := norm_nonneg v
  change ‖v‖ ≤ 3/(N:ℝ)
  rw [show (3:ℝ)/(N:ℝ)=3*(1/(N:ℝ)) by ring]
  nlinarith only [hsq, hpos, hn, sq_nonneg (1/(N:ℝ))]

/-- Zero-parent spatial contraction leaves the actual representative's
unit direction unchanged. The full coarse source is not assumed native. -/
theorem full_direction_readback {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index))
    (j : Fin (R.image (parentLabel D a (2^b))).card) :
    direction ((fullSource h R a level b E).line j) =
      direction (D.line (representative h R a (2^b)
        (parentIndex (R.image (parentLabel D a (2^b))) j))) :=
  full_direction h R a level b E j

/-- The same absence of a contraction factor holds for the literal
horizontal graph slope used by the old affine-residual theorem. -/
theorem full_horizontal_readback {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index))
    (j : Fin (R.image (parentLabel D a (2^b))).card) :
    horizontalSlope ((fullSource h R a level b E).line j) =
      horizontalSlope (D.line (representative h R a (2^b)
        (parentIndex (R.image (parentLabel D a (2^b))) j))) := by
  ext v
  refine Fin.lastCases ?_ (fun k => ?_) v
  · simp only [horizontalSlope, ActualSlopeSource.heightPoint_last]
  · simpa only [horizontalSlope, ActualSlopeSource.heightPoint_castSucc, PiLp.toLp_apply]
      using full_slope h R a level b E j k

/-- The actual representative readback supplies the full drift bound.
Only the genuine equality of its phase label with the old tube is needed. -/
theorem full_horizontal_distance {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a : ℝ) (level b : ℕ) (E : Finset (Fin n × Index))
    (j : Fin (R.image (parentLabel D a (2^b))).card) (i : Fin n)
    (hi : parentLabel D a (2^b) i = parentIndex (R.image (parentLabel D a (2^b))) j) :
    dist (horizontalSlope ((fullSource h R a level b E).line j))
      (horizontalSlope (D.line i)) ≤ 3 / ((2^b : ℕ) : ℝ) := by
  rw [full_horizontal_readback]
  apply same_parent_horizontal_distance D a (2^b) (by positivity)
  exact ((representative_spec h R a (2^b)
    (parentIndex_mem (R.image (parentLabel D a (2^b))) j)).2).trans hi.symm

/-- The first admitted reference's graph slope is exactly the original
normalized localHorizontalSlope, before and after the second contraction. -/
theorem local_horizontal_readback {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (Eref : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (i : Fin (parentLabels D R a (2^m) p).card) :
    horizontalSlope ((source h R Eref a m p).line i) =
      localHorizontalSlope D (2^m) p
        (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i) := by
  ext v
  refine Fin.lastCases ?_ (fun k => ?_) v
  · simp only [horizontalSlope, localHorizontalSlope, ActualSlopeSource.heightPoint_last]
  · simp only [horizontalSlope, localHorizontalSlope, ActualSlopeSource.heightPoint_castSucc,
      NativeLocalParentSource.source_line, NativeLocalParentGeometry.slope_line]

/-- The same E1-reference source and its actual full coarse family feed
the original normalized-direction residual without a changed source. -/
theorem same_reference_horizontal_distance {n : ℕ} {D : FiniteScaleSource n}
    {eta localEta : ℝ} (h : IsWangZakharovNativeFiniteInput D eta)
    (R : Finset (Fin n)) (Eref : Finset (Fin n × Index)) (a : ℝ) (m : ℕ) (p : Parent)
    (hReferenceNative : IsWangZakharovNativeFiniteInput (source h R Eref a m p) localEta)
    (level b : ℕ)
    (selected : Finset (Fin (parentLabels D R a (2^m) p).card × Index))
    (i : Fin (parentLabels D R a (2^m) p).card)
    (j : Fin (((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
      (parentLabel (source h R Eref a m p) 0 (2^b))).card))
    (hi : parentLabel (source h R Eref a m p) 0 (2^b) i =
      parentIndex ((univ : Finset (Fin (parentLabels D R a (2^m) p).card)).image
        (parentLabel (source h R Eref a m p) 0 (2^b))) j) :
    dist (horizontalSlope ((fullSource hReferenceNative univ 0 level b selected).line j))
      (localHorizontalSlope D (2^m) p
        (NativePaddedCellSource.originalLabel (parentLabels D R a (2^m) p) i)) ≤
      3 / ((2^b : ℕ) : ℝ) := by
  have hh := full_horizontal_distance hReferenceNative univ 0 level b selected j i hi
  rwa [local_horizontal_readback] at hh

end NativeFullReferenceDirectionDrift
