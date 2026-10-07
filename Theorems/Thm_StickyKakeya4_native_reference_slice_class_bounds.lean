import Theorems.Thm_StickyKakeya4_native_reference_column_exponents
import Theorems.Thm_StickyKakeya4_native_slice_class_algebra

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeReferenceSliceClassBounds
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeAnisotropicGlobalSourceBridge NativeAnisotropicPairNumerator
open NativeSliceCountComparison NativeColumnPopulationBounds NativeReferenceColumnExponents
open NativeAnisotropicSliceLabels NativeSliceClassAlgebra NativeIncidenceMultiplicityTower

/-- The actual anisotropic pair multiplicity, whose bounds are supplied
by the paid original-source transfer and the queried short-row bridge. -/
def HasColumnPowerProfile {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m f : ℕ)
    (E : Finset (Fin n × Index)) (p : Parent) (lower upper : ℝ) : Prop :=
  lower*(relativeWidth m f)^(-extremalExponent) ≤
      multiplicity ((parentEdges D a (2^m) E p).image (columnPair D a m f p)) ∧
    multiplicity ((parentEdges D a (2^m) E p).image (columnPair D a m f p)) ≤
      upper*(relativeWidth m f)^(-extremalExponent)

lemma relativeWidth_ratio (m fine coarse : ℕ) (hcf : coarse ≤ fine) :
    relativeWidth m coarse=((2^(fine-coarse):ℕ):ℝ)*relativeWidth m fine := by
  unfold relativeWidth
  rw [NativeAnisotropicColumnCapacity.dyadic_height_eq coarse fine hcf]
  ring

/-- The genuine source numerator and multiplicity profiles give both the
global count ratio and every occupied local class exponent. Only the latter
spends Q^4. All labels use the same original parent chart and fixed height. -/
theorem reference_class_power_bounds {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m fine coarse : ℕ) (hm6 : 6 ≤ m) (hmc : m ≤ coarse) (hcf : coarse ≤ fine)
    (hfL : fine ≤ level)
    (hfwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^fine:ℕ):ℝ))
    (hcwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^coarse:ℕ):ℝ))
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population : ℝ) (hpopulation : 0 < population)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hfine : HasColumnPowerProfile D a m fine E p profileLower profileUpper)
    (Hcoarse : HasColumnPowerProfile D a m coarse E p profileLower profileUpper)
    (Q : ℕ)
    (HF : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^fine:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2))
    (HC : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^coarse:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2)) :
    let L := lowerCountCoefficient D.thickness zeta population profileUpper
    let U := upperCountCoefficient D.thickness zeta profileLower
    let T : ℝ := ((2^(fine-coarse):ℕ):ℝ)
    ((L/U)*T^(3-extremalExponent)*(points D a m coarse E p).card ≤
        (points D a m fine E p).card ∧
      ((points D a m fine E p).card:ℝ) ≤
        (U/L)*T^(3-extremalExponent)*(points D a m coarse E p).card) ∧
    ∀x∈points D a m fine E p,
      (L/((Q:ℝ)^4*U))*T^(3-extremalExponent) ≤
        ((points D a m fine E p).filter
          (fun z => horizontalCoarsen fine coarse z=horizontalCoarsen fine coarse x)).card ∧
      (((points D a m fine E p).filter
          (fun z => horizontalCoarsen fine coarse z=horizontalCoarsen fine coarse x)).card:ℝ) ≤
        (((Q:ℝ)^4*U)/L)*T^(3-extremalExponent) := by
  dsimp only
  have hd : 0 < D.thickness := by rw [Hbackbone.2.1]; positivity
  have hcoef := count_coefficients_pos (zeta:=zeta) hd hpopulation hL hU
  have hPfine := reference_column_point_power_bounds h original R level Hbackbone m fine
    hm6 (hmc.trans hcf) hfL hfwindow E hE p hp population hpopulation hret
    profileLower profileUpper hL hU Hfine
  have hPcoarse := reference_column_point_power_bounds h original R level Hbackbone m coarse
    hm6 hmc (hcf.trans hfL) hcwindow E hE p hp population hpopulation hret
    profileLower profileUpper hL hU Hcoarse
  have hheight : (0:ℝ)<64/((2^m:ℕ):ℝ) := by positivity
  have hratio : (0:ℝ)<((2^(fine-coarse):ℕ):ℝ) := by positivity
  constructor
  · exact global_count_ratio_bounds hheight (relativeWidth_pos m fine) hratio
      (relativeWidth_ratio m fine coarse hcf) hcoef.1 hcoef.2 hPfine hPcoarse
  · intro x hx
    have hQ := NativePaidParentScaleBudget.uniform_radix_pos _ hp _ Q HF
    have hclasses := column_class_counts_comparable D a m fine coarse hcf E p Q HF HC
    have hPc : lowerCountCoefficient D.thickness zeta population profileUpper*
        (relativeWidth m coarse)^(extremalExponent-3) ≤
          (64/((2^m:ℕ):ℝ))*((points D a m fine E p).image (horizontalCoarsen fine coarse)).card ∧
        (64/((2^m:ℕ):ℝ))*((points D a m fine E p).image (horizontalCoarsen fine coarse)).card ≤
          upperCountCoefficient D.thickness zeta profileLower*(relativeWidth m coarse)^(extremalExponent-3) := by
      rw [points_coarsen D a m fine coarse hcf E p]
      exact hPcoarse
    have hh := class_bounds_from_global_counts (points D a m fine E p)
      (horizontalCoarsen fine coarse) (Q^4) (by positivity) hclasses
      (64/((2^m:ℕ):ℝ)) (relativeWidth m fine) (relativeWidth m coarse)
      (((2^(fine-coarse):ℕ):ℝ)) extremalExponent
      (lowerCountCoefficient D.thickness zeta population profileUpper)
      (upperCountCoefficient D.thickness zeta profileLower)
      hheight (relativeWidth_pos m fine) hratio (relativeWidth_ratio m fine coarse hcf)
      hcoef.1 hcoef.2 hPfine hPc x hx
    simpa only [Nat.cast_pow] using hh

end NativeReferenceSliceClassBounds
