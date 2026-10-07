import Theorems.Thm_StickyKakeya4_native_fixed_menu_slice_ad
import Theorems.Thm_StickyKakeya4_native_slice_ad_constant
import Theorems.Thm_StickyKakeya4_native_realized_slice_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeReferenceSliceAD
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeSliceCountComparison NativeColumnPopulationBounds
open NativeReferenceColumnExponents NativeReferenceSliceClassBounds NativeAnisotropicSliceLabels
open NativeSquaredGrainQueries NativeReferenceSliceAllRadii NativeFixedHorizontalMenu SelfUniform
open NativeSliceClassBalls NativeSliceRadiusInterpolation NativeFixedMenuSliceAD NativeRealizedSliceGeometry

/-- The actual reference slice in the existing real-dimensional AD API.
Its one explicit constant pays the asymmetric source bounds and finite menu;
the source geometry also supplies separation, a box bound, and diameter. -/
theorem fixed_menu_reference_slice_AD {n J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (HB : HasOriginalBackbone D original R a level zeta)
    (m : ℕ) (hm6 : 6 ≤ m) (hbL : phaseDepth m ≤ level) (hJ : 0 < J)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population : ℝ) (hpopulation : 0 < population)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hprofile : ∀j,HasColumnPowerProfile D a m (depths J m j) E p profileLower profileUpper)
    (Q : ℕ)
    (Hcaller : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (sliceRelations D a m (depths J m) j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (sliceRelations D a m (depths J m) j) E y)
    (height : ℤ) (hheight : height∈(points D a m (phaseDepth m) E p).image (fun u => u (3:Fin 4))) :
    let L := lowerCountCoefficient D.thickness zeta population profileUpper
    let U := upperCountCoefficient D.thickness zeta profileLower
    let B : ℝ := max 8 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let C := NativeSliceADConstant.constant (L/((Q:ℝ)^4*U)) (((Q:ℝ)^4*U)/L) B (3-extremalExponent)
    let P := realizedSlice (points D a m (phaseDepth m) E p) (horizontalMesh m) height
    1 ≤ C ∧ P.Nonempty ∧ FiniteVoronoiPopulation.Separated P (horizontalMesh m) ∧
      (∀x∈P,∀v : Fin 3,|x v| ≤ 3/16) ∧ (∀x∈P,∀y∈P,dist x y ≤ 3/8) ∧
      FiniteVoronoiRealADCoarsening.ADBounds P (horizontalMesh m) C (3-extremalExponent) := by
  dsimp only
  have HU := caller_column_uniformities D a m (depths J m)
    (fun j => (depths_bounds J m hm6 j).2) E Q Hcaller p
  have hQ := NativePaidParentScaleBudget.uniform_radix_pos _ hp _ Q HU.1
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hd : 0 < D.thickness := by rw [HB.2.1]; positivity
  obtain ⟨hcoefL,hcoefU⟩ := count_coefficients_pos (zeta:=zeta) hd hpopulation hL hU
  have Hgeometry := realized_slice_geometry h original R level HB m hm6 hbL E hE p height
  refine ⟨NativeSliceADConstant.one_le_constant _ _ _ _,?_,
    realized_slice_separated _ _ (horizontalMesh_pos m) height,Hgeometry.1,Hgeometry.2,?_⟩
  · obtain ⟨u,hu,huh⟩ := mem_image.mp hheight
    exact ⟨realized (horizontalMesh m) u,
      mem_image.mpr ⟨u,mem_filter.mpr ⟨hu,huh⟩,rfl⟩⟩
  · apply NativeSliceADConstant.ADBounds_of_asymmetric_counts _ _ _ _ _ _
      (horizontalMesh_pos m) (by positivity)
    intro x hx r hr hr1
    simp only [realizedSlice,mem_image,heightSlice,mem_filter] at hx
    obtain ⟨u,⟨hu,huh⟩,rfl⟩ := hx
    have hh := fixed_menu_reference_all_radius_bounds h original R level HB m hm6 hbL hJ
      E hE p hp population hpopulation hret profileLower profileUpper hL hU Hprofile Q Hcaller u hu r hr hr1
    dsimp only at hh
    rw [huh] at hh
    exact hh

end NativeReferenceSliceAD
