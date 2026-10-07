import Theorems.Thm_StickyKakeya4_native_reference_slice_all_radii
import Theorems.Thm_StickyKakeya4_native_fixed_horizontal_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeFixedMenuSliceAD
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeSliceCountComparison NativeColumnPopulationBounds
open NativeReferenceColumnExponents NativeReferenceSliceClassBounds NativeAnisotropicSliceLabels
open NativeSquaredGrainQueries NativeReferenceSliceAllRadii NativeFixedHorizontalMenu SelfUniform
open NativeSliceClassBalls NativeSliceRadiusInterpolation

/-- The interpolation cost of the literal fixed-size horizontal menu. -/
lemma menu_gap_cost {delta : ℝ} (J m level : ℕ) (hJ : 0 < J)
    (hbL : phaseDepth m ≤ level) (hdy : delta=(2:ℝ)⁻¹^level) :
    max 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ)) ≤ 8*delta^(-(1/(J:ℝ))) := by
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  have hspan : phaseDepth m-m ≤ level := (Nat.sub_le _ _).trans hbL
  have hfloor : (((phaseDepth m-m)/J:ℕ):ℝ) ≤ ((phaseDepth m-m:ℕ):ℝ)/(J:ℝ) := Nat.cast_div_le
  have hgap : ((((phaseDepth m-m)/J+1)-0:ℕ):ℝ) ≤ (level:ℝ)/J+1 := by
    simp only [Nat.sub_zero,Nat.cast_add,Nat.cast_one]
    linarith only [hfloor.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hspan) hJr.le)]
  have hp := NativeFixedSizeScaleMenu.dyadic_gap_power level ((phaseDepth m-m)/J+1) 0 J hJ hdy hgap
  simp only [Nat.sub_zero] at hp
  have hd : 0 < delta := by rw [hdy]; positivity
  have hd1 : delta ≤ 1 := by rw [hdy]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hpow : 1 ≤ delta^(-(1/(J:ℝ))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (neg_nonpos.mpr (by positivity))
  exact max_le (by nlinarith only [hpow]) (hp.trans (by nlinarith only [hpow]))

/-- With the spatial exponent in[0,3], interpolation spends at most3/J
of the original dyadic scale power, plus the fixed constant512. -/
lemma menu_gap_power_cost {delta s : ℝ} (J m level : ℕ) (hJ : 0 < J)
    (hbL : phaseDepth m ≤ level) (hdy : delta=(2:ℝ)⁻¹^level)
    (hs : 0 ≤ s) (hs3 : s ≤ 3) :
    (max 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ)))^s ≤ 512*delta^(-(3/(J:ℝ))) := by
  have hd : 0 < delta := by rw [hdy]; positivity
  have hd1 : delta ≤ 1 := by rw [hdy]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  have hp := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ max 8 (((2^((phaseDepth m-m)/J+1):ℕ):ℝ)))
    (menu_gap_cost J m level hJ hbL hdy) hs
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hd.le _),←Real.rpow_mul hd.le] at hp
  have h8 : (8:ℝ)^s ≤ 512 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤8) hs3
    norm_num at hh
    exact hh
  have hexp : -(3/(J:ℝ)) ≤ -(1/(J:ℝ))*s := by
    have hh := div_le_div_of_nonneg_right hs3 hJr.le
    calc
      _ ≤ -(s/(J:ℝ)) := neg_le_neg hh
      _ = _ := by ring
  have hdPow := Real.rpow_le_rpow_of_exponent_ge hd hd1 hexp
  exact hp.trans (mul_le_mul h8 hdPow (by positivity) (by norm_num))

/-- The fixed number J is selected before the source. Every later source
uses exactly the same number of horizontal caller slots, and the actual
reference E2 slice satisfies the full radius range with explicit costs. -/
theorem fixed_menu_reference_all_radius_bounds {n J : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
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
    (u : Index) (hu : u∈points D a m (phaseDepth m) E p)
    (r : ℝ) (hr : horizontalMesh m ≤ r) (hr1 : r ≤ 1) :
    let L := lowerCountCoefficient D.thickness zeta population profileUpper
    let U := upperCountCoefficient D.thickness zeta profileLower
    let B : ℝ := max 8 ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let P := realizedSlice (points D a m (phaseDepth m) E p) (horizontalMesh m) (u (3:Fin 4))
    (L/((Q:ℝ)^4*U))*(r/horizontalMesh m)^(3-extremalExponent) ≤
        B^(3-extremalExponent)*ballCount P (realized (horizontalMesh m) u) r ∧
      ballCount P (realized (horizontalMesh m) u) r ≤
        (729*((Q:ℝ)^4*U/L))*B^(3-extremalExponent)*(r/horizontalMesh m)^(3-extremalExponent) := by
  exact caller_reference_all_radius_bounds h original R level Hbackbone m
    ((phaseDepth m-m)/J+1) hm6 hbL hJ (depths J m) (depths_zero J m) (depths_last J m hJ hm6)
    (fun j => (depths_bounds J m hm6 j).2) (depths_monotone J m) (depths_gap J m hJ)
    E hE p hp population hpopulation hret profileLower profileUpper hL hU Hprofile Q Hcaller u hu r hr hr1

end NativeFixedMenuSliceAD
