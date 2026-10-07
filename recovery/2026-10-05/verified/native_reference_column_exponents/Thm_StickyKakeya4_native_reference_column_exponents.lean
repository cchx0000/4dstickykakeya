import Theorems.Thm_StickyKakeya4_native_column_population_bounds
import Theorems.Thm_StickyKakeya4_native_paid_parent_scale_budget

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4500000

noncomputable section
namespace NativeReferenceColumnExponents
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeAnisotropicGlobalSourceBridge NativeAnisotropicPairNumerator
open NativeSliceCountComparison NativeSlicePopulationAlgebra NativeColumnPopulationBounds
open NativeIncidenceMultiplicityTower

def lowerCountCoefficient (delta zeta population profileUpper : ℝ) : ℝ :=
  (population*delta^(2*zeta)/43904)/profileUpper

def upperCountCoefficient (delta zeta profileLower : ℝ) : ℝ :=
  (pairUpperConstant*delta^(-2*zeta))/profileLower

lemma count_coefficients_pos {delta zeta population profileLower profileUpper : ℝ}
    (hd : 0 < delta) (hp : 0 < population) (hL : 0 < profileLower) (hU : 0 < profileUpper) :
    0 < lowerCountCoefficient delta zeta population profileUpper ∧
      0 < upperCountCoefficient delta zeta profileLower := by
  have hC := pairUpperConstant_pos
  dsimp [lowerCountCoefficient,upperCountCoefficient]
  constructor <;> positivity

lemma quotient_power_bounds {I N H r kappa Al Au Ml Mu M : ℝ}
    (hH : 0 < H) (hr : 0 < r) (hN : 0 ≤ N) (hMl : 0 < Ml) (hMu : 0 < Mu)
    (hread : M*N=I)
    (hIlower : Al*r^(-3:ℝ) ≤ H*I) (hIupper : H*I ≤ Au*r^(-3:ℝ))
    (hMlower : Ml*r^(-kappa) ≤ M) (hMupper : M ≤ Mu*r^(-kappa)) :
    (Al/Mu)*r^(kappa-3) ≤ H*N ∧ H*N ≤ (Au/Ml)*r^(kappa-3) := by
  have hread' : M*(H*N)=H*I := by rw [←hread]; ring
  have hh := slice_power_bounds (I:=H*I) (N:=H*N) (Z:=1) (S:=H*N) (H:=1) (C:=1)
    (Al:=Al) (Au:=Au) (Zl:=1) (Zu:=1) (Ml:=Ml) (Mu:=Mu) (M:=M) (r:=r) (kappa:=kappa)
    (by norm_num) (by norm_num) hr (mul_nonneg hH.le hN) (mul_nonneg hH.le hN)
    (by norm_num) (by norm_num) hMl hMu hread' (by simp) (by simp)
    (by simpa only [one_mul] using hIlower) (by simpa only [one_mul] using hIupper)
    (by norm_num) (by norm_num) hMlower hMupper
  simpa only [one_mul,mul_one] using hh

/-- Actual phase/shading numerators and actual reference multiplicity
bounds yield the global spatial exponent3-kappa. No point-count exponent
or AD property is an input. -/
theorem reference_column_point_power_bounds {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m f : ℕ) (hm6 : 6 ≤ m) (hmf : m ≤ f) (hfL : f ≤ level)
    (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population : ℝ) (hpopulation : 0 < population)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hprofile : profileLower*(relativeWidth m f)^(-extremalExponent) ≤
        multiplicity ((parentEdges D a (2^m) E p).image (columnPair D a m f p)) ∧
      multiplicity ((parentEdges D a (2^m) E p).image (columnPair D a m f p)) ≤
        profileUpper*(relativeWidth m f)^(-extremalExponent)) :
    lowerCountCoefficient D.thickness zeta population profileUpper*(relativeWidth m f)^(extremalExponent-3) ≤
        (64/((2^m:ℕ):ℝ))*(points D a m f E p).card ∧
      (64/((2^m:ℕ):ℝ))*(points D a m f E p).card ≤
        upperCountCoefficient D.thickness zeta profileLower*(relativeWidth m f)^(extremalExponent-3) := by
  have hb := reference_numerator_height_bounds h original R level Hbackbone m f hm6 hmf hfL hwindow
    E hE p hp population hpopulation.le hret
  have hh := quotient_power_bounds (by positivity : (0:ℝ)<64/((2^m:ℕ):ℝ))
    (relativeWidth_pos m f) (Nat.cast_nonneg (points D a m f E p).card) hL hU
    (column_multiplicity_card D a m f E p hp) hb.1 hb.2.1 Hprofile.1 Hprofile.2
  exact hh

/-- Every occupied fixed-height slice has the derived spatial exponent.
Class uniformity is the literal reference relation installed before E2,
and its27Q^4 averaging loss remains explicit. -/
theorem reference_height_point_power_bounds {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (level : ℕ) (Hbackbone : HasOriginalBackbone D original R a level zeta)
    (m f : ℕ) (hm6 : 6 ≤ m) (hmf : m ≤ f) (hfL : f ≤ level)
    (hwindow : (64/((2^m:ℕ):ℝ))^2 ≤ 64/((2^f:ℕ):ℝ))
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population : ℝ) (hpopulation : 0 < population)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (profileLower profileUpper : ℝ) (hL : 0 < profileLower) (hU : 0 < profileUpper)
    (Hprofile : profileLower*(relativeWidth m f)^(-extremalExponent) ≤
        multiplicity ((parentEdges D a (2^m) E p).image (columnPair D a m f p)) ∧
      multiplicity ((parentEdges D a (2^m) E p).image (columnPair D a m f p)) ≤
        profileUpper*(relativeWidth m f)^(-extremalExponent))
    (Q : ℕ)
    (HF : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2))
    (HC : HasUniformFibers (parentEdges D a (2^m) E p) Q
      (fun z => columnLabel D a (2^m) p (64/((2^m:ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) z.2))
    (z : ℤ) (hz : z∈(points D a m f E p).image (fun q => q (3:Fin 4))) :
    (lowerCountCoefficient D.thickness zeta population profileUpper/(10*27*(Q:ℝ)^4))*
        (relativeWidth m f)^(extremalExponent-3) ≤ (heightSlice (points D a m f E p) z).card ∧
      ((heightSlice (points D a m f E p) z).card:ℝ) ≤
        ((43904*27*(Q:ℝ)^4/population)*upperCountCoefficient D.thickness zeta profileLower)*
          (relativeWidth m f)^(extremalExponent-3) := by
  have hb := reference_numerator_height_bounds h original R level Hbackbone m f hm6 hmf hfL hwindow
    E hE p hp population hpopulation.le hret
  have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
    rw [NativeLocalParentScales.relative_scale Hbackbone.2.1 (hmf.trans hfL)]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have havg := reference_slice_average_cross h original Hbackbone.1 Hbackbone.2.2.1 m f hmf hscale
    E (hE.trans (filter_subset _ _)) p Q HF HC z hz
  have hQ := NativePaidParentScaleBudget.uniform_radix_pos _ hp _ Q HF
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hAvgU : ((heightSlice (points D a m f E p) z).card:ℝ)*
      ((points D a m f E p).image (fun q => q (3:Fin 4))).card ≤
      (27*(Q:ℝ)^4)*(points D a m f E p).card := by exact_mod_cast havg.1
  have hAvgL : ((points D a m f E p).card:ℝ) ≤
      (27*(Q:ℝ)^4)*(heightSlice (points D a m f E p) z).card*
        ((points D a m f E p).image (fun q => q (3:Fin 4))).card := by exact_mod_cast havg.2
  have hh := slice_power_bounds (by positivity : (0:ℝ)<64/((2^m:ℕ):ℝ))
    (by positivity : (0:ℝ)<27*(Q:ℝ)^4) (relativeWidth_pos m f)
    (Nat.cast_nonneg (points D a m f E p).card) (Nat.cast_nonneg (heightSlice (points D a m f E p) z).card)
    (by positivity : (0:ℝ)<population/43904) (by norm_num : (0:ℝ)<10) hL hU
    (column_multiplicity_card D a m f E p hp) hAvgU hAvgL hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 Hprofile.1 Hprofile.2
  convert hh using 1 <;> dsimp [lowerCountCoefficient,upperCountCoefficient] <;> ring

end NativeReferenceColumnExponents
