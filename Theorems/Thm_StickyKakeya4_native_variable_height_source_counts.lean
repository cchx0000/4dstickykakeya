import Theorems.Thm_StickyKakeya4_native_variable_height_source_bridge
import Theorems.Thm_StickyKakeya4_native_variable_height_reference_counts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeVariableHeightSourceCounts
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeLocalPairFibers NativeCoarseShadingUniformity NativeCoarseDirectionThinning
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeColumnPopulationBounds NativeReferenceColumnExponents
open NativeVariableHeightPopulation NativeVariableHeightReferenceCounts NativeIncidenceMultiplicityTower

/-- Source reference-count law at independent physical height H and spatial
width sigma. Both original-source multiplicity bounds are read through the
actual queried time-filling bridge. No local height-density or point-count
exponent is an input; one E2 and the original R remain fixed. -/
theorem queried_column_point_power_bounds {n level : ℕ} {D : FiniteScaleSource n}
    {eta eta2 zeta a lambda c1 c2 : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (R : Finset (Fin n)) (HB : HasOriginalBackbone D original R a level zeta)
    (E : Finset (Fin n × Index)) (hE : E⊆retained original R)
    (F1 F2 G Q1 Q2 : ℕ) (hF1 : 0 < F1) (hG : 0 < G) (hQ2 : 0 < Q2)
    (hQ1 : 1 ≤ Q1) (hGF : G ≤ F2) (heta2 : 0 ≤ eta2) (hlambda : 0 < lambda)
    (hRich : ∀e,e∈E → D.thickness^eta*(2^level:ℕ)/
      (16384*(((F1:ℝ)/lambda)*(G:ℝ))*(Q2:ℝ)^2) ≤
        (pairFiber D a (2^level) E (localPair D a (2^level) e)).card)
    (hcost1 : (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c1))
    (hcost2 : (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta2) ≤ D.thickness^(-c2))
    (m f b : ℕ) (hmf : m ≤ f) (hbf : b ≤ f) (hfL : f ≤ level) (hb6 : 6 ≤ b)
    (hwindow : (64/((2^m:ℕ):ℝ))*(64/((2^b:ℕ):ℝ)) ≤ 8*(64/((2^f:ℕ):ℝ)))
    (HF : HasUniformFibers E Q2 (fixedPair D a level f f (representative h R a (2^f))))
    (HC : HasUniformFibers E Q2 (fixedPair D a level f b (representative h R a (2^f))))
    (p : Parent) (hp : (parentEdges D a (2^m) E p).Nonempty)
    (population fullLower fullUpper : ℝ) (hpopulation : 0 < population)
    (hfullLower : 0 < fullLower) (hfullUpper : 0 < fullUpper)
    (hret : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (Hfull : fullLower*(relativeWidth m f)^(-extremalExponent) ≤
        (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E p))).toReal ∧
      (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E p))).toReal ≤
        fullUpper*(relativeWidth m f)^(-extremalExponent)) :
    let eps := lambda*D.thickness^(c1+3*c2)
    let C := NativeVariableHeightSourceBridge.comparisonCost
    let H := 64/((2^b:ℕ):ℝ)
    lowerCountCoefficient D.thickness zeta population ((C/eps)*fullUpper)*
        (relativeWidth m f)^(extremalExponent-3) ≤ H*(NativeHeightWindowRelations.points D a m f b E p).card ∧
      H*(NativeHeightWindowRelations.points D a m f b E p).card ≤
        ((NativeVariableHeightNumeratorUpper.pairUpperConstant*D.thickness^(-2*zeta))/((eps/C)*fullLower))*
          (relativeWidth m f)^(extremalExponent-3) := by
  intro eps C H
  have hEO : E⊆incidences original := hE.trans (filter_subset _ _)
  have hER : ∀z∈E,z.1∈R := fun z hz => (mem_filter.mp (hE hz)).2
  have hbridge := NativeVariableHeightSourceBridge.queried_global_source_comparison h original HB.1 HB.2.2.1
    R E hEO hER F1 F2 G Q1 Q2 hF1 hG hQ2 hQ1 hGF heta2 HB.2.1 hlambda hRich hcost1 hcost2
    f m b hmf hbf hfL hb6 hwindow HF HC p hp
  have heps : 0 < eps := mul_pos hlambda (Real.rpow_pos_of_pos h.1.2.1 _)
  have hC : 0 < C := NativeVariableHeightSourceBridge.comparisonCost_pos
  have hL : 0 < (eps/C)*fullLower := by positivity
  have hU : 0 < (C/eps)*fullUpper := by positivity
  apply NativeVariableHeightReferenceCounts.reference_column_point_power_bounds h original R level HB
    m f b hmf hbf hfL hb6 hwindow E hE p hp population hpopulation hret
    ((eps/C)*fullLower) ((C/eps)*fullUpper) hL hU
  constructor
  · calc
      _ = (eps/C)*(fullLower*(relativeWidth m f)^(-extremalExponent)) := by ring
      _ ≤ (eps/C)*(NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E p))).toReal :=
        mul_le_mul_of_nonneg_left Hfull.1 (by positivity)
      _ ≤ _ := hbridge.1
  · calc
      _ ≤ (C/eps)*(NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level f (parentEdges D a (2^m) E p))).toReal := hbridge.2
      _ ≤ (C/eps)*(fullUpper*(relativeWidth m f)^(-extremalExponent)) :=
        mul_le_mul_of_nonneg_left Hfull.2 (by positivity)
      _ = _ := by ring

end NativeVariableHeightSourceCounts
