import Theorems.Thm_StickyKakeya4_native_height_window_boundary
import Theorems.Thm_StickyKakeya4_native_variable_height_source_counts
import Theorems.Thm_StickyKakeya4_native_variable_height_source_bridge
import Theorems.Thm_StickyKakeya4_native_variable_height_reference_counts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeWindowSourceCounts
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeLocalPairFibers NativeCoarseShadingUniformity NativeCoarseDirectionThinning
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeColumnPopulationBounds NativeReferenceColumnExponents
open NativeVariableHeightPopulation NativeVariableHeightReferenceCounts NativeIncidenceMultiplicityTower

open NativeHeightWindowBoundary NativeVariableHeightSourceCounts

/-- Source count law on all prepared heights H≤8. The only endpoint cost
is an explicit factor8 from time-only coarsening; its lower is unchanged. -/
theorem queried_window_point_power_bounds {n level : ℕ} {D : FiniteScaleSource n}
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
    (m f b : ℕ) (hm6 : 6 ≤ m) (hmf : m ≤ f) (hbf : b ≤ f) (hfL : f ≤ level) (hb3 : 3 ≤ b)
    (hwindow : (64/((2^m:ℕ):ℝ))*(64/((2^b:ℕ):ℝ)) ≤ 8*(64/((2^f:ℕ):ℝ)))
    (HF : HasUniformFibers E Q2 (fixedPair D a level f f (representative h R a (2^f))))
    (HC : HasUniformFibers E Q2 (fixedPair D a level f (max 6 b) (representative h R a (2^f))))
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
        8*((NativeVariableHeightNumeratorUpper.pairUpperConstant*D.thickness^(-2*zeta))/((eps/C)*fullLower))*
          (relativeWidth m f)^(extremalExponent-3) := by
  intro eps C H
  have hb : b ≤ max 6 b := le_max_right _ _
  have hheight : 64/((2^(max 6 b):ℕ):ℝ) ≤ 64/((2^b:ℕ):ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hb
  have hwindow' : (64/((2^m:ℕ):ℝ))*(64/((2^(max 6 b):ℕ):ℝ)) ≤ 8*(64/((2^f:ℕ):ℝ)) :=
    (mul_le_mul_of_nonneg_left hheight (by positivity)).trans hwindow
  have hbase := queried_column_point_power_bounds h original R HB E hE F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hlambda hRich hcost1 hcost2 m f (max 6 b) hmf
    (max_le (hm6.trans hmf) hbf) hfL (le_max_left _ _) hwindow' HF HC p hp
    population fullLower fullUpper hpopulation hfullLower hfullUpper hret Hfull
  have hboundary := weighted_point_counts_max_six D a m f b hb3 E p
  constructor
  · exact hbase.1.trans hboundary.1
  · exact hboundary.2.trans ((mul_le_mul_of_nonneg_left hbase.2 (by norm_num : (0:ℝ)≤8)).trans_eq (by ring))

/-- Exact prepared window relation in the existing chart. The height depth
is f-m+3, and its shear drift is exactly8 times the matching spatial width. -/
lemma prepared_window_geometry (m f g : ℕ) (hm6 : 6 ≤ m) (hmf : m ≤ f)
    (hmg : m ≤ g) (hgf : g ≤ f) (hf : f ≤ NativeSquaredGrainQueries.phaseDepth m) :
    3 ≤ f-m+3 ∧ f-m+3 ≤ g ∧
      (64/((2^m:ℕ):ℝ))*(64/((2^(f-m+3):ℕ):ℝ)) ≤ 8*(64/((2^g:ℕ):ℝ)) := by
  have hdepth : f-m+3 ≤ g := by dsimp [NativeSquaredGrainQueries.phaseDepth] at hf; omega
  refine ⟨by omega,hdepth,?_⟩
  have hp : ((2^m:ℕ):ℝ)*((2^(f-m+3):ℕ):ℝ)=8*((2^f:ℕ):ℝ) := by
    rw [←Nat.cast_mul,←pow_add,show m+(f-m+3)=f+3 by omega,pow_add]
    push_cast
    ring
  have he : (64/((2^m:ℕ):ℝ))*(64/((2^(f-m+3):ℕ):ℝ))=8*(64/((2^f:ℕ):ℝ)) := by
    field_simp
    nlinarith only [hp]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hgf

end NativeWindowSourceCounts
