import Theorems.Thm_StickyKakeya4_native_actual_window_XY_ad
import Theorems.Thm_StickyKakeya4_native_window_source_classes
import Theorems.Thm_StickyKakeya4_native_window_source_counts
import Theorems.Thm_StickyKakeya4_native_reference_slice_class_bounds
import Theorems.Thm_StickyKakeya4_native_variable_height_source_bridge
import Theorems.Thm_StickyKakeya4_native_variable_height_reference_counts

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section
namespace NativeSourceWindowXYAD
open NativeHorizontalGrainSlice NativeConditionedPairMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeLocalPairFibers NativeCoarseShadingUniformity NativeCoarseDirectionThinning
open NativeJointUniformCoarseRelations NativeFixedCompactKakeyaExponent NativeMiddleWindowBalance
open NativeAnisotropicShortRowGeometry NativeColumnPopulationBounds NativeReferenceColumnExponents
open NativeVariableHeightPopulation NativeVariableHeightReferenceCounts NativeIncidenceMultiplicityTower

open NativeWindowSourceCounts NativeSliceClassAlgebra NativeReferenceSliceClassBounds NativeAnisotropicSliceLabels

open NativeActualWindowXYAD NativeWindowEncodedCapacities NativeWindowQuotientTransport
open NativeReferenceXYGridPoints NativeReferenceXYGridLinear NativeTranslatedGrainHeightOverlap
open NativeTranslatedGrainHeightMetric NativeOffsetAngularGeometry NativeSliceClassBalls
open NativeSliceRadiusInterpolation NativeWindowXYMetric NativeSquaredGrainQueries FiniteVoronoiRealADCoarsening
open scoped Matrix.Norms.Elementwise

/-- Actual original-source queries and physical profiles produce window
XY regularity on the prescribed third core, with no point-count or AD premise. -/
theorem source_window_AD {n level J : ℕ} {D : FiniteScaleSource n}
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
    (m ell f gap : ℕ) (hm : 12 ≤ m) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m)
    (hfL : phaseDepth m ≤ level) (hJ : 0 < J) (depth : Fin (J+1) → ℕ)
    (hfirst : depth 0=m) (hlast : depth (Fin.last J)=f) (hdepth : ∀j,depth j ≤ f)
    (hmono : Monotone depth) (hgap : ∀j : Fin J,depth j.succ-depth j.castSucc ≤ gap)
    (Hqueries : ∀j,
      HasUniformFibers E Q2 (fixedPair D a level (depth j) (depth j) (representative h R a (2^(depth j)))) ∧
      HasUniformFibers E Q2 (fixedPair D a level (depth j) (max 6 (f-m+3)) (representative h R a (2^(depth j)))))
    (p : Parent) (population fullLower fullUpper : ℝ) (hpopulation : 0 < population)
    (hfullLower : 0 < fullLower) (hfullUpper : 0 < fullUpper)
    (hpop : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (Hfull : ∀j,
      fullLower*(relativeWidth m (depth j))^(-extremalExponent) ≤
        (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level (depth j) (parentEdges D a (2^m) E p))).toReal ∧
      (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level (depth j) (parentEdges D a (2^m) E p))).toReal ≤
        fullUpper*(relativeWidth m (depth j))^(-extremalExponent))
    (Hcolumns : ∀j,HasUniformFibers (parentEdges D a (2^m) E p) Q2
      (fun z => columnLabel D a (2^m) p (64/((2^(depth j):ℕ):ℝ)) (64/((2^(f-m+3):ℕ):ℝ)) z.2))
    (S T : Finset (Fin n × Index)) (hS : S⊆parentEdges D a (2^m) E p) (hT : T⊆S) (hTn : T.Nonempty)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (Lip : ℝ) (hLip0 : 0 ≤ Lip)
    (hF : ∀z∈S,‖F (translatedHeight D a m z.2)‖ ≤ (1/4:ℝ))
    (hLip : ∀z∈S,∀w∈S,‖F (translatedHeight D a m z.2)-F (translatedHeight D a m w.2)‖ ≤
      Lip*|referenceHeight m (translatedHeight D a m z.2)-referenceHeight m (translatedHeight D a m w.2)|)
    (Qnew : ℕ)
    (HT : HasUniformFibers T Qnew (fun z => xyPoint D a m ell f f p P hP hell hell4 hd F z.2))
    (HC : ∀j,HasUniformFibers T Qnew
      (fun z => horizontalCoarsen f (depth j) (xyPoint D a m ell f f p P hP hell hell4 hd F z.2)))
    (retain loss : ℝ) (hretain : 0 < retain) (hloss : 0 < loss)
    (hret : retain*((parentEdges D a (2^m) E p).card:ℝ) ≤ loss*T.card) :
    let eps := lambda*D.thickness^(c1+3*c2)
    let C := NativeVariableHeightSourceBridge.comparisonCost
    let L := lowerCountCoefficient D.thickness zeta population ((C/eps)*fullUpper)
    let U := 8*(NativeVariableHeightNumeratorUpper.pairUpperConstant*D.thickness^(-2*zeta))/((eps/C)*fullLower)
    ∀height : ℤ,ADBounds
      (realizedSlice (T.image (fun z => xyPoint D a m ell f f p P hP hell hell4 hd F z.2))
        (mu m*(NativeWindowQuotientTransport.factor m f:ℝ)) height)
      (mu m*(NativeWindowQuotientTransport.factor m f:ℝ)) (windowConstant L U retain loss Q2 Qnew ((2*menuRadius Lip+1)^3) gap)
      (3-extremalExponent) := by
  intro eps C L U
  have hparent := hTn.mono (hT.trans hS)
  have hlow (j : Fin (J+1)) : m ≤ depth j := by
    rw [←hfirst]
    exact hmono (Fin.zero_le j)
  have HF : HasUniformFibers (parentEdges D a (2^m) E p) Q2
      (fun z => columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^(f-m+3):ℕ):ℝ)) z.2) := by
    simpa only [hlast] using Hcolumns (Fin.last J)
  have Hcounts (j : Fin (J+1)) := NativeWindowSourceClasses.queried_window_class_power_bounds h original R HB
    E hE F1 F2 G Q1 Q2 hF1 hG hQ2 hQ1 hGF heta2 hlambda hRich hcost1 hcost2
    m f (depth j) (by omega) (hlow j) (hdepth j) hfb hfL
    (fun s hs => by
      rcases hs with rfl | rfl
      · simpa only [hlast] using Hqueries (Fin.last J)
      · exact Hqueries j)
    p hparent population fullLower fullUpper hpopulation hfullLower hfullUpper hpop
    (fun s hs => by
      rcases hs with rfl | rfl
      · simpa only [hlast] using Hfull (Fin.last J)
      · exact Hfull j) HF (Hcolumns j)
  have heps : 0 < eps := mul_pos hlambda (Real.rpow_pos_of_pos h.1.2.1 _)
  have hC : 0 < C := NativeVariableHeightSourceBridge.comparisonCost_pos
  have hPair := NativeVariableHeightNumeratorUpper.pairUpperConstant_pos
  have hL : 0 < L := by dsimp [L,lowerCountCoefficient]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  apply of_reference_counts h original HB.1 HB.2.2.1 level m ell f gap hm HB.2.1 hfL hmf hfb
    hJ depth hfirst hlast hdepth hmono hgap E S T (hE.trans (filter_subset _ _)) p hS hT hTn
    P hP hell hell4 hd F Lip hLip0 hF hLip Q2 Qnew HF HT HC L U retain loss hL hU hretain hloss hret
  · intro j
    exact (Hcounts j).1.1
  · intro j v hv
    exact ((Hcounts j).2 v hv).2

end NativeSourceWindowXYAD
