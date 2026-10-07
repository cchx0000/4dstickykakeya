import Theorems.Thm_StickyKakeya4_native_source_window_XY_ad
import Theorems.Thm_StickyKakeya4_native_actual_window_quotient
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
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
namespace NativeSourceWindowYAD
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

open NativeSourceWindowXYAD NativeThirdXYSourceData NativeReferenceXYGridField NativeGrainQuotientFibers
open NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightFibers NativeHeightSlopeCoordinates
open NativeQuotientLatticeTransport NativeEncodedQuotientAD NativeWindowXYLabels

/-- Source-generated XY window counts and the existing third-core source
X bound give quotient regularity of the same literal varying-field Y union. -/
theorem source_window_quotient_AD {n level J dCore : ℕ} {D : FiniteScaleSource n}
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
    (hret : retain*((parentEdges D a (2^m) E p).card:ℝ) ≤ loss*T.card)
    (graphPlane : Index → Submodule ℝ E4) (Hgraph : Finset (Fin n × Index))
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hFraw : ∀t,‖Fraw t‖ ≤ (1/4:ℝ))
    (hpre :
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell graphPlane Hgraph P hP hell hell4 hd
        (physicalMesh m (phaseDepth m)/8)
      S⊆second D a m ell graphPlane Sq)
    (Hread :
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell graphPlane Hgraph P hP hell hell4 hd
        (physicalMesh m (phaseDepth m)/8)
      ∀x∈second D a m ell graphPlane Sq,Fraw (rawHeight D m x.2)=
        nodeSlope P hP ell hell hell4 hd (sliceSpace (graphPlane (NativeSpatialAngularGeometry.spatialLabel D (2^m) x.2)))
          (slice_horizontal (graphPlane (NativeSpatialAngularGeometry.spatialLabel D (2^m) x.2))))
    (hField :
      let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell graphPlane Hgraph P hP hell hell4 hd
        (physicalMesh m (phaseDepth m)/8)
      F=fixedField D a m ell graphPlane Sq Fraw)
    (recordPopulation recordLower recordUpper recordLambda recordG Cpre threshold : ℝ)
    (L3 : ℕ) (Rel3 : Fin dCore → (Fin n × Index) → (Fin n × Index) → Prop) (CX : ℝ)
    (Hdata : HasThirdXYSourceData (J:=J) D zeta a m graphPlane E Hgraph S T P hP hell hell4 hd Fraw p
      recordPopulation recordLower recordUpper Q2 recordLambda recordG Cpre threshold L3 Rel3 CX)
    (hdimension : extremalExponent+(ell:ℝ) ≤ 4) :
    let eps := lambda*D.thickness^(c1+3*c2)
    let C := NativeVariableHeightSourceBridge.comparisonCost
    let L := lowerCountCoefficient D.thickness zeta population ((C/eps)*fullUpper)
    let U := 8*(NativeVariableHeightNumeratorUpper.pairUpperConstant*D.thickness^(-2*zeta))/((eps/C)*fullLower)
    let KXY := windowConstant L U retain loss Q2 Qnew ((2*menuRadius Lip+1)^3) gap
    ∀height : ℤ,ADBounds
      (((productSlice
        ((T.image (fun x => NativeReferenceXYGridMaps.pxy D a m ell p P hP hell hell4 hd F x.2)).image
          (window (8*NativeWindowQuotientTransport.factor m f) (NativeWindowQuotientTransport.factor m f))) height).image Prod.snd).image
            (NativeQuotientGridCenters.center (mu m*(NativeWindowQuotientTransport.factor m f:ℝ))))
      (mu m*(NativeWindowQuotientTransport.factor m f:ℝ))
      (quotientConstant (ell-1) (4-ell) (1/((32:ℝ)^(ell-1)*CX)) KXY (3-extremalExponent))
      (4-(ell:ℝ)-extremalExponent) := by
  intro eps C L U KXY
  let Sq := NativeWeightedGrainQuotientGeometry.retained D a m ell graphPlane Hgraph P hP hell hell4 hd
    (physicalMesh m (phaseDepth m)/8)
  have Hxy := source_window_AD h original R HB E hE F1 F2 G Q1 Q2 hF1 hG hQ2 hQ1 hGF
    heta2 hlambda hRich hcost1 hcost2 m ell f gap hm hmf hfb hfL hJ depth hfirst hlast hdepth hmono hgap
    Hqueries p population fullLower fullUpper hpopulation hfullLower hfullUpper hpop Hfull Hcolumns
    S T hS hT hTn P hP hell hell4 hd F Lip hLip0 hF hLip Qnew HT HC retain loss hretain hloss hret
  have hKXY : 0 < KXY := lt_of_lt_of_le (by norm_num) (NativeSliceADConstant.one_le_constant _ _ _ _)
  have hTI : T⊆incidences original := (hT.trans hS).trans ((filter_subset _ _).trans (hE.trans (filter_subset _ _)))
  have hpT : ∀x∈T,parentLabel D a (2^m) x.1=p := fun x hx => (mem_filter.mp (hS (hT hx))).2
  have HX : ∀x∈T,(rho m)^(-((ell:ℝ)-1)) ≤ CX*
      (referenceX D a m ell graphPlane T P hP hell hell4 hd (mu m)
        (referenceKey D a m ell graphPlane P hP hell hell4 hd (mu m) x)).card := by
    intro x hx
    rw [NativeReferenceXYGridPoints.mu_phase m (by omega)]
    exact Hdata.2.2.1 x hx
  have HH := NativeActualWindowQuotient.of_reference_cross h original HB.1 HB.2.2.1 m level ell f hm hmf hfb
    HB.2.1 hfL p graphPlane Sq T (hT.trans hpre) hTn hTI hpT P hP hell hell4 hd hdimension Fraw hFraw Hread
    CX KXY hKXY HX (by
      intro height
      have hh := Hxy height
      rw [hField] at hh
      simpa only [xyPoint,Finset.image_image,Function.comp_def,NativeWindowQuotientTransport.factor] using hh)
  rw [hField]
  exact HH.2

end NativeSourceWindowYAD
