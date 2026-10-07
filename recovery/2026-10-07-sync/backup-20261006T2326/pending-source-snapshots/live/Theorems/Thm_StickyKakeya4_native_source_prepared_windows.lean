import Theorems.Thm_StickyKakeya4_native_source_window_Y_ad
import Theorems.Thm_StickyKakeya4_native_window_menu_interpolation
import Theorems.Thm_StickyKakeya4_native_window_XY_relation_menu
import Theorems.Thm_StickyKakeya4_native_source_window_XY_ad
import Theorems.Thm_StickyKakeya4_native_actual_window_quotient
import Theorems.Thm_StickyKakeya4_native_actual_window_global_count
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
namespace NativeSourcePreparedWindows
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

open NativeSourceWindowYAD NativeWindowNesting NativeWindowRealInterpolation

/-- All finite prepared profiles are generated on the SAME actual third core.
The relation values vary with the prepared tests, while their fixed number
was installed before this T was selected. No AD profile is an input. -/
theorem source_prepared_window_profiles {n level J dCore : ℕ} {D : FiniteScaleSource n}
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
    (m ell : ℕ) (hm : 12 ≤ m) (hfL : phaseDepth m ≤ level) (hJ : 0 < J)
    (Hqueries : ∀i j : Fin (J+1),
      let f := NativeFixedHorizontalMenu.depths J m i
      let d := NativeWindowXYRelationMenu.depth J m f j
      HasUniformFibers E Q2 (fixedPair D a level d d (representative h R a (2^d))) ∧
      HasUniformFibers E Q2 (fixedPair D a level d (max 6 (f-m+3)) (representative h R a (2^d))))
    (p : Parent) (population fullLower fullUpper : ℝ) (hpopulation : 0 < population)
    (hfullLower : 0 < fullLower) (hfullUpper : 0 < fullUpper)
    (hpop : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (Hfull : ∀i j : Fin (J+1),
      let f := NativeFixedHorizontalMenu.depths J m i
      let d := NativeWindowXYRelationMenu.depth J m f j
      fullLower*(relativeWidth m d)^(-extremalExponent) ≤
        (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level d (parentEdges D a (2^m) E p))).toReal ∧
      (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level d (parentEdges D a (2^m) E p))).toReal ≤
        fullUpper*(relativeWidth m d)^(-extremalExponent))
    (Hcolumns : ∀i j : Fin (J+1),
      let f := NativeFixedHorizontalMenu.depths J m i
      let d := NativeWindowXYRelationMenu.depth J m f j
      HasUniformFibers (parentEdges D a (2^m) E p) Q2
      (fun z => columnLabel D a (2^m) p (64/((2^d:ℕ):ℝ)) (64/((2^(f-m+3):ℕ):ℝ)) z.2))
    (S T : Finset (Fin n × Index)) (hS : S⊆parentEdges D a (2^m) E p) (hT : T⊆S) (hTn : T.Nonempty)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (Lip : ℝ) (hLip0 : 0 ≤ Lip)
    (hF : ∀z∈S,‖F (translatedHeight D a m z.2)‖ ≤ (1/4:ℝ))
    (hLip : ∀z∈S,∀w∈S,‖F (translatedHeight D a m z.2)-F (translatedHeight D a m w.2)‖ ≤
      Lip*|referenceHeight m (translatedHeight D a m z.2)-referenceHeight m (translatedHeight D a m w.2)|)
    (Qnew : ℕ)
    (HT : ∀i : Fin (J+1),
      let f := NativeFixedHorizontalMenu.depths J m i
      HasUniformFibers T Qnew (fun z => xyPoint D a m ell f f p P hP hell hell4 hd F z.2))
    (HC : ∀i j : Fin (J+1),
      let f := NativeFixedHorizontalMenu.depths J m i
      let d := NativeWindowXYRelationMenu.depth J m f j
      HasUniformFibers T Qnew (fun z => horizontalCoarsen f d (xyPoint D a m ell f f p P hP hell hell4 hd F z.2)))
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
    let KXY := windowConstant L U retain loss Q2 Qnew ((2*menuRadius Lip+1)^3) ((phaseDepth m-m)/J+1)
    let KY := quotientConstant (ell-1) (4-ell) (1/((32:ℝ)^(ell-1)*CX)) KXY (3-extremalExponent)
    let A := T.image (fun x => NativeReferenceXYGridMaps.pxy D a m ell p P hP hell hell4 hd F x.2)
    ∀i : Fin (J+1),∀z∈A,
      let f := NativeFixedHorizontalMenu.depths J m i
      ADBounds (points A (NativeWindowQuotientTransport.factor m f)
        (mu m*(NativeWindowQuotientTransport.factor m f:ℝ)) z)
        (mu m*(NativeWindowQuotientTransport.factor m f:ℝ)) KY (4-(ell:ℝ)-extremalExponent) ∧
      ((atPoint A (NativeWindowQuotientTransport.factor m f) z).card:ℝ) ≤
        KY*(windowHalfWidth m f:ℝ)^(4-(ell:ℝ)-extremalExponent) := by
  intro eps C L U KXY KY A i z _hz f
  have hm6 : 6 ≤ m := by omega
  have hf := NativeFixedHorizontalMenu.depths_bounds J m hm6 i
  have HH := source_window_quotient_AD h original R HB E hE F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hlambda hRich hcost1 hcost2 m ell f ((phaseDepth m-m)/J+1)
    hm hf.1 hf.2 hfL hJ (NativeWindowXYRelationMenu.depth J m f)
    (NativeWindowXYRelationMenu.depth_first J m f hf.1)
    (NativeWindowXYRelationMenu.depth_last J m f hJ hm6 hf.2)
    (fun j => (NativeWindowXYRelationMenu.depth_bounds J m f hm6 hf.1 j).2)
    (NativeWindowXYRelationMenu.depth_monotone J m f)
    (NativeWindowXYRelationMenu.depth_gap J m f hJ)
    (Hqueries i) p population fullLower fullUpper hpopulation hfullLower hfullUpper hpop
    (Hfull i) (Hcolumns i) S T hS hT hTn P hP hell hell4 hd F Lip hLip0 hF hLip Qnew
    (HT i) (HC i) retain loss hretain hloss hret graphPlane Hgraph Fraw hFraw hpre Hread hField
    recordPopulation recordLower recordUpper recordLambda recordG Cpre threshold L3 Rel3 CX Hdata hdimension
  exact ⟨HH.1 _,HH.2 _⟩

/-- Actual original source data generate every intermediate dyadic window,
including its independent global cover count, on the identical T. -/
theorem source_middle_window_profiles {n level J dCore : ℕ} {D : FiniteScaleSource n}
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
    (m ell : ℕ) (hm : 12 ≤ m) (hfL : phaseDepth m ≤ level) (hJ : 0 < J)
    (Hqueries : ∀i j : Fin (J+1),
      let f := NativeFixedHorizontalMenu.depths J m i
      let d := NativeWindowXYRelationMenu.depth J m f j
      HasUniformFibers E Q2 (fixedPair D a level d d (representative h R a (2^d))) ∧
      HasUniformFibers E Q2 (fixedPair D a level d (max 6 (f-m+3)) (representative h R a (2^d))))
    (p : Parent) (population fullLower fullUpper : ℝ) (hpopulation : 0 < population)
    (hfullLower : 0 < fullLower) (hfullUpper : 0 < fullUpper)
    (hpop : population*(R.filter (fun i => parentLabel D a (2^m) i=p)).card ≤
      D.thickness*(parentEdges D a (2^m) E p).card)
    (Hfull : ∀i j : Fin (J+1),
      let f := NativeFixedHorizontalMenu.depths J m i
      let d := NativeWindowXYRelationMenu.depth J m f j
      fullLower*(relativeWidth m d)^(-extremalExponent) ≤
        (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level d (parentEdges D a (2^m) E p))).toReal ∧
      (NativeFiniteKakeyaCounts.multiplicity
          (NativeFullCoarseShadow.fullSource h R a level d (parentEdges D a (2^m) E p))).toReal ≤
        fullUpper*(relativeWidth m d)^(-extremalExponent))
    (Hcolumns : ∀i j : Fin (J+1),
      let f := NativeFixedHorizontalMenu.depths J m i
      let d := NativeWindowXYRelationMenu.depth J m f j
      HasUniformFibers (parentEdges D a (2^m) E p) Q2
      (fun z => columnLabel D a (2^m) p (64/((2^d:ℕ):ℝ)) (64/((2^(f-m+3):ℕ):ℝ)) z.2))
    (S T : Finset (Fin n × Index)) (hS : S⊆parentEdges D a (2^m) E p) (hT : T⊆S) (hTn : T.Nonempty)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (Lip : ℝ) (hLip0 : 0 ≤ Lip)
    (hF : ∀z∈S,‖F (translatedHeight D a m z.2)‖ ≤ (1/4:ℝ))
    (hLip : ∀z∈S,∀w∈S,‖F (translatedHeight D a m z.2)-F (translatedHeight D a m w.2)‖ ≤
      Lip*|referenceHeight m (translatedHeight D a m z.2)-referenceHeight m (translatedHeight D a m w.2)|)
    (Qnew : ℕ)
    (HT : ∀i : Fin (J+1),
      let f := NativeFixedHorizontalMenu.depths J m i
      HasUniformFibers T Qnew (fun z => xyPoint D a m ell f f p P hP hell hell4 hd F z.2))
    (HC : ∀i j : Fin (J+1),
      let f := NativeFixedHorizontalMenu.depths J m i
      let d := NativeWindowXYRelationMenu.depth J m f j
      HasUniformFibers T Qnew (fun z => horizontalCoarsen f d (xyPoint D a m ell f f p P hP hell hell4 hd F z.2)))
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
    let KXY := windowConstant L U retain loss Q2 Qnew ((2*menuRadius Lip+1)^3) ((phaseDepth m-m)/J+1)
    let KY := quotientConstant (ell-1) (4-ell) (1/((32:ℝ)^(ell-1)*CX)) KXY (3-extremalExponent)
    let A := T.image (fun x => NativeReferenceXYGridMaps.pxy D a m ell p P hP hell hell4 hd F x.2)
    ∀f : ℕ,m ≤ f → f ≤ phaseDepth m → ∀z∈A,
      ∃lo hi : Fin (J+1),
        let fl := NativeFixedHorizontalMenu.depths J m lo
        let fh := NativeFixedHorizontalMenu.depths J m hi
        let Ds := (2:ℕ)^(fh-f)
        let Db := (2:ℕ)^(f-fl)
        fl ≤ f ∧ f ≤ fh ∧
        Ds ≤ 2^((phaseDepth m-m)/J+1) ∧ Db ≤ 2^((phaseDepth m-m)/J+1) ∧
        ADBounds (points A (NativeWindowQuotientTransport.factor m f)
          (mu m*(NativeWindowQuotientTransport.factor m f:ℝ)) z)
          (mu m*(NativeWindowQuotientTransport.factor m f:ℝ))
          (NativeHalfScaleInterpolation.constant ((1/KY)/(Ds:ℝ)^(4-ell))
            (NativeWindowIntegerInterpolation.upperConstant (4-ell) Db KY (4-(ell:ℝ)-extremalExponent))
            ((Db:ℝ)^(4-ell)*KY) (4-(ell:ℝ)-extremalExponent))
          (4-(ell:ℝ)-extremalExponent) ∧
        ((atPoint A (NativeWindowQuotientTransport.factor m f) z).card:ℝ) ≤
          (Db:ℝ)^(4-ell)*KY*(windowHalfWidth m fl:ℝ)^(4-(ell:ℝ)-extremalExponent) := by
  intro eps C L U KXY KY A f hmf hfb z hz
  have HH := source_prepared_window_profiles h original R HB E hE F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hlambda hRich hcost1 hcost2 m ell hm hfL hJ Hqueries
    p population fullLower fullUpper hpopulation hfullLower hfullUpper hpop Hfull Hcolumns
    S T hS hT hTn P hP hell hell4 hd F Lip hLip0 hF hLip Qnew HT HC retain loss hretain hloss hret
    graphPlane Hgraph Fraw hFraw hpre Hread hField recordPopulation recordLower recordUpper
    recordLambda recordG Cpre threshold L3 Rel3 CX Hdata hdimension
  have hKY : 0 < KY := lt_of_lt_of_le (by norm_num) (quotientConstant_one_le _ _ _ _ _)
  exact NativeWindowMenuInterpolation.middle_window_AD A m (by omega) hJ hKY hKY.le
    (by linarith only [hdimension]) (fun i w hw => (HH i w hw).1)
    (fun i w hw => (HH i w hw).2) f hmf hfb z hz

end NativeSourcePreparedWindows
