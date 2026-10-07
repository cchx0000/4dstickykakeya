import Theorems.Thm_StickyKakeya4_native_source_prepared_windows
import Theorems.Thm_StickyKakeya4_native_window_all_dyadic_ad
import Theorems.Thm_StickyKakeya4_native_window_height_support
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
namespace NativeSourceAllWindows
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

open NativeSourcePreparedWindows

/-- Original source costs, genuine reference profiles and the one actual
third core generate every dyadic time-window profile after the fixed chart
contraction. Both global counts and all real ball radii are retained. -/
theorem source_all_dyadic_windows {n level J dCore : ℕ} {D : FiniteScaleSource n}
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
    (hdimension : extremalExponent+(ell:ℝ) ≤ 4)
    (hell2 : 2 ≤ ell) :
    let eps := lambda*D.thickness^(c1+3*c2)
    let C := NativeVariableHeightSourceBridge.comparisonCost
    let L := lowerCountCoefficient D.thickness zeta population ((C/eps)*fullUpper)
    let U := 8*(NativeVariableHeightNumeratorUpper.pairUpperConstant*D.thickness^(-2*zeta))/((eps/C)*fullLower)
    let KXY := windowConstant L U retain loss Q2 Qnew ((2*menuRadius Lip+1)^3) ((phaseDepth m-m)/J+1)
    let KY := quotientConstant (ell-1) (4-ell) (1/((32:ℝ)^(ell-1)*CX)) KXY (3-extremalExponent)
    let A := T.image (fun x => NativeReferenceXYGridMaps.pxy D a m ell p P hP hell hell4 hd F x.2)
    let s := 4-(ell:ℝ)-extremalExponent
    let B : ℝ := ((2^((phaseDepth m-m)/J+1):ℕ):ℝ)
    let Cfinal := (2:ℝ)^40*KY*B^2
    ∀v : ℕ,mu m*((2^v:ℕ):ℝ)/512 ≤ 1 → ∀z∈A,
      let rho := mu m*((2^v:ℕ):ℝ)/512
      ADBounds (points A (2^v) rho z) rho Cfinal s ∧
        ((atPoint A (2^v) z).card:ℝ) ≤ Cfinal*rho^(-s) := by
  intro eps C L U KXY KY A s B Cfinal v hfinal z hz
  have HH := source_prepared_window_profiles h original R HB E hE F1 F2 G Q1 Q2
    hF1 hG hQ2 hQ1 hGF heta2 hlambda hRich hcost1 hcost2 m ell hm hfL hJ Hqueries
    p population fullLower fullUpper hpopulation hfullLower hfullUpper hpop Hfull Hcolumns
    S T hS hT hTn P hP hell hell4 hd F Lip hLip0 hF hLip Qnew HT HC retain loss hretain hloss hret
    graphPlane Hgraph Fraw hFraw hpre Hread hField recordPopulation recordLower recordUpper
    recordLambda recordG Cpre threshold L3 Rel3 CX Hdata hdimension
  have hKY : 1 ≤ KY := quotientConstant_one_le _ _ _ _ _
  have hs0 : 0 ≤ s := by dsimp [s]; linarith only [hdimension]
  have hs2 : s ≤ 2 := by
    have he : (2:ℝ) ≤ ell := by exact_mod_cast hell2
    dsimp [s]
    linarith only [he,extremalExponent_nonneg]
  have hTI : T⊆incidences original :=
    (hT.trans hS).trans ((filter_subset _ _).trans (hE.trans (filter_subset _ _)))
  have Hheight : ∀w∈A,|w.1| ≤ 4*(NativeWindowQuotientTransport.factor m m:ℤ) := by
    intro w hw
    simp only [A,Finset.mem_image] at hw
    obtain ⟨x,hx,rfl⟩ := hw
    have hh := NativeWindowHeightSupport.translated_height_bound h original HB.1 HB.2.2.1
      m (by omega) p x (hTI hx)
    simpa only [NativeReferenceXYGridMaps.pxy,Nat.cast_mul,Nat.cast_ofNat] using hh
  exact NativeWindowAllDyadicAD.all_dyadic_windows A m (by omega) hJ (by omega) hKY hs0 hs2
    (fun i w hw => (HH i w hw).1) (fun i w hw => (HH i w hw).2) Hheight v hfinal z hz

end NativeSourceAllWindows
