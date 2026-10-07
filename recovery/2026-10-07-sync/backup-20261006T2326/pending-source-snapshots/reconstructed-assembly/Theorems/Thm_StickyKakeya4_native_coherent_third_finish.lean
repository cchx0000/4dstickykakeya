import Theorems.Thm_StickyKakeya4_native_source_coherence_engine
import Theorems.Thm_StickyKakeya4_native_source_coherence_cost
import Theorems.Thm_StickyKakeya4_native_post_graph_XY_hook_data
/- RECONSTRUCTED 2026-10-06. UNVERIFIED.
The historical attempt was running at the last observed Oct 5 checkpoint.
This consumes an already chosen engine and makes no second menu choice. -/
import Theorems.Thm_StickyKakeya4_native_source_offset_coherence
import Theorems.Thm_StickyKakeya4_native_saturated_all_mesh_lower
import Theorems.Thm_StickyKakeya4_native_paid_mesh_angular_bounds
import Theorems.Thm_StickyKakeya4_native_incident_affine_anchor_source
import Theorems.Thm_StickyKakeya4_native_fixed_offset_coherence
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
set_option diagnostics true
noncomputable section
namespace NativeCoherentThirdFinish
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeGenericReferenceData NativeExtraQueriedRankConfiguration
open NativePaidMeshAngularBounds NativePaidMeshAngularUpper NativeConditionalReferenceMenu
open NativeSaturatedAllMeshLower NativeOriginalPointSaturation NativeJointUniformCoarseRelations
open NativeFixedCompactKakeyaExponent NativeRankExponentHierarchy NativeActualMesoscopicRankConfiguration
open NativeMiddleGrainParentBudget NativeHeightMetricMenu NativeTranslatedGrainHeightOverlap
open NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu NativeFixedOffsetCoherence
open NativeIncidentAffineAnchorSource NativeIncidentAffineAnchorGeometry NativeGrainQuotientInjection
open NativeReferenceXYGridLinear NativeHorizontalGraphCoordinates NativeHeightSlopeCoordinates
open NativeHorizontalGrainSlice NativeProjectorCellChart
open NativeActualHeightSlopeVariation NativeCompatibleNodeDirections NativeSpatialAngularGeometry
open NativeOriginalPointAngularLower NativeQueriedVertexWeights NativeActivePhasePopulation
open NativeDirectionRankDichotomy NativeRetainedQueryMenu NativeSmallLossParentBudget
open scoped BigOperators Matrix.Norms.Elementwise
open NativeSourceCoherenceEngine NativePostGraphXYHookData NativeThirdXYSourceData
open NativeOriginalParentSelection NativeWeightedGrainQuotientGeometry
open NativeTranslatedGrainHeightSelection NativeSquaredGrainQueries NativeAnisotropicSliceLabels
open NativeSharpXPowerAlgebra NativeRetainedSliceCore NativeReferenceXYGridField
/-- RECONSTRUCTED UNVERIFIED DRAFT. This file was written but not submitted
for a source check before the Oct 5 interruption.
The actual quotient and height source is made coherent by whole original
points, then the stored hook makes exactly one third core. The same-cell
conclusion and its literal ceiling-product loss are retained on that core. -/
theorem from_actual_source (Kcoh Kupper : ℕ) (c loss seedCap deltaUpper : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (Hupper : HasUpperEngine Kupper (c^3/8) loss seedCap deltaUpper) :
    ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed tau e eta0 c2 r q epsilon metric : ℝ)
      (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0 < tau) (L g Khalf : ℕ),
      0 ≤ eta → 0 ≤ zeta → eta ≤ seed/8 → zeta ≤ seed/256 → seed ≤ seedCap → D.thickness ≤ deltaUpper →
    ∀ref : Reference h tau htau seed e zeta L g,HasCallerUniformities ref (factory g Kupper) →
    ∀(E2 S : Finset (Fin n × Index)) (points : Finset Index),E2⊆ref.E1 → E2.Nonempty → S.Nonempty →
    ∀rank : Fin 4,1 ≤ rank.val → rank.val+1 ≤ 3 →
      0 < eta0 → c ≤ 1/(eta0+1) → 0 < r → r ≤ 1 → r ≤ D.thickness^(cutoff c rank) →
      r^((2*((rank.val+1:ℕ):ℝ)+1)*rankLoss eta0 c rank)*(E2.card:ℝ) ≤
        (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ) →
      tau ≤ 1/2 → tau ≤ commonBudget eta0 c/1024 →
      tau ≤ commonBudget eta0 c/(1000*(((2*Khalf:ℕ):ℝ)+1)) →
      seed ≤ tau/16384 → c2=commonBudget eta0 c/4 → 0 < g → 1/(g:ℝ) < rankWindow tau/4 →
    ∀F2 G Q2 : ℕ,0 < G → G ≤ F2 →
      (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*D.thickness^(-eta) ≤ D.thickness^(-c2) →
    ∀j : Fin (g+1),18 ≤ (ref.schedule j).val → (ref.schedule j).val ≤ ref.level/4 →
      48*((2^(ref.schedule j).val:ℕ):ℝ)*r=1 → 64*D.thickness ≤ r^2 →
      D.thickness ≤ NativeHistoryDimensionRange.extraCutoff c hc hc1 g →
    let m := middleDepth (ref.schedule j).val
    ∀p : Parent,Saturated (parentEdges D ref.a (2^m) E2 p) S Prod.snd →
      HasUniformFibers (parentEdges D ref.a (2^m) E2 p) Q2 Prod.snd →
      (let lambda := r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1))
       let W : ℝ := (WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)
       let mu := (lambda*W/(2*(factor ref.dimension (g+1) L:ℝ)*G*(E2.card:ℝ)))*D.thickness^eta
       (mu/rowConstant)*(parentEdges D ref.a (2^m) ref.E1 p).card ≤ (parentEdges D ref.a (2^m) E2 p).card) →
      0 < epsilon → epsilon ≤ 1/2 → eta0 ≤ epsilon → c ≤ epsilon/24 → 0 < Khalf →
      0 < q → q ≤ 1 → r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q →
      D.thickness^(cutoff c rank*epsilon/2) ≤ 1/errorConstant → 0 ≤ metric →
    ∀(S0 : Finset Index) (point : Index → Index)
      (tuple : Index → Fin (rank.val+1) → (Fin n × Index))
      (anchor : Index → Fin (rank.val+1) → Fin n),
      (∀z∈S,z.2∈S0) → IsNodeDirectionSystem D ref.a m E2 S0 q (rank.val+1) point tuple anchor →
    ∀oldPlane : Index → Submodule ℝ E4,(∀k∈S0,Module.finrank ℝ (oldPlane k)=rank.val+1) →
      (∀z∈E2,Metric.infDist (slopeVector D z.1) (oldPlane z.2:Set E4) ≤ r) →
    ∀(P0 : Submodule ℝ E4) (hP0 : P0≤heightKernel) (hd : Module.finrank ℝ P0=(rank.val+1)-1),
      (∀k∈S.image Prod.snd,cell P0=cell (horizontalPlane D tuple (spatialLabel D (2^m) k))) →
    ∀f : ℤ → Matrix (Fin (4-(rank.val+1))) (Fin ((rank.val+1)-1)) ℝ,
      (∀height,‖f height‖ ≤ (1/4:ℝ)) →
      (∀k∈S.image Prod.snd,f (rawHeight D m k)=
        nodeSlope P0 hP0 (rank.val+1) (by omega) (by omega) hd
          (horizontalPlane D tuple (spatialLabel D (2^m) k)) (horizontalPlane_le D tuple _)) →
      (∀z∈S,∀w∈S,‖f (rawHeight D m z.2)-f (rawHeight D m w.2)‖ ≤
        metric*|chartHeightCoordinate m 0 (rawHeight D m z.2)-chartHeightCoordinate m 0 (rawHeight D m w.2)|) →
    ∀(Jhorizontal d3 L3 : ℕ) (population PL PU retain Cgraph t : ℝ)
      (Rel3 : Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop),
      HasThirdXYFinish (J:=Jhorizontal) D eta zeta ref.a q tau (seed/8) c2
        (r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1)))
        ((WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)/(E2.card:ℝ))
        (factor ref.dimension (g+1) L) G Q2 m tuple E2 S P0 hP0 (by omega) (by omega) hd f p
        population PL PU retain Cgraph t metric L3 Rel3 →
    ∀depths : Fin Kcoh → ℕ,(∀u,6 ≤ depths u ∧ depths u ≤ m+6) →
    let plane := nodePlane D tuple
    let Sq := NativeWeightedGrainQuotientGeometry.retained D ref.a m (rank.val+1) plane S
      P0 hP0 (by omega) (by omega) hd (physicalMesh m (phaseDepth m)/8)
    let Sfull := second D ref.a m (rank.val+1) plane Sq
    let Gcoh := NativeSourceCoherenceCost.cost g (rank.val+1) r loss (rankLoss eta0 c rank) depths
    let Cpre := quotientCost q*(Gcoh:ℝ)
    ∃choice : Index → Fin n,∃xi : Index → EuclideanSpace ℝ (Fin (4-(rank.val+1))),
      (∀k∈Sfull.image Prod.snd,(choice k,k)∈Sfull ∧ ‖xi k‖ ≤ (5/2:ℝ)) ∧
      (∀z∈Sfull,‖quotientMap P0 hP0 (rank.val+1) (by omega) (by omega) hd (f (rawHeight D m z.2))
        (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ (5/4:ℝ)*(64/((2^m:ℕ):ℝ))^(1-2*epsilon)) ∧
    ∃Pcoh⊆Sfull.image Prod.snd,let Spre := NativeFinitePointCoherence.lift Sfull Prod.snd Pcoh
      Spre.Nonempty ∧ Spre⊆Sfull ∧ Saturated (parentEdges D ref.a (2^m) E2 p) Spre Prod.snd ∧
      Sfull.card ≤ Gcoh*Spre.card ∧ 0 < Cpre ∧ (S.card:ℝ) ≤ Cpre*Spre.card ∧
      (∀k∈Pcoh,Spre.filter (fun z => z.2=k)=Sfull.filter (fun z => z.2=k)) ∧
      let Q3 := NativeSourceSizeBounds.radix Spre.card L3
      let F3 := refinementCost (d3+2) (Jhorizontal+1) L3
      let CX := (Cpre/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2
        (r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1)))
        ((WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)/(E2.card:ℝ))
        (factor ref.dimension (g+1) L) G Q2 F3 Q3 q (rank.val+1)
      ∃T,HasThirdXYSourceData (J:=Jhorizontal) D zeta ref.a m plane E2 S Spre T P0 hP0
        (by omega) (by omega) hd f p population PL PU Q2 retain Cgraph Cpre t L3 Rel3 CX ∧
      (∀u z w,z∈T → w∈T → physicalCell D ref.a (2^m) (2^(depths u)) p z.2=
          physicalCell D ref.a (2^m) (2^(depths u)) p w.2 →
        ‖xi z.2-xi w.2‖ ≤ 3*offsetMesh ((5/4:ℝ)*(64/((2^m:ℕ):ℝ))^(1-2*epsilon)) metric (2^(depths u))) ∧
      (let field := fixedField D ref.a m (rank.val+1) plane Sq f
       ∀v∈T.image (fun z => translatedHeight D ref.a m z.2),∀w∈T.image (fun z => translatedHeight D ref.a m z.2),
        ‖field v-field w‖ ≤ (3*metric)*|referenceHeight m v-referenceHeight m w|) := by
  intro n D eta zeta seed tau e eta0 c2 r q epsilon metric h htau L g Khalf
    heta hzeta hetaSeed hzseed hseedCap hsmallUpper ref Hcaller E2 S points h21 hE2n hSn
    rank hi hell he0 hcUnit hr hr1 hrdelta hmass htauHalf hTau hTauHistory hseed hc2 hg hgrid
    F2 G Q2 hG hGF H2 j hstop18 hstopCap hidentity hdelta hsmall m p HS HPoint hret
    he heHalf heSmall hcSmall hKhalf hq hq1 hqraw hsmallError hmetric S0 point tuple anchor hpoints Hsys
    oldPlane hOld hnear P0 hP0 hd hCell f hF hRead Hmetric Jhorizontal d3 L3 population PL PU retain Cgraph t
    Rel3 Hfinish depths hdepths plane Sq Sfull Gcoh Cpre
  have hSE : ∀z∈parentEdges D ref.a (2^m) E2 p,parentLabel D ref.a (2^m) z.1=p :=
    fun _ hz => (mem_filter.mp hz).2
  have hSqSat := quotient_saturation D ref.a m (rank.val+1) plane p _ S hSE HS
    P0 hP0 (by omega) (by omega) hd (physicalMesh m (phaseDepth m)/8)
  have hSat : Saturated (parentEdges D ref.a (2^m) E2 p) Sfull Prod.snd :=
    translated_heights_saturation D ref.a m (rank.val+1) plane p _ Sq hSE hSqSat
  have hSqS : Sq⊆S := NativeWeightedGrainQuotientSelection.selected_subset _ _ _ _
  have hfullS : Sfull⊆S := (second_subset D ref.a m (rank.val+1) plane Sq).trans hSqS
  have hfullN : Sfull.Nonempty := by
    by_contra hh
    have hzero : Sfull.card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hh)
    have hpos : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hSn
    have hcost := Hfinish.1
    change (S.card:ℝ) ≤ quotientCost q*Sfull.card at hcost
    rw [hzero,Nat.cast_zero,mul_zero] at hcost
    exact (not_lt_of_ge hcost) hpos
  have Hcoh := coherence_of_upper Kcoh Kupper c loss seedCap deltaUpper hc hc1 Hupper
  obtain ⟨choice,xi,hchoice,hres,Pcoh,hPcoh,hSpreN,hSpreFull,hSpreSat,hcost,hcoh,hfiber⟩ :=
    Hcoh n D eta zeta seed tau e eta0 c2 r q epsilon metric h htau L g Khalf
      heta hzeta hetaSeed hzseed hseedCap hsmallUpper ref Hcaller E2 Sfull points h21 hE2n hfullN
      rank hi hell he0 hcUnit hr hr1 hrdelta hmass htauHalf hTau hTauHistory hseed hc2 hg hgrid
      F2 G Q2 hG hGF H2 j hstop18 hstopCap hidentity hdelta hsmall p hSat HPoint hret
      he heHalf heSmall hcSmall hKhalf hq hq1 hqraw hsmallError hmetric S0 point tuple anchor
      (fun z hz => hpoints z (hfullS hz)) Hsys oldPlane hOld hnear P0 hP0 hd
      (fun k hk => hCell k (image_subset_image hfullS hk)) f hF
      (fun k hk => hRead k (image_subset_image hfullS hk))
      (fun z hz w hw => Hmetric z (hfullS hz) w (hfullS hw)) depths hdepths
  let Spre := NativeFinitePointCoherence.lift Sfull Prod.snd Pcoh
  change Sfull.card ≤ Gcoh*Spre.card at hcost
  have hGpos : 0 < Gcoh := by
    have hpos := card_pos.mpr hfullN
    by_contra hh
    have hz : Gcoh=0 := by omega
    rw [hz,zero_mul] at hcost
    omega
  have hCq : 0 < quotientCost q := by
    unfold quotientCost
    have hcap : 0 < quotientCap q := by unfold quotientCap; positivity
    have hh : 0 < ⌈quotientCap q⌉₊ := Nat.ceil_pos.mpr hcap
    positivity
  have hCpre : 0 < Cpre := by dsimp [Cpre]; positivity
  have hPreRet : (S.card:ℝ) ≤ Cpre*Spre.card := by
    have hh : (Sfull.card:ℝ) ≤ (Gcoh:ℝ)*Spre.card := by exact_mod_cast hcost
    calc
      (S.card:ℝ) ≤ quotientCost q*Sfull.card := Hfinish.1
      _ ≤ quotientCost q*((Gcoh:ℝ)*Spre.card) := mul_le_mul_of_nonneg_left hh hCq.le
      _ = Cpre*Spre.card := by dsimp [Cpre]; ring
  obtain ⟨T,HT,hfield⟩ := Hfinish.2 Spre hSpreFull Cpre hCpre hPreRet
  refine ⟨choice,xi,hchoice,hres,Pcoh,hPcoh,hSpreN,hSpreFull,hSpreSat,hcost,hCpre,hPreRet,hfiber,T,HT,?_,hfield⟩
  intro u z w hz hw hcell
  exact hcoh u z w (HT.1.1 hz) (HT.1.1 hw) hcell

end NativeCoherentThirdFinish
