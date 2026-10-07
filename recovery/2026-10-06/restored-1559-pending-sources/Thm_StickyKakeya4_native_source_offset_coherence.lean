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
namespace NativeSourceOffsetCoherence
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

lemma mesh_window (m s : ℕ) (hs : s ≤ m+6) : meshWidth m/512 ≤ 64/((2^s:ℕ):ℝ) := by
  have hp : ((2^s:ℕ):ℝ) ≤ ((2^(m+6):ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hs
  calc
    meshWidth m/512 ≤ 64/((2^(m+6):ℕ):ℝ) := by
      dsimp [meshWidth]
      rw [Nat.pow_add,Nat.cast_mul]
      norm_num
      have hx : (0:ℝ) < ((2^m:ℕ):ℝ) := by positivity
      field_simp
      norm_num
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) hp

/-- Actual finite offset coherence before the third core. The angular
bounds and point anchors are derived from the original reference and the
stored native tuple/chart data; no angular or affine residual certificate is
assumed. Selection retains whole original-point incidence fibers. -/
theorem exists_source_offset_coherence (Kcoh : ℕ) (c loss : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hloss : 0 < loss) (hloss1 : loss ≤ 1) :
    ∃Kupper : ℕ,∃seedCap deltaUpper : ℝ,0 < Kupper ∧ 0 < seedCap ∧ 0 < deltaUpper ∧ deltaUpper ≤ 1/8 ∧
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
    ∀depths : Fin Kcoh → ℕ,(∀u,6 ≤ depths u ∧ depths u ≤ m+6) →
    let error := (5/4:ℝ)*(64/((2^m:ℕ):ℝ))^(1-2*epsilon)
    let lower := fun u => (64/((2^(depths u):ℕ):ℝ))^(-extremalExponent)/
      ((2744*rowConstant*((g:ℝ)+1))*r^(-(9*rankLoss eta0 c rank)))
    let upper := fun u => meshAngularConstant*r^(-loss)*(64/((2^(depths u):ℕ):ℝ))^(-extremalExponent)
    ∃choice : Index → Fin n,∃xi : Index → EuclideanSpace ℝ (Fin (4-(rank.val+1))),
      (∀k∈S.image Prod.snd,(choice k,k)∈S ∧ ‖xi k‖ ≤ (5/2:ℝ)) ∧
      (∀z∈S,‖quotientMap P0 hP0 (rank.val+1) (by omega) (by omega) hd (f (rawHeight D m z.2))
        (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error) ∧
    ∃Pcoh⊆S.image Prod.snd,let Spre := NativeFinitePointCoherence.lift S Prod.snd Pcoh
      Spre.Nonempty ∧ Spre⊆S ∧ Saturated (parentEdges D ref.a (2^m) E2 p) Spre Prod.snd ∧
      S.card ≤ (∏u,⌈((4:ℝ)^(4-(rank.val+1))*upper u)/lower u⌉₊)*Spre.card ∧
      (∀u z w,z∈Spre → w∈Spre → physicalCell D ref.a (2^m) (2^(depths u)) p z.2=
          physicalCell D ref.a (2^m) (2^(depths u)) p w.2 →
        ‖xi z.2-xi w.2‖ ≤ 3*offsetMesh error metric (2^(depths u))) ∧
      (∀k∈Pcoh,Spre.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) := by
  obtain ⟨Kupper,seedCap,deltaUpper,hKupper,hSeed,hdUpper,hdUpper8,Hupper⟩ :=
    exists_paid_mesh_angular_bounds (c^3/8) loss (by positivity) hloss hloss1
  refine ⟨Kupper,seedCap,deltaUpper,hKupper,hSeed,hdUpper,hdUpper8,?_⟩
  intro n D eta zeta seed tau e eta0 c2 r q epsilon metric h htau L g Khalf
    heta hzeta hetaSeed hzseed hseedCap hsmallUpper ref Hcaller E2 S points h21 hE2n hSn
    rank hi hell he0 hcUnit hr hr1 hrdelta hmass htauHalf hTau hTauHistory hseed hc2 hg hgrid
    F2 G Q2 hG hGF H2 j hstop18 hstopCap hidentity hdelta hsmall m p HS HPoint hret
    he heHalf heSmall hcSmall hKhalf hq hq1 hqraw hsmallError hmetric S0 point tuple anchor hpoints Hsys
    oldPlane hOld hnear P0 hP0 hd hCell f hF hRead Hmetric depths hdepths error lower upper
  have hstop6 : 6 ≤ (ref.schedule j).val := by omega
  have hSE2 : S⊆E2 := HS.1.trans (filter_subset _ _)
  have hparent : ∀z∈S,parentLabel D ref.a (2^m) z.1=p := fun z hz => (mem_filter.mp (HS.1 hz)).2
  have hm : m=grainDepth (2*Khalf) (ref.schedule j).val (middleIndex Khalf) :=
    (grainDepth_middle Khalf (ref.schedule j).val hKhalf hstop6).symm
  obtain ⟨choice,xi,Hanchor⟩ := exists_actual_incident_affine_anchors h hr hr1 he heHalf he0.le heSmall hc hc1 hcSmall
    rank hell hrdelta htau.le g Khalf (ref.schedule j).val m hKhalf hstop6 hm hTauHistory hgrid hq hq1 hqraw
    hidentity hsmallError E2 S hSE2 S0 hpoints point tuple anchor Hsys oldPlane hOld hnear p hparent
    P0 hP0 hd hCell f hRead
  have hres : ∀z∈S,‖quotientMap P0 hP0 (rank.val+1) (by omega) (by omega) hd (f (rawHeight D m z.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error := by
    intro z hz
    have hh := (Hanchor z.2 (mem_image_of_mem Prod.snd hz)).2.2.2 z.1 hz
    simp only [NativeReferenceXYGridLinear.quotientMap,LinearMap.sub_apply,LinearMap.comp_apply,
      Matrix.toEuclideanLin,Matrix.toLpLin_apply]
    change ‖NativeIncidentAffineAnchorGeometry.normalCoordinates P0 hP0 (rank.val+1) _ _ hd (localHorizontalSlope D (2^m) p z.1)-
      matrixVector (f (rawHeight D m z.2)) (NativeGrainQuotientInjection.tangentCoordinates P0 (rank.val+1) hd
        (localHorizontalSlope D (2^m) p z.1))-xi z.2‖ ≤ error
    have hswap (u v w : EuclideanSpace ℝ (Fin (4-(rank.val+1)))) : u-v-w=u-w-v := by abel
    rw [hswap]
    exact hh
  have hRow := rowConstant_pos
  have hDen : 0 < (2744*rowConstant*((g:ℝ)+1))*r^(-(9*rankLoss eta0 c rank)) := by positivity
  have hlower : ∀u k,k∈S.image Prod.snd → lower u ≤
      (((S.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) (2^(depths u)) p z.1)).card:ℝ) := by
    intro u k hk
    have hh := actual_all_mesh_point_lower h htau L ref E2 S points h21 hE2n rank hi hell heta he0 hc hc1 hcUnit
      hr hr1 hrdelta hmass htauHalf hTau hTauHistory hseed hc2 hg hgrid F2 G Q2 hG hGF H2 j hstop18 hstopCap
      hidentity hsmall p HS HPoint hret (depths u) (hdepths u).1 (hdepths u).2 k hk
    exact (div_le_iff₀ hDen).mpr (by simpa only [pointMenu,mul_comm] using hh)
  have hupper : ∀u cell,((angularMenu D ref.a m (2^(depths u)) p S cell).card:ℝ) ≤ upper u := by
    intro u cell
    let Ecell := S.filter (fun z => physicalCell D ref.a (2^m) (2^(depths u)) p z.2=cell)
    have hCE : Ecell⊆S := filter_subset _ _
    have hMiddle := (middle_scale_bounds (ref.schedule j).val hstop6 r hidentity).2.2.2.1
    exact (Hupper n D eta zeta seed tau e h htau L g heta hzeta hetaSeed hzseed hseedCap hsmallUpper
      ref Hcaller j hstop6 (depths u) (hdepths u).1 (hdepths u).2 r (cutoff c rank) hr hrdelta
      (cutoff_bounds hc hc1 rank).2.2 hdelta hMiddle p Ecell (hCE.trans (hSE2.trans h21))
      (fun z hz => hparent z (hCE hz)) cell (fun _z hz => (mem_filter.mp hz).2)).1
  obtain ⟨Pcoh,hPcoh,hCoherent,hCost,hCompat,hFiber,_hLowerRet⟩ := select_fixed_offset_menu D ref.a m p S hSn hparent
    P0 hP0 (rank.val+1) (by omega) (by omega) hd f xi error metric 0 (by dsimp [error]; positivity) hmetric
    (fun u => 2^(depths u)) (fun _ => by positivity) (fun u => mesh_window m (depths u) (hdepths u).2)
    lower upper (fun _ => by dsimp [lower]; positivity) (fun k _ => hF (rawHeight D m k)) Hmetric hres hlower hupper
  refine ⟨choice,xi,(fun k hk => ⟨(Hanchor k hk).1,(Hanchor k hk).2.2.1⟩),hres,Pcoh,hPcoh,
    hCoherent,filter_subset _ _,?_,hCost,(fun u z w hz hw hcell => (hCompat u z w hz hw hcell).2),hFiber⟩
  exact saturated_filter _ _ Prod.snd HS (fun z => z.2∈Pcoh)
    (fun x _hx y _hy heq => by simp only [heq])

end NativeSourceOffsetCoherence
