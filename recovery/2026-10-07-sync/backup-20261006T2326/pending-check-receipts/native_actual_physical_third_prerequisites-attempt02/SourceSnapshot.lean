/- Actual physical/third prerequisites. Originally drafted without verification; consult current receipts. -/
import Theorems.Thm_StickyKakeya4_native_translated_height_freeze
import Theorems.Thm_StickyKakeya4_native_actual_configured_cell_selection
import Theorems.Thm_StickyKakeya4_native_actual_configured_residue
import Theorems.Thm_StickyKakeya4_native_physical_local_offset_coherence
import Theorems.Thm_StickyKakeya4_native_saturated_all_mesh_lower
import Theorems.Thm_StickyKakeya4_native_paid_mesh_angular_bounds
import Theorems.Thm_StickyKakeya4_native_incident_affine_anchor_source
import Theorems.Thm_StickyKakeya4_native_fixed_offset_coherence
import Theorems.Thm_StickyKakeya4_native_post_graph_XY_hook_data
import Theorems.Thm_StickyKakeya4_native_third_XY_source_data
import Theorems.Thm_StickyKakeya4_native_sharp_X_power_algebra
import Theorems.Thm_StickyKakeya4_native_actual_new_cut_budget

/- Preserved origin: Thm_StickyKakeya4_native_pre_third_height_support.lean; SHA256 315652d64ae43ab85c8a30ae103f5baf6d88ff222a3412ab514c7695aeb27c86. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
noncomputable section
namespace NativePreThirdHeightSupport
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeMatrixHeightWholePoint NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric
open NativeTranslatedHeightFreeze NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeNormalizedCellRelativeMenu CanonicalConfiguredE4Bridge
open scoped Matrix.Norms.Elementwise

/-- The support selector uses a cell eight times wider than the final
working cell. The precise dyadic nesting gives the required implication. -/
lemma configured_fine_to_support (delta : ℝ) (x y : E4)
    (h : wzDyadicCellIndex (delta/512) x=wzDyadicCellIndex (delta/512) y) :
    wzDyadicCellIndex (delta/64) x=wzDyadicCellIndex (delta/64) y := by
  ext j
  have hj : ⌊x j/(delta/512)⌋=⌊y j/(delta/512)⌋ := congrFun h j
  have hh:=NativeFrozenTimeField.same_base_same_coarse 8 hj
  have he : (delta/512)*(8:ℝ)=delta/64 := by ring
  simpa only [wzDyadicCellIndex,Nat.cast_ofNat,he] using hh

/-- The actual two remaining pre-third cuts. The fields are frozen from the
single-height source once, and then the certified original-coordinate support
selector acts on that same source. A final GLOBAL residue8 cut supplies
both point separation and height separation with its same color witness.
Both the original wider support-cell implication and its finer nested
version are retained on the same final U. The literal single-old-height
property is retained for every later subset as well. Every whole-point cost is explicit. -/
theorem select_actual_height_support {n K : ℕ} {V : Type*} [Zero V]
    {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m : ℕ) (hm : 6≤ m) (p : Parent)
    (S : Finset (Fin n × Index)) (hS : S.Nonempty)
    (hparent : ∀z∈S,parentLabel D a (2^m) z.1=p)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (G : ℤ → V) (hF : ∀t,‖F t‖≤ (1/4:ℝ))
    (R0 : ℕ) (hR0 : 0< R0) (hbase : rho m≤ mu m*(R0:ℝ))
    (M J : Fin K → ℕ) (hM : ∀j,0< M j)
    (hmenu : ∀j,mu m*(R0:ℝ)≤ 64/(M j:ℝ))
    (hIntegral : ∀j,64/(M j:ℝ)=(mu m*(R0:ℝ))*(J j:ℝ)) :
    ∃Bh⊆S.image Prod.snd,let Sh:=edgeLift S Prod.snd Bh
    let Fcfg:=frozen D a m R0 Sh F
    let Gcfg:=frozen D a m R0 Sh G
    (∀t,‖Fcfg t‖≤ (1/4:ℝ)) ∧
    ∃B0⊆Sh.image Prod.snd,let U0:=edgeLift Sh Prod.snd B0
    ∃color : Fin 4 → Fin 8,∃B⊆U0.image Prod.snd,let U:=edgeLift U0 Prod.snd B
      U.Nonempty ∧ U⊆S ∧ S.card≤ (((8*R0)*53^(4*K))*8^4)*U.card ∧
      (∀k∈B,U.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀z∈U,Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=F (translatedHeight D a m z.2) ∧
        Gcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=G (translatedHeight D a m z.2)) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀j x y,
        ⌊NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 x (3:Fin 4)/((64/(M j:ℝ))/512)⌋=
        ⌊NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 y (3:Fin 4)/((64/(M j:ℝ))/512)⌋ →
        physicalCell D a (2^m) (M j) p x (3:Fin 4)=physicalCell D a (2^m) (M j) p y (3:Fin 4)) ∧
      (∀k∈B,SeparatedAlignmentPatches.color 8 (by norm_num)
        (NativeActualConfiguredResidue.parameter s (mu m) R0 F Fcfg
          (NativeActualConfiguredPoint.sourceLabel D a m p s P hP hd F k))=color) ∧
      (∀x∈U.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
        ∀y∈U.image (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2),
        x≠y → (mu m*(R0:ℝ))/64≤ dist x y) ∧
      (∀z∈U,∀u∈U,
        NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2 (3:Fin 4)≠
          NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 u.2 (3:Fin 4) →
        (mu m*(R0:ℝ))/64≤ dist
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 z.2 (3:Fin 4))
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 u.2 (3:Fin 4))) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀T⊆U,∀z∈T,∀w∈T,
        translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
        translatedHeight D a m z.2=translatedHeight D a m w.2) := by
  obtain ⟨Bh,hBh,hSh,hShS,hHeightCost,hHeightFiber,hHeight,hFrozen⟩:=
    select_and_freeze D a m S hS F G R0 hR0
  let Sh:=edgeLift S Prod.snd Bh
  let Fcfg:=frozen D a m R0 Sh F
  have hCfg (t : ℤ) : ‖Fcfg t‖≤ (1/4:ℝ) := by
    exact NativeFrozenTimeField.field_norm_le Sh
      (fun z => referenceHeight m (translatedHeight D a m z.2))
      (fun z => F (translatedHeight D a m z.2)) (mu m*(R0:ℝ)) (1/4:ℝ)
      (by norm_num) (fun z _ => hF (translatedHeight D a m z.2)) t
  obtain ⟨B0,hB0,hU0Sh,hSupportCost,hSupportFiber,hSupport⟩:=
    NativeActualConfiguredCellSelection.select_actual_edges h m hm p Sh
      (fun z hz => hparent z (hShS hz)) s P hP hd F Fcfg hF hCfg R0 hR0 hbase K M hM hmenu
  let U0:=edgeLift Sh Prod.snd B0
  have hU0 : U0.Nonempty := by
    by_contra hn
    have hz : U0.card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
    change Sh.card≤ 53^(4*K)*U0.card at hSupportCost
    rw [hz,mul_zero] at hSupportCost
    have hp : 0 < Sh.card := card_pos.mpr hSh
    exact (not_lt_of_ge hSupportCost) hp
  have hBhPoint (k : Index) (hk : k∈Sh.image Prod.snd) : k∈Bh := by
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hk
    exact (mem_filter.mp hz).2
  obtain ⟨color,B,hB,hUU0,hResidueCost,hResidueFiber,hColor,hSep,hTimeSep⟩:=
    NativeActualConfiguredResidue.select_actual_edges D a m p U0 s P hP hd F Fcfg R0 hR0
  let U:=edgeLift U0 Prod.snd B
  have hU : U.Nonempty := by
    by_contra hn
    have hz : U.card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
    change U0.card≤ 8^4*U.card at hResidueCost
    rw [hz,mul_zero] at hResidueCost
    have hp:=card_pos.mpr hU0
    omega
  have hUSh : U⊆Sh := hUU0.trans hU0Sh
  have hBPoint (k : Index) (hk : k∈B) : k∈B0 := by
    obtain ⟨z,hz,rfl⟩:=mem_image.mp (hB hk)
    exact (mem_filter.mp hz).2
  refine ⟨Bh,hBh,hCfg,B0,hB0,color,B,hB,hU,hUSh.trans hShS,?_,?_,?_,?_,?_,hColor,hSep,hTimeSep,?_,?_⟩
  · calc
      S.card≤ (8*R0)*Sh.card := hHeightCost
      _≤ (8*R0)*(53^(4*K)*U0.card) := Nat.mul_le_mul_left _ hSupportCost
      _=((8*R0)*53^(4*K))*U0.card := by ring
      _≤ ((8*R0)*53^(4*K))*(8^4*U.card) := Nat.mul_le_mul_left _ hResidueCost
      _=(((8*R0)*53^(4*K))*8^4)*U.card := by ring
  · intro k hk
    exact (hResidueFiber k hk).trans ((hSupportFiber k (hBPoint k hk)).trans
      (hHeightFiber k (hBhPoint k (hB0 (hBPoint k hk)))))
  · intro z hz
    exact hFrozen U hUSh z hz
  · intro j x hx y hy hcell
    exact hSupport j x (hUU0 hx) y (hUU0 hy) (configured_fine_to_support (64/(M j:ℝ)) _ _ hcell)
  · intro j x y htime
    have hs : 512*((64/(M j:ℝ))/512)=(mu m*(R0:ℝ))*(J j:ℝ) := by
      calc
        _=64/(M j:ℝ) := by ring
        _=(mu m*(R0:ℝ))*(J j:ℝ) := hIntegral j
    rw [NativeActualConfiguredPoint.point_height_floor D a m p s P hP hd F Fcfg R0 hR0 x _ (J j) hs,
      NativeActualConfiguredPoint.point_height_floor D a m p s P hP hd F Fcfg R0 hR0 y _ (J j) hs] at htime
    have he : 512*((64/(M j:ℝ))/512)=64/(M j:ℝ) := by ring
    rw [he] at htime
    exact htime
  · intro j x hx y hy hcell
    exact hSupport j x (hUU0 hx) y (hUU0 hy) hcell
  · intro T hTU z hz w hw he
    exact hHeight z (hUSh (hTU hz)) w (hUSh (hTU hw)) he

end NativePreThirdHeightSupport
end -- original anonymous section NativePreThirdHeightSupport

/- Preserved origin: Thm_StickyKakeya4_native_source_physical_coherence.lean; SHA256 7a9d01220d636c09c7462eb1f7d0f0670848ee851d5b506999bdb3b3800d5813. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativeSourcePhysicalCoherence
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

open NativePhysicalLocalOffsetCoherence NativeMatrixHeightWholePoint
def HasUpperEngine (Kupper : ℕ) (amin loss seedCap deltaUpper : ℝ) : Prop :=
      ∀(n : ℕ) (D : FiniteScaleSource n) (eta zeta seed tau e : ℝ)
        (h : IsWangZakharovNativeFiniteInput D eta) (htau : 0< tau) (L g : ℕ),
        0≤ eta → 0≤ zeta → eta≤ seed/8 → zeta≤ seed/256 →
        seed≤ seedCap → D.thickness≤ deltaUpper →
      ∀ref : Reference h tau htau seed e zeta L g,
        HasCallerUniformities ref (factory g Kupper) →
      ∀i : Fin (g+1),6≤ (ref.schedule i).val →
      let m := middleDepth (ref.schedule i).val
      ∀s : ℕ,6≤ s → s≤ m+6 →
      ∀r power : ℝ,0< r → r≤ D.thickness^power → amin≤ power →
        64*D.thickness≤ r^2 → 3072*r≤ ((64:ℝ)/((2^m:ℕ):ℝ))^2 →
      ∀(p : Parent) (E : Finset (Fin n × Index)),E⊆ ref.E1 →
        (∀z∈E,parentLabel D ref.a (2^m) z.1=p) →
      ∀cell : Index,
        (∀z∈E,physicalCell D ref.a (2^m) (2^s) p z.2=cell) →
        (((E.image (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
          meshAngularConstant*r^(-loss)*(64/((2^s:ℕ):ℝ))^(-extremalExponent)) ∧
        ∀t : ℕ,6≤ t → t≤ s → ∀center : EuclideanSpace ℝ (Fin 3),
          (((ballEdges D (2^m) p E center (64/((2^t:ℕ):ℝ))).image
            (fun z => angularCell D (2^m) (2^s) p z.1)).card:ℝ)≤
          meshAngularConstant*r^(-loss)*
            ((64/((2^t:ℕ):ℝ))/(64/((2^s:ℕ):ℝ)))^extremalExponent

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

/-- Actual native source bounds and affine anchors are derived internally
from the prescribed Reference and its single upper engine. The SAME original
physical/angular labels are retained. Matrix selection is performed first;
the offset count is then rerun with local variation rho before the third core. -/
def HasPhysicalCoherenceEngine (Kcoh Kupper : ℕ) (c loss seedCap deltaUpper : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) : Prop :=
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
    ∀(P0 : Submodule ℝ E4) (hP0 : P0≤ heightKernel) (hd : Module.finrank ℝ P0=(rank.val+1)-1),
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
    let R := modulus (2*metric)
    (∀j,error ≤ 64/((2^(depths j):ℕ):ℝ)) →
    ∃choice : Index → Fin n,∃xi : Index → EuclideanSpace ℝ (Fin (4-(rank.val+1))),
      (∀k∈S.image Prod.snd,(choice k,k)∈S ∧ ‖xi k‖ ≤ (5/2:ℝ)) ∧
      (∀z∈S,‖quotientMap P0 hP0 (rank.val+1) (by omega) (by omega) hd (f (rawHeight D m z.2))
        (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error) ∧
    ∃B⊆S.image Prod.snd,let T := NativeFinitePointCoherence.lift S Prod.snd B
      T.Nonempty ∧ T⊆S ∧ Saturated (parentEdges D ref.a (2^m) E2 p) T Prod.snd ∧
      S.card ≤ (R^(2*Kcoh)*(∏j,⌈((4:ℝ)^(4-(rank.val+1))*upper j)/lower j⌉₊))*T.card ∧
      (∀j z u,z∈T → u∈T → physicalCell D ref.a (2^m) (2^(depths j)) p z.2=
          physicalCell D ref.a (2^m) (2^(depths j)) p u.2 →
        ‖f (rawHeight D m z.2)-f (rawHeight D m u.2)‖ < 64/((2^(depths j):ℕ):ℝ) ∧
        ‖xi z.2-xi u.2‖ ≤ (129/4:ℝ)*(64/((2^(depths j):ℕ):ℝ))) ∧
      (∀k∈B,T.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀j k,k∈B → lower j ≤ (((T.filter (fun z => z.2=k)).image
        (fun z => angularCell D (2^m) (2^(depths j)) p z.1)).card:ℝ)) ∧
      (∀j z u,z∈T → u∈T → physicalCell D ref.a (2^m) (2^(depths j)) p z.2 (3:Fin 4)=
          physicalCell D ref.a (2^m) (2^(depths j)) p u.2 (3:Fin 4) →
        ‖f (rawHeight D m z.2)-f (rawHeight D m u.2)‖ < 64/((2^(depths j):ℕ):ℝ))


theorem coherence_of_actual_upper (Kcoh Kupper : ℕ) (c loss seedCap deltaUpper : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (Hupper : HasUpperEngine Kupper (c^3/8) loss seedCap deltaUpper) :
    HasPhysicalCoherenceEngine Kcoh Kupper c loss seedCap deltaUpper hc hc1 := by
  intro n D eta zeta seed tau e eta0 c2 r q epsilon metric h htau L g Khalf
    heta hzeta hetaSeed hzseed hseedCap hsmallUpper ref Hcaller E2 S points h21 hE2n hSn
    rank hi hell he0 hcUnit hr hr1 hrdelta hmass htauHalf hTau hTauHistory hseed hc2 hg hgrid
    F2 G Q2 hG hGF H2 j hstop18 hstopCap hidentity hdelta hsmall m p HS HPoint hret
    he heHalf heSmall hcSmall hKhalf hq hq1 hqraw hsmallError hmetric S0 point tuple anchor hpoints Hsys
    oldPlane hOld hnear P0 hP0 hd hCell f hF hRead Hmetric depths hdepths error lower upper R hErrorWindow
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
  obtain ⟨B,hB,hT,hTS,hCost,hCoherent,hFiber,hLowerT,hHeight⟩ := select_actual_matrix_offset_menu
    D ref.a m p S hSn hparent P0 hP0 (rank.val+1) (by omega) (by omega) (by omega) hd
    f xi error metric 0 (by dsimp [error]; positivity) hmetric
    (fun j => 2^(depths j)) (fun _ => by positivity)
    (fun j => mesh_window m (depths j) (hdepths j).2) hErrorWindow
    lower upper (fun _ => by dsimp [lower]; positivity)
    (fun k _ => hF (rawHeight D m k)) Hmetric hres hlower hupper
  refine ⟨choice,xi,(fun k hk => ⟨(Hanchor k hk).1,(Hanchor k hk).2.2.1⟩),hres,
    B,hB,hT,hTS,?_,hCost,hCoherent,hFiber,hLowerT,hHeight⟩
  exact saturated_filter _ _ Prod.snd HS (fun z => z.2∈B)
    (fun x _hx y _hy heq => by simp only [heq])

end NativeSourcePhysicalCoherence
end -- original anonymous section NativeSourcePhysicalCoherence

/- Preserved origin: Thm_StickyKakeya4_native_physical_coherent_third_join.lean; SHA256 7cb1f1fe8f658332f0f359d6c43470eaede3d5215aa73016ffb1de36732f045f. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
noncomputable section
namespace NativePhysicalCoherentThirdJoin
open NativeGrainHeightProjectionSource NativeTranslatedGrainHeightMetric
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
open NativeSourcePhysicalCoherence NativePostGraphXYHookData NativeThirdXYSourceData
open NativeOriginalParentSelection NativeWeightedGrainQuotientGeometry
open NativeTranslatedGrainHeightSelection NativeSquaredGrainQueries NativeAnisotropicSliceLabels
open NativeSharpXPowerAlgebra NativeRetainedSliceCore NativeReferenceXYGridField
open NativeRetainedSliceBudgetAlgebra NativeWeightedGrainQuotientSource NativeGrainQuotientFibers
/-- The actual pre-third source is refined by a matrix palette and then a
fresh local-variation offset choice, preserving the original angular labels.
The paid-subset continuation leaves room for the actual single-height and
configured-support cuts before the existing hook makes the unique third core.
The pairwise matrix/offset and height-only matrix fields are retained on
Spre itself, so later fixed point/cell representatives may be chosen before T.
All of these choices are charged in Ctotal; no earlier third core is constructed.
This theorem does not itself construct those later cuts or identify configured
cells with the original physical cells. -/
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
    ∀(P0 : Submodule ℝ E4) (hP0 : P0≤ heightKernel) (hd : Module.finrank ℝ P0=(rank.val+1)-1),
      (∀k∈S.image Prod.snd,cell P0=cell (horizontalPlane D tuple (spatialLabel D (2^m) k))) →
    ∀f : ℤ → Matrix (Fin (4-(rank.val+1))) (Fin ((rank.val+1)-1)) ℝ,
      (∀height,‖f height‖ ≤ (1/4:ℝ)) →
      (∀k∈S.image Prod.snd,f (rawHeight D m k)=
        nodeSlope P0 hP0 (rank.val+1) (by omega) (by omega) hd
          (horizontalPlane D tuple (spatialLabel D (2^m) k)) (horizontalPlane_le D tuple _)) →
      (∀z∈S,∀w∈S,‖f (rawHeight D m z.2)-f (rawHeight D m w.2)‖ ≤
        metric*|chartHeightCoordinate m 0 (rawHeight D m z.2)-chartHeightCoordinate m 0 (rawHeight D m w.2)|) →
    ∀(Jhorizontal d3 L3 : ℕ) (population PL PU retain Cgraph t : ℝ),
      (∀Rel3 : Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop,
      (∀j x,Rel3 j x x) → (∀j x y,Rel3 j x y → Rel3 j y x) →
      HasThirdXYFinish (J:=Jhorizontal) D eta zeta ref.a q tau (seed/8) c2
        (r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1)))
        ((WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)/(E2.card:ℝ))
        (factor ref.dimension (g+1) L) G Q2 m tuple E2 S P0 hP0 (by omega) (by omega) hd f p
        population PL PU retain Cgraph t metric L3 Rel3) →
    ∀depths : Fin Kcoh → ℕ,(∀u,6 ≤ depths u ∧ depths u ≤ m+6) →
    (∀j,(5/4:ℝ)*(64/((2^m:ℕ):ℝ))^(1-2*epsilon) ≤ 64/((2^(depths j):ℕ):ℝ)) →
    let plane := nodePlane D tuple
    let Sq := NativeWeightedGrainQuotientGeometry.retained D ref.a m (rank.val+1) plane S
      P0 hP0 (by omega) (by omega) hd (physicalMesh m (phaseDepth m)/8)
    let Sfull := second D ref.a m (rank.val+1) plane Sq
    let Gcoh := (NativeMatrixHeightWholePoint.modulus (2*metric))^(2*Kcoh)*
      ∏j,⌈((4:ℝ)^(4-(rank.val+1))*(meshAngularConstant*r^(-loss)*
        (64/((2^(depths j):ℕ):ℝ))^(-extremalExponent)))/
        ((64/((2^(depths j):ℕ):ℝ))^(-extremalExponent)/
          ((2744*rowConstant*((g:ℝ)+1))*r^(-(9*rankLoss eta0 c rank))))⌉₊
    let Cpre := quotientCost q*(Gcoh:ℝ)
    ∃choice : Index → Fin n,∃xi : Index → EuclideanSpace ℝ (Fin (4-(rank.val+1))),
      (∀k∈Sfull.image Prod.snd,(choice k,k)∈Sfull ∧ ‖xi k‖ ≤ (5/2:ℝ)) ∧
      (∀z∈Sfull,‖quotientMap P0 hP0 (rank.val+1) (by omega) (by omega) hd (f (rawHeight D m z.2))
        (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ (5/4:ℝ)*(64/((2^m:ℕ):ℝ))^(1-2*epsilon)) ∧
    ∃Pcoh⊆Sfull.image Prod.snd,let Spre := NativeFinitePointCoherence.lift Sfull Prod.snd Pcoh
      Spre.Nonempty ∧ Spre⊆Sfull ∧ Saturated (parentEdges D ref.a (2^m) E2 p) Spre Prod.snd ∧
      Sfull.card ≤ Gcoh*Spre.card ∧ 0 < Cpre ∧ (S.card:ℝ) ≤ Cpre*Spre.card ∧
      (∀k∈Pcoh,Spre.filter (fun z => z.2=k)=Sfull.filter (fun z => z.2=k)) ∧
      (∀u z w,z∈Spre → w∈Spre → physicalCell D ref.a (2^m) (2^(depths u)) p z.2=
          physicalCell D ref.a (2^m) (2^(depths u)) p w.2 →
        ‖f (rawHeight D m z.2)-f (rawHeight D m w.2)‖ < 64/((2^(depths u):ℕ):ℝ) ∧
        ‖xi z.2-xi w.2‖ ≤ (129/4:ℝ)*(64/((2^(depths u):ℕ):ℝ))) ∧
      (∀u z w,z∈Spre → w∈Spre → physicalCell D ref.a (2^m) (2^(depths u)) p z.2 (3:Fin 4)=
          physicalCell D ref.a (2^m) (2^(depths u)) p w.2 (3:Fin 4) →
        ‖f (rawHeight D m z.2)-f (rawHeight D m w.2)‖ < 64/((2^(depths u):ℕ):ℝ)) ∧
      ∀Snext : Finset (Fin n × Index),Snext⊆Spre →
      ∀Cextra : ℝ,0 < Cextra → (Spre.card:ℝ) ≤ Cextra*Snext.card →
      ∀Rel3 : Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop,
      (∀j x,Rel3 j x x) → (∀j x y,Rel3 j x y → Rel3 j y x) →
      let Ctotal := Cpre*Cextra
      let Q3 := NativeSourceSizeBounds.radix Snext.card L3
      let F3 := refinementCost (d3+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau (seed/8) c2
        (r^(rankLoss eta0 c rank)/(4*((g:ℝ)+1)))
        ((WeightedRichDirectionalLayers.mass points (pointWeight E2):ℝ)/(E2.card:ℝ))
        (factor ref.dimension (g+1) L) G Q2 F3 Q3 q (rank.val+1)
      ∃T,HasThirdXYSourceData (J:=Jhorizontal) D zeta ref.a m plane E2 S Snext T P0 hP0
        (by omega) (by omega) hd f p population PL PU Q2 retain Cgraph Ctotal t L3 Rel3 CX ∧
      (∀u z w,z∈T → w∈T → physicalCell D ref.a (2^m) (2^(depths u)) p z.2=
          physicalCell D ref.a (2^m) (2^(depths u)) p w.2 →
        ‖f (rawHeight D m z.2)-f (rawHeight D m w.2)‖ < 64/((2^(depths u):ℕ):ℝ) ∧
        ‖xi z.2-xi w.2‖ ≤ (129/4:ℝ)*(64/((2^(depths u):ℕ):ℝ))) ∧
      (∀u z w,z∈T → w∈T → physicalCell D ref.a (2^m) (2^(depths u)) p z.2 (3:Fin 4)=
          physicalCell D ref.a (2^m) (2^(depths u)) p w.2 (3:Fin 4) →
        ‖f (rawHeight D m z.2)-f (rawHeight D m w.2)‖ < 64/((2^(depths u):ℕ):ℝ)) ∧
      (let field := fixedField D ref.a m (rank.val+1) plane Sq f
       ∀v∈T.image (fun z => translatedHeight D ref.a m z.2),∀w∈T.image (fun z => translatedHeight D ref.a m z.2),
        ‖field v-field w‖ ≤ (3*metric)*|referenceHeight m v-referenceHeight m w|) := by
  intro n D eta zeta seed tau e eta0 c2 r q epsilon metric h htau L g Khalf
    heta hzeta hetaSeed hzseed hseedCap hsmallUpper ref Hcaller E2 S points h21 hE2n hSn
    rank hi hell he0 hcUnit hr hr1 hrdelta hmass htauHalf hTau hTauHistory hseed hc2 hg hgrid
    F2 G Q2 hG hGF H2 j hstop18 hstopCap hidentity hdelta hsmall m p HS HPoint hret
    he heHalf heSmall hcSmall hKhalf hq hq1 hqraw hsmallError hmetric S0 point tuple anchor hpoints Hsys
    oldPlane hOld hnear P0 hP0 hd hCell f hF hRead Hmetric Jhorizontal d3 L3 population PL PU retain Cgraph t
    HfinishAll depths hdepths hErrorWindow plane Sq Sfull Gcoh Cpre
  have Hfinish := HfinishAll (fun _ _ _ => True) (fun _ _ => True.intro) (fun _ _ _ _ => True.intro)
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
  have Hcoh := coherence_of_actual_upper Kcoh Kupper c loss seedCap deltaUpper hc hc1 Hupper
  obtain ⟨choice,xi,hchoice,hres,Pcoh,hPcoh,hSpreN,hSpreFull,hSpreSat,hcost,hcoh,hfiber,_hLowerRet,hheight⟩ :=
    Hcoh n D eta zeta seed tau e eta0 c2 r q epsilon metric h htau L g Khalf
      heta hzeta hetaSeed hzseed hseedCap hsmallUpper ref Hcaller E2 Sfull points h21 hE2n hfullN
      rank hi hell he0 hcUnit hr hr1 hrdelta hmass htauHalf hTau hTauHistory hseed hc2 hg hgrid
      F2 G Q2 hG hGF H2 j hstop18 hstopCap hidentity hdelta hsmall p hSat HPoint hret
      he heHalf heSmall hcSmall hKhalf hq hq1 hqraw hsmallError hmetric S0 point tuple anchor
      (fun z hz => hpoints z (hfullS hz)) Hsys oldPlane hOld hnear P0 hP0 hd
      (fun k hk => hCell k (image_subset_image hfullS hk)) f hF
      (fun k hk => hRead k (image_subset_image hfullS hk))
      (fun z hz w hw => Hmetric z (hfullS hz) w (hfullS hw)) depths hdepths hErrorWindow
  let Spre := NativeFinitePointCoherence.lift Sfull Prod.snd Pcoh
  change Sfull.card ≤ Gcoh*Spre.card at hcost
  have hGpos : 0 < Gcoh := by
    have hpos := card_pos.mpr hfullN
    by_contra hh
    have hz : Gcoh=0 := by omega
    rw [hz,zero_mul] at hcost
    omega
  have hCq : 0 < quotientCost q := quotientCost_pos hq
  have hCpre : 0 < Cpre := by dsimp [Cpre]; positivity
  have hPreRet : (S.card:ℝ) ≤ Cpre*Spre.card := by
    have hh : (Sfull.card:ℝ) ≤ (Gcoh:ℝ)*Spre.card := by exact_mod_cast hcost
    calc
      (S.card:ℝ) ≤ quotientCost q*Sfull.card := Hfinish.1
      _ ≤ quotientCost q*((Gcoh:ℝ)*Spre.card) := mul_le_mul_of_nonneg_left hh hCq.le
      _ = Cpre*Spre.card := by dsimp [Cpre]; ring
  refine ⟨choice,xi,hchoice,hres,Pcoh,hPcoh,hSpreN,hSpreFull,hSpreSat,hcost,hCpre,hPreRet,hfiber,hcoh,hheight,?_⟩
  intro Snext hNext Cextra hExtra hExtraRet Rel3 hExtraRefl hExtraSymm Ctotal Q3 F3 CX
  have hNextFull : Snext⊆Sfull := hNext.trans hSpreFull
  have hTotal : 0 < Ctotal := mul_pos hCpre hExtra
  have hTotalRet : (S.card:ℝ) ≤ Ctotal*Snext.card := by
    calc
      (S.card:ℝ) ≤ Cpre*Spre.card := hPreRet
      _ ≤ Cpre*(Cextra*Snext.card) := mul_le_mul_of_nonneg_left hExtraRet hCpre.le
      _ = Ctotal*Snext.card := by dsimp [Ctotal]; ring
  obtain ⟨T,HT,hfield⟩ := (HfinishAll Rel3 hExtraRefl hExtraSymm).2
    Snext hNextFull Ctotal hTotal hTotalRet
  refine ⟨T,HT,?_,?_,hfield⟩
  · intro u z w hz hw hcell
    exact hcoh u z w (hNext (HT.1.1 hz)) (hNext (HT.1.1 hw)) hcell
  · intro u z w hz hw hcell
    exact hheight u z w (hNext (HT.1.1 hz)) (hNext (HT.1.1 hw)) hcell

end NativePhysicalCoherentThirdJoin
end -- original anonymous section NativePhysicalCoherentThirdJoin

/- Preserved origin: Thm_StickyKakeya4_native_actual_height_third_join.lean; SHA256 4ec261813772e43f6f84ce06a62536888ab72ce7dfd0455d9e5a34e2a2045d3f. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeActualHeightThirdJoin
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeMatrixHeightWholePoint NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric
open NativeTranslatedHeightFreeze NativeReferenceXYGridPoints NativeHorizontalGrainSlice
open NativeNormalizedCellRelativeMenu CanonicalConfiguredE4Bridge NativePreThirdHeightSupport
open NativeThirdXYSourceData NativeSharpXPowerAlgebra NativeRetainedSliceCore
open NativeReferenceXYGridField NativeSpatialAngularGeometry NativeSquaredGrainQueries
open NativeGrainQuotientFibers NativeRetainedSliceBudgetAlgebra NativeOriginalCellChartGeometry
open scoped Matrix.Norms.Elementwise

/-- Exact cost readback for the actual continuation. The old quotient
charge occurs once; the new coherence, height, support and residue cuts
are precisely the natural charge paid by source_new_cut_cost. -/
lemma source_total_charge (q : ℝ) (Kcoh Ksupport normal g R0 : ℕ)
    (meshConstant row r loss rankLoss metric kappa : ℝ) (mesh : Fin Kcoh → ℝ) :
    (quotientCost q *
      (NativeActualNewCutBudget.coherenceCharge Kcoh normal g meshConstant row r loss rankLoss metric kappa mesh : ℝ)) *
      ((((8*R0)*53^(4*Ksupport))*8^4:ℕ):ℝ) =
    quotientCost q *
      (NativeActualNewCutBudget.newCutCharge Kcoh Ksupport normal g R0
        meshConstant row r loss rankLoss metric kappa mesh : ℝ) := by
  simp only [NativeActualNewCutBudget.newCutCharge, Nat.cast_mul]
  ring

/-- The rank-2 branch calls the actual height, support and residue cuts,
then the source continuation exactly once on their common U. The relation
values may depend on that U and its frozen fields; their count d3 is an
input fixed before the source. The original fixedField and raw field are
read back on the same final T. No point saturation of T is asserted. -/
theorem attach_rank_two {n K Jhorizontal d3 : ℕ} {V : Type*} [Zero V]
    {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a zeta : ℝ) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (plane : Index → Submodule ℝ E4)
    (E2 Hgraph S : Finset (Fin n × Index)) (hS : S.Nonempty)
    (hparent : ∀z∈S, parentLabel D a (2^m) z.1 = p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 1)
    (hFull : S ⊆ NativeTranslatedGrainHeightSelection.second D a m 2 plane
      (NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
        (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 4) hd (physicalMesh m (phaseDepth m)/8)))
    (Fraw : ℤ → Matrix (Fin 2) (Fin 1) ℝ) (hFraw : ∀t, ‖Fraw t‖ ≤ (1/4:ℝ))
    (q tau c1 c2 lambda b population PL PU retain Cgraph Cpre t : ℝ)
    (F1 G Q2 L3 : ℕ)
    (Hnext : ∀U⊆S, ∀Cextra : ℝ, 0 < Cextra → (S.card:ℝ) ≤ Cextra*U.card →
      ∀Rel : Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop,
      (∀j x, Rel j x x) → (∀j x y, Rel j x y → Rel j y x) →
      let Ctotal := Cpre*Cextra
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost (d3+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau c1 c2
        lambda b F1 G Q2 F3 Q3 q 2
      ∃T, HasThirdXYSourceData (J:=Jhorizontal) D zeta a m plane E2 Hgraph U T P hP
        (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 4) hd Fraw p
        population PL PU Q2 retain Cgraph Ctotal t L3 Rel CX)
    (Gfield : ℤ → V) (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (M J : Fin K → ℕ) (hM : ∀j, 0 < M j)
    (hmenu : ∀j, mu m*(R0:ℝ) ≤ 64/(M j:ℝ))
    (hIntegral : ∀j, 64/(M j:ℝ) = (mu m*(R0:ℝ))*(J j:ℝ))
    (relations : Finset (Fin n × Index) → (ℤ → Matrix (Fin 2) (Fin 1) ℝ) →
      (ℤ → V) → Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop)
    (hRefl : ∀U Fcfg Gcfg j x, relations U Fcfg Gcfg j x x)
    (hSymm : ∀U Fcfg Gcfg j x y, relations U Fcfg Gcfg j x y → relations U Fcfg Gcfg j y x) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 2 plane Hgraph P hP
        (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 4) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 2 plane Sq Fraw
    ∃Bh⊆S.image Prod.snd,let Sh:=edgeLift S Prod.snd Bh
    let Fcfg:=frozen D a m R0 Sh F
    let Gcfg:=frozen D a m R0 Sh Gfield
    (∀t,‖Fcfg t‖≤ (1/4:ℝ)) ∧
    ∃B0⊆Sh.image Prod.snd,let U0:=edgeLift Sh Prod.snd B0
    ∃color : Fin 4 → Fin 8,∃B⊆U0.image Prod.snd,let U:=edgeLift U0 Prod.snd B
      U.Nonempty ∧ U⊆S ∧ S.card≤ (((8*R0)*53^(4*K))*8^4)*U.card ∧
      (∀k∈B,U.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀z∈U,Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=F (translatedHeight D a m z.2) ∧
        Gcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=Gfield (translatedHeight D a m z.2)) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀j x y,
        ⌊NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 x (3:Fin 4)/((64/(M j:ℝ))/512)⌋=
        ⌊NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 y (3:Fin 4)/((64/(M j:ℝ))/512)⌋ →
        physicalCell D a (2^m) (M j) p x (3:Fin 4)=physicalCell D a (2^m) (M j) p y (3:Fin 4)) ∧
      (∀k∈B,SeparatedAlignmentPatches.color 8 (by norm_num)
        (NativeActualConfiguredResidue.parameter .oneTwo (mu m) R0 F Fcfg
          (NativeActualConfiguredPoint.sourceLabel D a m p .oneTwo P hP hd F k))=color) ∧
      (∀x∈U.image (fun z => NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 z.2),
        ∀y∈U.image (fun z => NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 z.2),
        x≠y → (mu m*(R0:ℝ))/64≤ dist x y) ∧
      (∀z∈U,∀u∈U,
        NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 z.2 (3:Fin 4)≠
          NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 u.2 (3:Fin 4) →
        (mu m*(R0:ℝ))/64≤ dist
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 z.2 (3:Fin 4))
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 u.2 (3:Fin 4))) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p .oneTwo P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀T⊆U,∀z∈T,∀w∈T,
        translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
        translatedHeight D a m z.2=translatedHeight D a m w.2) ∧
      (∀z∈U, Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2)) ∧
      let Cextra : ℝ := ((((8*R0)*53^(4*K))*8^4:ℕ):ℝ)
      let Ctotal := Cpre*Cextra
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost (d3+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau c1 c2
        lambda b F1 G Q2 F3 Q3 q 2
      ∃T, HasThirdXYSourceData (J:=Jhorizontal) D zeta a m plane E2 Hgraph U T P hP
        (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 4) hd Fraw p
        population PL PU Q2 retain Cgraph Ctotal t L3 (relations U Fcfg Gcfg) CX ∧
      T ⊆ U ∧
      (∀z∈T, Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2) ∧
        Gcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Gfield (translatedHeight D a m z.2)) ∧
      (∀z∈T, ∀w∈T,
        translatedHeight D a m z.2/((8*R0:ℕ):ℤ) = translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
        translatedHeight D a m z.2 = translatedHeight D a m w.2) := by
  intro Sq F
  have hF : ∀height, ‖F height‖ ≤ (1/4:ℝ) := fixedField_norm D a m 2 plane Sq Fraw hFraw
  obtain ⟨Bh, hBh, hCfg, B0, hB0, color, B, hB, hU, hUS, hCost, hFiber,
      hFrozen, hFine, hTime, hColor, hSep, hTimeSep, hWide, hSingle⟩ :=
    select_actual_height_support h m hm p S hS hparent .oneTwo P hP hd F Gfield hF
      R0 hR0 hbase M J hM hmenu hIntegral
  let Sh := edgeLift S Prod.snd Bh
  let Fcfg := frozen D a m R0 Sh F
  let Gcfg := frozen D a m R0 Sh Gfield
  let U0 := edgeLift Sh Prod.snd B0
  let U := edgeLift U0 Prod.snd B
  have hRaw (z : Fin n × Index) (hz : z ∈ U) :
      Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2) :=
    (hFrozen z hz).1.trans (fixedField_readback D a m 2 plane Sq Fraw z (hFull (hUS hz)))
  let Cextra : ℝ := ((((8*R0)*53^(4*K))*8^4:ℕ):ℝ)
  have hExtra : 0 < Cextra := by dsimp [Cextra]; positivity
  have hExtraCost : (S.card:ℝ) ≤ Cextra*U.card := by
    dsimp only [Cextra,U,U0,Sh]
    exact_mod_cast hCost
  obtain ⟨T, HT⟩ := Hnext U hUS Cextra hExtra hExtraCost
    (relations U Fcfg Gcfg) (hRefl U Fcfg Gcfg) (hSymm U Fcfg Gcfg)
  have hTU : T ⊆ U := HT.1.1
  refine ⟨Bh, hBh, hCfg, B0, hB0, color, B, hB, hU, hUS, hCost, hFiber,
    hFrozen, hFine, hTime, hColor, hSep, hTimeSep, hWide, hSingle, hRaw, T, HT, hTU, ?_, ?_⟩
  · intro z hz
    exact ⟨hRaw z (hTU hz), (hFrozen z (hTU hz)).2⟩
  · exact hSingle T hTU

/-- The rank-3 branch calls the actual height, support and residue cuts,
then the source continuation exactly once on their common U. The relation
values may depend on that U and its frozen fields; their count d3 is an
input fixed before the source. The original fixedField and raw field are
read back on the same final T. No point saturation of T is asserted. -/
theorem attach_rank_three {n K Jhorizontal d3 : ℕ} {V : Type*} [Zero V]
    {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (a zeta : ℝ) (m : ℕ) (hm : 6 ≤ m) (p : Parent)
    (plane : Index → Submodule ℝ E4)
    (E2 Hgraph S : Finset (Fin n × Index)) (hS : S.Nonempty)
    (hparent : ∀z∈S, parentLabel D a (2^m) z.1 = p)
    (P : Submodule ℝ E4) (hP : P ≤ heightKernel) (hd : Module.finrank ℝ P = 2)
    (hFull : S ⊆ NativeTranslatedGrainHeightSelection.second D a m 3 plane
      (NativeWeightedGrainQuotientGeometry.retained D a m 3 plane Hgraph P hP
        (by norm_num : 1 ≤ 3) (by norm_num : 3 ≤ 4) hd (physicalMesh m (phaseDepth m)/8)))
    (Fraw : ℤ → Matrix (Fin 1) (Fin 2) ℝ) (hFraw : ∀t, ‖Fraw t‖ ≤ (1/4:ℝ))
    (q tau c1 c2 lambda b population PL PU retain Cgraph Cpre t : ℝ)
    (F1 G Q2 L3 : ℕ)
    (Hnext : ∀U⊆S, ∀Cextra : ℝ, 0 < Cextra → (S.card:ℝ) ≤ Cextra*U.card →
      ∀Rel : Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop,
      (∀j x, Rel j x x) → (∀j x y, Rel j x y → Rel j y x) →
      let Ctotal := Cpre*Cextra
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost (d3+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau c1 c2
        lambda b F1 G Q2 F3 Q3 q 3
      ∃T, HasThirdXYSourceData (J:=Jhorizontal) D zeta a m plane E2 Hgraph U T P hP
        (by norm_num : 1 ≤ 3) (by norm_num : 3 ≤ 4) hd Fraw p
        population PL PU Q2 retain Cgraph Ctotal t L3 Rel CX)
    (Gfield : ℤ → V) (R0 : ℕ) (hR0 : 0 < R0) (hbase : rho m ≤ mu m*(R0:ℝ))
    (M J : Fin K → ℕ) (hM : ∀j, 0 < M j)
    (hmenu : ∀j, mu m*(R0:ℝ) ≤ 64/(M j:ℝ))
    (hIntegral : ∀j, 64/(M j:ℝ) = (mu m*(R0:ℝ))*(J j:ℝ))
    (relations : Finset (Fin n × Index) → (ℤ → Matrix (Fin 1) (Fin 2) ℝ) →
      (ℤ → V) → Fin d3 → (Fin n × Index) → (Fin n × Index) → Prop)
    (hRefl : ∀U Fcfg Gcfg j x, relations U Fcfg Gcfg j x x)
    (hSymm : ∀U Fcfg Gcfg j x y, relations U Fcfg Gcfg j x y → relations U Fcfg Gcfg j y x) :
    let Sq := NativeWeightedGrainQuotientGeometry.retained D a m 3 plane Hgraph P hP
        (by norm_num : 1 ≤ 3) (by norm_num : 3 ≤ 4) hd (physicalMesh m (phaseDepth m)/8)
    let F := fixedField D a m 3 plane Sq Fraw
    ∃Bh⊆S.image Prod.snd,let Sh:=edgeLift S Prod.snd Bh
    let Fcfg:=frozen D a m R0 Sh F
    let Gcfg:=frozen D a m R0 Sh Gfield
    (∀t,‖Fcfg t‖≤ (1/4:ℝ)) ∧
    ∃B0⊆Sh.image Prod.snd,let U0:=edgeLift Sh Prod.snd B0
    ∃color : Fin 4 → Fin 8,∃B⊆U0.image Prod.snd,let U:=edgeLift U0 Prod.snd B
      U.Nonempty ∧ U⊆S ∧ S.card≤ (((8*R0)*53^(4*K))*8^4)*U.card ∧
      (∀k∈B,U.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀z∈U,Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=F (translatedHeight D a m z.2) ∧
        Gcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ))=Gfield (translatedHeight D a m z.2)) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/512)
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀j x y,
        ⌊NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 x (3:Fin 4)/((64/(M j:ℝ))/512)⌋=
        ⌊NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 y (3:Fin 4)/((64/(M j:ℝ))/512)⌋ →
        physicalCell D a (2^m) (M j) p x (3:Fin 4)=physicalCell D a (2^m) (M j) p y (3:Fin 4)) ∧
      (∀k∈B,SeparatedAlignmentPatches.color 8 (by norm_num)
        (NativeActualConfiguredResidue.parameter .twoOne (mu m) R0 F Fcfg
          (NativeActualConfiguredPoint.sourceLabel D a m p .twoOne P hP hd F k))=color) ∧
      (∀x∈U.image (fun z => NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 z.2),
        ∀y∈U.image (fun z => NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 z.2),
        x≠y → (mu m*(R0:ℝ))/64≤ dist x y) ∧
      (∀z∈U,∀u∈U,
        NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 z.2 (3:Fin 4)≠
          NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 u.2 (3:Fin 4) →
        (mu m*(R0:ℝ))/64≤ dist
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 z.2 (3:Fin 4))
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 u.2 (3:Fin 4))) ∧
      (∀j,∀x∈U,∀y∈U,
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 x.2)=
        wzDyadicCellIndex ((64/(M j:ℝ))/64)
          (NativeActualConfiguredPoint.point D a m p .twoOne P hP hd F Fcfg R0 y.2) →
        physicalCell D a (2^m) (M j) p x.2=physicalCell D a (2^m) (M j) p y.2) ∧
      (∀T⊆U,∀z∈T,∀w∈T,
        translatedHeight D a m z.2/((8*R0:ℕ):ℤ)=translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
        translatedHeight D a m z.2=translatedHeight D a m w.2) ∧
      (∀z∈U, Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2)) ∧
      let Cextra : ℝ := ((((8*R0)*53^(4*K))*8^4:ℕ):ℝ)
      let Ctotal := Cpre*Cextra
      let Q3 := NativeSourceSizeBounds.radix U.card L3
      let F3 := refinementCost (d3+2) (Jhorizontal+1) L3
      let CX := (Ctotal/quotientCost q)*fiberCoefficient D.thickness eta zeta tau c1 c2
        lambda b F1 G Q2 F3 Q3 q 3
      ∃T, HasThirdXYSourceData (J:=Jhorizontal) D zeta a m plane E2 Hgraph U T P hP
        (by norm_num : 1 ≤ 3) (by norm_num : 3 ≤ 4) hd Fraw p
        population PL PU Q2 retain Cgraph Ctotal t L3 (relations U Fcfg Gcfg) CX ∧
      T ⊆ U ∧
      (∀z∈T, Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2) ∧
        Gcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Gfield (translatedHeight D a m z.2)) ∧
      (∀z∈T, ∀w∈T,
        translatedHeight D a m z.2/((8*R0:ℕ):ℤ) = translatedHeight D a m w.2/((8*R0:ℕ):ℤ) →
        translatedHeight D a m z.2 = translatedHeight D a m w.2) := by
  intro Sq F
  have hF : ∀height, ‖F height‖ ≤ (1/4:ℝ) := fixedField_norm D a m 3 plane Sq Fraw hFraw
  obtain ⟨Bh, hBh, hCfg, B0, hB0, color, B, hB, hU, hUS, hCost, hFiber,
      hFrozen, hFine, hTime, hColor, hSep, hTimeSep, hWide, hSingle⟩ :=
    select_actual_height_support h m hm p S hS hparent .twoOne P hP hd F Gfield hF
      R0 hR0 hbase M J hM hmenu hIntegral
  let Sh := edgeLift S Prod.snd Bh
  let Fcfg := frozen D a m R0 Sh F
  let Gcfg := frozen D a m R0 Sh Gfield
  let U0 := edgeLift Sh Prod.snd B0
  let U := edgeLift U0 Prod.snd B
  have hRaw (z : Fin n × Index) (hz : z ∈ U) :
      Fcfg (translatedHeight D a m z.2/((8*R0:ℕ):ℤ)) = Fraw (rawHeight D m z.2) :=
    (hFrozen z hz).1.trans (fixedField_readback D a m 3 plane Sq Fraw z (hFull (hUS hz)))
  let Cextra : ℝ := ((((8*R0)*53^(4*K))*8^4:ℕ):ℝ)
  have hExtra : 0 < Cextra := by dsimp [Cextra]; positivity
  have hExtraCost : (S.card:ℝ) ≤ Cextra*U.card := by
    dsimp only [Cextra,U,U0,Sh]
    exact_mod_cast hCost
  obtain ⟨T, HT⟩ := Hnext U hUS Cextra hExtra hExtraCost
    (relations U Fcfg Gcfg) (hRefl U Fcfg Gcfg) (hSymm U Fcfg Gcfg)
  have hTU : T ⊆ U := HT.1.1
  refine ⟨Bh, hBh, hCfg, B0, hB0, color, B, hB, hU, hUS, hCost, hFiber,
    hFrozen, hFine, hTime, hColor, hSep, hTimeSep, hWide, hSingle, hRaw, T, HT, hTU, ?_, ?_⟩
  · intro z hz
    exact ⟨hRaw z (hTU hz), (hFrozen z (hTU hz)).2⟩
  · exact hSingle T hTU

end NativeActualHeightThirdJoin
end -- original anonymous section NativeActualHeightThirdJoin
