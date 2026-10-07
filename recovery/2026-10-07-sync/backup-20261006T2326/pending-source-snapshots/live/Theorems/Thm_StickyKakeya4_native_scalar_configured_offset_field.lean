import Theorems.Thm_StickyKakeya4_native_actual_configured_offset_field
import Theorems.Thm_StickyKakeya4_native_original_phase_window_population

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
noncomputable section
namespace NativeScalarConfiguredOffsetField
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeHorizontalGrainSlice CanonicalConfiguredE4Bridge NativeNormalizedCellRelativeMenu
open NativeMergedPointOffsets NativeConfiguredOffsetField NativeActualConfiguredOffsetField
open OriginalPhaseWindowGraph OriginalWCoreDynamics OriginalWWitnessCounts OriginalWCoarseEscapeMenus
open OriginalWGrainDrift OriginalPhaseGridPopulation NativeOriginalPhaseWindowGraph

/-- The actual two normal coordinates use the product norm in the scalar
phase consumer. Its norm is bounded by the source Euclidean norm. -/
def normalPair (v : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ := (v 0,v 1)

lemma normalPair_sub_le (v w : EuclideanSpace ℝ (Fin 2)) :
    ‖normalPair v-normalPair w‖≤‖v-w‖ := by
  change max ‖v 0-w 0‖ ‖v 1-w 1‖≤‖v-w‖
  exact max_le
    (by simpa only [PiLp.sub_apply] using PiLp.norm_apply_le (v-w) (0:Fin 2))
    (by simpa only [PiLp.sub_apply] using PiLp.norm_apply_le (v-w) (1:Fin 2))

/-- Changing the coordinate representation retains the identical U-witness
used by the shared pointOffset, including its zero extension. -/
lemma normalPair_pointOffset {Omega : Type*} (U : Finset Omega) (point : Omega → E4)
    (xi : Omega → EuclideanSpace ℝ (Fin 2)) (p : E4) :
    normalPair (pointOffset U point xi p)=
      pointOffset U point (fun w => normalPair (xi w)) p := by
  unfold pointOffset
  split_ifs <;> rfl

/-- Only the order of the four literal coordinate labels changes. -/
def indexOfCell (c : ℤ × (ℤ × (ℤ × ℤ))) : Index :=
  ![c.2.1,c.2.2.1,c.2.2.2,c.1]

lemma physicalCell_readback (Delta : ℝ) (p : E4) :
    indexOfCell (OriginalPhaseCellPopulation.physicalCell Delta
      (fun x : E4 => x 3) (fun x : E4 => x 0) (fun x : E4 => (x 1,x 2)) p)=
      wzDyadicCellIndex Delta p := by
  ext j
  fin_cases j <;> rfl

/-- The phase caller's field is the coarse representative field on the
same pre-third U, expressed in its height-first physical cell convention. -/
def scalarField {Omega : Type*} (U : Finset Omega) (point : Omega → E4)
    (xi : Omega → ℝ × ℝ) (Delta : ℝ) (c : ℤ × (ℤ × (ℤ × ℤ))) : ℝ × ℝ :=
  cellField U point xi Delta (indexOfCell c)

lemma graph_point_mem {Omega Tube : Type*} [DecidableEq Tube]
    (T : Finset Omega) (point : Omega → E4) (tube : Omega → Tube)
    (p : E4) (hp : p∈TwoTubePathCollisionCount.points (T.image (fun z => (point z,tube z)))) :
    p∈T.image point := by
  obtain ⟨v,hv,hvp⟩:=mem_image.mp hp
  obtain ⟨z,hz,hzv⟩:=mem_image.mp hv
  exact mem_image.mpr ⟨z,hz,(congrArg Prod.fst hzv).trans hvp⟩

/-- The actual configured graph supplies the formerly separate common-field
input to the enlarged phase population theorem. Its point offset and cell
field use U throughout, and its counted points are the deduplicated image of
the same later T. No old edge count is substituted for a geometric count. -/
theorem enlarged_phase_population {n : ℕ} {Tube : Type*} [DecidableEq Tube]
    (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (S U T : Finset (Fin n × Index)) (hUS : U⊆S) (hTU : T⊆U)
    (split : Split) (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (hd : Module.finrank ℝ P=tangentDim split)
    (Fold Fcfg : ℤ → Matrix (Fin (normalDim split)) (Fin (tangentDim split)) ℝ)
    (R0 M : ℕ) (hM : 0<M) (xi : Index → ℝ × ℝ) (tube : (Fin n × Index) → Tube)
    (hcoh : ∀v∈S, ∀w∈S,
      physicalCell D a (2^m) M p v.2=physicalCell D a (2^m) M p w.2 →
        ‖xi v.2-xi w.2‖≤(129/4:ℝ)*(64/(M:ℝ)))
    (hread : ∀v∈U, ∀w∈U,
      wzDyadicCellIndex ((64/(M:ℝ))/64)
        (NativeActualConfiguredPoint.point D a m p split P hP hd Fold Fcfg R0 v.2)=
      wzDyadicCellIndex ((64/(M:ℝ))/64)
        (NativeActualConfiguredPoint.point D a m p split P hP hd Fold Fcfg R0 w.2) →
      physicalCell D a (2^m) M p v.2=physicalCell D a (2^m) M p w.2) :
    let point:=fun v : Fin n × Index =>
      NativeActualConfiguredPoint.point D a m p split P hP hd Fold Fcfg R0 v.2
    let I:=T.image (fun v => (point v,tube v))
    let height:=fun x : E4 => x 3
    let x:=fun x : E4 => x 0
    let y:=fun x : E4 => (x 1,x 2)
    let offset:=pointOffset U point (fun v => xi v.2)
    let Delta:=(64/(M:ℝ))/64
    ∀F : ℝ → ℝ →L[ℝ] ℝ × ℝ,
    ∀SCore : Finset (ℝ × Tube), ∀hSV : SCore⊆vertices I height,
    ∀z x0 : ℝ, ∀xi0 : ℝ × ℝ, ∀k : GrainLabel,
    ∀r tau width A mesh Rball : ℝ,
    0<r → 0<tau → 0<width → 0≤A → r≤Delta →
    4*width+A*r≤Delta → ‖F z‖≤A → 0<mesh → 0≤Rball →
    ∀center : OriginalPhaseGridPopulation.Point,
    (((expanded (heightSlice SCore z)
      (fun s => grainCell width (grainCoordinate height x y F (rep I height SCore hSV s)))
      (fun s => phaseLabel r tau x0 xi0 x offset (rep I height SCore hSV s)) k).filter
      (fun v => ‖gridPoint mesh v-center‖≤Rball)).card:ℝ)≤
      (27*(2*(2064:ℝ)*Delta/tau+2)^2)*(2*Rball/mesh+2) := by
  intro point I height x y offset Delta F SCore hSV z x0 xi0 k r tau width A mesh Rball
    hr ht hw hA hrD hphysical hF hm hR center
  obtain ⟨hDelta,hfields⟩:=from_actual_coherence D a m p S U hUS split P hP hd
    Fold Fcfg R0 M hM xi hcoh hread
  have hfield : ∀v∈TwoTubePathCollisionCount.points I,
      ‖offset v-scalarField U point (fun w => xi w.2) Delta
        (OriginalPhaseCellPopulation.physicalCell Delta height x y v)‖≤2064*Delta := by
    intro v hv
    have hh:=hfields T hTU v (graph_point_mem T point tube v hv)
    simpa only [scalarField,physicalCell_readback] using hh
  exact NativeOriginalPhaseWindowPopulation.original_enlarged_phase_ball_population
    I height x y offset F (scalarField U point (fun v => xi v.2) Delta)
    SCore hSV z x0 xi0 k hr ht hDelta hw hA (by norm_num : (0:ℝ)≤2064)
    hrD hphysical hF hfield hm hR center

end NativeScalarConfiguredOffsetField
