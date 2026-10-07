import Theorems.Thm_StickyKakeya4_native_original_packet_reference
import Theorems.Thm_StickyKakeya4_native_nodal_reference_lift
import Theorems.Thm_StickyKakeya4_native_rank_one_slope_cap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000

noncomputable section
namespace NativeTaggedPacketRows
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeOriginalParentSelection NativeCubicalIncidenceCounts NativeSpatialAngularGeometry
open NativeDirectionRankDichotomy NativeShortRowPackets NativeSquaredGrainQueries
open NativeOriginalPacketReference NativeQuantizedLinePackets NativeNodalPacketOverlap NativeNodalReferenceLift

/-- The reference universe uses actual original spatial nodes and complete
old point fibers. Its definition does not depend on the chosen directions. -/
def reference {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (E : Finset (Fin n × Index))
    (S : Finset Index) : Finset (Index × Index) :=
  boxReference (S.image (spatialLabel D (2^m))) (64/((2^m:ℕ):ℝ))
    (E.image Prod.snd) (rawVertex D (phaseDepth m))

/-- The finite packet keeps its node tag in every predecessor comparison. -/
def packetSet {n : ℕ} (D : FiniteScaleSource n) (m : ℕ) (E : Finset (Fin n × Index))
    (S : Finset Index) (directionIndex : Index → Fin n) (c : Index × (Index × ℤ)) :
    Finset (Index × Index) :=
  (reference D m E S).filter (taggedPacket (fun n => slopeVector D (directionIndex n))
    (64/((2^(phaseDepth m):ℕ):ℝ)) (64/((2^m:ℕ):ℝ)) (rawVertex D (phaseDepth m)) c)

def assignedLabel {n : ℕ} (D : FiniteScaleSource n) (m : ℕ)
    (directionIndex : Index → Fin n) (u : Index × Index) : Index × (Index × ℤ) :=
  (u.1,packetLabel (slopeVector D (directionIndex u.1)) (64/((2^(phaseDepth m):ℕ):ℝ))
    (64/((2^m:ℕ):ℝ)) (rawVertex D (phaseDepth m) u.2))

/-- Every complete old vertex fiber supplied by a genuine short row belongs
to the SAME node-tagged reference packet. Reference enlargement never changes
the old labels, old weights, or the direction used by predecessor iteration. -/
theorem short_closure_tag_subset {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hmL : m ≤ level) (hm6 : 6 ≤ m)
    (hlarge : 64/((2^m:ℕ):ℝ) ≤ 1)
    (hscale : D.thickness ≤ (64/((2^m:ℕ):ℝ))^2)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (hE : E⊆incidences original)
    (S : Finset Index) (directionIndex : Index → Fin n)
    (anchor : Fin n × Index) (hanchor : anchor∈E) (hS : anchor.2∈S)
    (hangular : (parentLabel D a (2^m) anchor.1).1=
      (parentLabel D a (2^m) (directionIndex (spatialLabel D (2^m) anchor.2))).1) :
    (shortVertexClosure D a level (phaseDepth m) m rep E anchor).image
      (fun k => (spatialLabel D (2^m) anchor.2,k)) ⊆
        packetSet D m E S directionIndex (assignedLabel D m directionIndex
          (spatialLabel D (2^m) anchor.2,anchor.2)) := by
  let Delta : ℝ := 64/((2^m:ℕ):ℝ)
  let H : ℝ := 64/((2^(phaseDepth m):ℕ):ℝ)
  let point : Index → E4 := cellCenter (mesh D)
  let vertex := rawVertex D (phaseDepth m)
  let v : Index → E4 := fun z => slopeVector D (directionIndex z)
  let T := occupiedLabels S point vertex Delta H Delta v
  let c := assignedLabel D m directionIndex (spatialLabel D (2^m) anchor.2,anchor.2)
  have hD : 0 < Delta := by dsimp [Delta]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hsquare : H=Delta^2 := squared_scale_identity m hm6
  have hHD : H ≤ Delta := by rw [hsquare]; change Delta ≤ 1 at hlarge; nlinarith
  have hround (k : Index) : dist (vertex k) (point k) ≤ 2*H := by
    exact roundedVertex_distance H hH (point k)
  have hv4 : ∀z,v z (3:Fin 4)=1 := fun z => slopeVector_last D (directionIndex z)
  have hv : ∀z,‖v z‖ ≤ 2 := fun z => NativeRankOneSlopeCap.slopeVector_norm_le_two h (directionIndex z)
  have hanchors : ∀u∈T,∃x z : E4,wzDyadicCellIndex Delta x=u.1 ∧
      dist z x ≤ 2*H ∧ packetLabel (v u.1) H Delta z=u.2 := by
    intro u hu
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hu
    exact ⟨point k,vertex k,rfl,hround k,rfl⟩
  have hcT : c∈T := mem_image_of_mem _ hS
  intro u hu
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hu
  obtain ⟨hkE,hpkt⟩ := full_fiber_mem_packet h original horiginal ha level m hdy hmL hm6
    hlarge hscale rep E hE anchor hanchor (directionIndex (spatialLabel D (2^m) anchor.2)) hangular k hk
  have hpk : NativeScaledLinePackets.packet (v c.1) H Delta 64 512 c.2 (vertex k) := hpkt
  have hLift : (c.1,k)∈referenceLift T v H Delta (E.image Prod.snd) vertex := by
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem Prod.fst hcT,hkE⟩,
      mem_image.mpr ⟨c,mem_filter.mpr ⟨hcT,hpk⟩,rfl⟩⟩
  have hbox := referenceLift_subset_box T v Delta H Delta hD hH hD hHD (by linarith)
    hv4 hv hanchors (E.image Prod.snd) vertex hLift
  have hnode : T.image Prod.fst=S.image (spatialLabel D (2^m)) :=
    occupiedLabels_nodes S point vertex Delta H Delta v
  rw [hnode] at hbox
  exact mem_filter.mpr ⟨hbox,⟨rfl,hpk⟩⟩

end NativeTaggedPacketRows
