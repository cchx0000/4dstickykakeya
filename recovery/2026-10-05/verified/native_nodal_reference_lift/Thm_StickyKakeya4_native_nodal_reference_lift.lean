import Theorems.Thm_StickyKakeya4_native_nodal_packet_overlap

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

noncomputable section
namespace NativeNodalReferenceLift
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalDiameterCount NativeQuantizedLinePackets NativeNodalPacketOverlap
open scoped BigOperators

def roundedVertex (H : ℝ) (x : E4) : E4 := cellCenter H (wzDyadicCellIndex H x)

lemma roundedVertex_distance (H : ℝ) (hH : 0 < H) (x : E4) :
    dist (roundedVertex H x) x ≤ 2*H :=
  (wzDyadicCell_subset_ball_of_mem hH _ (mem_wzDyadicCell_index hH x)
    (cellCenter_mem hH _)).le

/-- The rounding input of the nodal overlap theorem is proved for the
actual vertex obtained by taking the center of the point's raw H-cube. -/
theorem rounded_occupied_overlap {α : Type*} (A : Finset α) (point : α → E4)
    (nodeMesh H Delta : ℝ) (v : Index → E4)
    (hm : 0 < nodeMesh) (hH : 0 < H) (hD : 0 < Delta)
    (hHD : H ≤ Delta) (hscale : Delta ≤ 2*nodeMesh)
    (hv4 : ∀n,v n (3:Fin 4)=1) (hv : ∀n,‖v n‖ ≤ 2) (y : E4) :
    let T := occupiedLabels A point (fun a => roundedVertex H (point a)) nodeMesh H Delta v
    (hits T v H Delta y).card ≤ 8193^4*(257^4*1025) ∧
      ((hits T v H Delta y).image Prod.fst).card ≤ 8193^4 := by
  exact occupied_overlap A point (fun a => roundedVertex H (point a)) nodeMesh H Delta v
    hm hH hD hHD hscale hv4 hv (fun a _ => roundedVertex_distance H hH (point a)) y

/-- Original reference labels are duplicated only at nodes whose actual
occupied packets meet them. Keeping this tag makes every direction node-local. -/
def referenceLift {α : Type*} (T : Finset (Index × (Index × ℤ))) (v : Index → E4)
    (H Delta : ℝ) (R : Finset α) (point : α → E4) : Finset (Index × α) :=
  ((T.image Prod.fst) ×ˢ R).filter (fun u => u.1∈(hits T v H Delta (point u.2)).image Prod.fst)

def currentLift {α : Type*} (A : Finset α) (point : α → E4) (nodeMesh : ℝ) : Finset (Index × α) :=
  A.image (fun a => (wzDyadicCellIndex nodeMesh (point a),a))

lemma currentLift_snd_injective {α : Type*} (A : Finset α) (point : α → E4) (nodeMesh : ℝ) :
    Set.InjOn Prod.snd (currentLift A point nodeMesh:Set (Index × α)) := by
  intro u hu z hz huz
  obtain ⟨a,_ha,rfl⟩ := mem_image.mp hu
  obtain ⟨b,_hb,rfl⟩ := mem_image.mp hz
  change a=b at huz
  subst b
  rfl

lemma currentLift_card {α : Type*} (A : Finset α) (point : α → E4) (nodeMesh : ℝ) :
    (currentLift A point nodeMesh).card=A.card := by
  apply card_image_iff.mpr
  intro a _ha b _hb hab
  exact congrArg Prod.snd hab

theorem currentLift_mass {α : Type*} (A : Finset α) (point : α → E4)
    (nodeMesh : ℝ) (w : α → ℕ) :
    (∑u∈currentLift A point nodeMesh,w u.2)=∑a∈A,w a := by
  apply sum_image
  intro a _ha b _hb hab
  exact congrArg Prod.snd hab

/-- Every current label is tagged by its unique original node and occurs
in the reference lift through its own occupied packet. -/
theorem currentLift_subset_reference {α : Type*} (A R : Finset α) (hAR : A⊆R)
    (point vertex : α → E4) (nodeMesh H Delta : ℝ) (v : Index → E4) :
    currentLift A point nodeMesh ⊆
      referenceLift (occupiedLabels A point vertex nodeMesh H Delta v) v H Delta R vertex := by
  intro u hu
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
  let c := (wzDyadicCellIndex nodeMesh (point a),
    packetLabel (v (wzDyadicCellIndex nodeMesh (point a))) H Delta (vertex a))
  have hc : c∈occupiedLabels A point vertex nodeMesh H Delta v := mem_image_of_mem _ ha
  have hself : NativeScaledLinePackets.packet (v c.1) H Delta 64 512 c.2 (vertex a) := by
    change c.2∈neighbors c.2 (2*64) 512
    apply mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro j
      apply mem_Icc.mpr
      constructor <;> omega
    · apply mem_Icc.mpr
      constructor <;> omega
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem Prod.fst hc,hAR ha⟩,
    mem_image.mpr ⟨c,mem_filter.mpr ⟨hc,hself⟩,rfl⟩⟩

lemma referenceLift_original {α : Type*} (T : Finset (Index × (Index × ℤ))) (v : Index → E4)
    (H Delta : ℝ) (R : Finset α) (point : α → E4) (u : Index × α)
    (hu : u∈referenceLift T v H Delta R point) : u.2∈R :=
  (mem_product.mp (mem_filter.mp hu).1).2

theorem reference_label_duplication {α : Type*} (T : Finset (Index × (Index × ℤ)))
    (v : Index → E4) (nodeMesh H Delta : ℝ)
    (hm : 0 < nodeMesh) (hH : 0 < H) (hD : 0 < Delta)
    (hHD : H ≤ Delta) (hscale : Delta ≤ 2*nodeMesh)
    (hv4 : ∀n,v n (3:Fin 4)=1) (hv : ∀n,‖v n‖ ≤ 2)
    (hanchor : ∀c∈T,∃x z : E4,wzDyadicCellIndex nodeMesh x=c.1 ∧
      dist z x ≤ 2*H ∧ packetLabel (v c.1) H Delta z=c.2)
    (R : Finset α) (point : α → E4) (a : α) :
    ((referenceLift T v H Delta R point).filter (fun u => u.2=a)).card ≤ 8193^4 := by
  calc
    _ ≤ ((hits T v H Delta (point a)).image Prod.fst).card := by
      apply card_le_card_of_injOn Prod.fst
      · intro u hu
        obtain ⟨hu,hua⟩ := mem_filter.mp hu
        have hh := (mem_filter.mp hu).2
        simpa only [mem_coe,hua] using hh
      · intro u hu z hz huz
        exact Prod.ext huz ((mem_filter.mp hu).2.trans (mem_filter.mp hz).2.symm)
    _ ≤ _ := nodal_duplication T v nodeMesh H Delta hm hH hD hHD hscale hv4 hv hanchor (point a)

theorem referenceLift_card {α : Type*} (T : Finset (Index × (Index × ℤ)))
    (v : Index → E4) (nodeMesh H Delta : ℝ)
    (hm : 0 < nodeMesh) (hH : 0 < H) (hD : 0 < Delta)
    (hHD : H ≤ Delta) (hscale : Delta ≤ 2*nodeMesh)
    (hv4 : ∀n,v n (3:Fin 4)=1) (hv : ∀n,‖v n‖ ≤ 2)
    (hanchor : ∀c∈T,∃x z : E4,wzDyadicCellIndex nodeMesh x=c.1 ∧
      dist z x ≤ 2*H ∧ packetLabel (v c.1) H Delta z=c.2)
    (R : Finset α) (point : α → E4) :
    (referenceLift T v H Delta R point).card ≤ 8193^4*R.card := by
  apply card_le_mul_card_image_of_maps_to (f:=Prod.snd)
  · intro u hu
    exact referenceLift_original T v H Delta R point u hu
  · intro a _ha
    exact reference_label_duplication T v nodeMesh H Delta hm hH hD hHD hscale hv4 hv hanchor R point a

/-- One common tagged reference universe, independent of all chosen
directions. This can be used unchanged at each directional stage. -/
def boxReference {α : Type*} (nodes : Finset Index) (nodeMesh : ℝ)
    (R : Finset α) (point : α → E4) : Finset (Index × α) :=
  (nodes ×ˢ R).filter (fun u => u.1∈indexBox (wzDyadicCellIndex nodeMesh (point u.2)) 4096)

theorem box_reference_duplication {α : Type*} (nodes : Finset Index) (nodeMesh : ℝ)
    (R : Finset α) (point : α → E4) (a : α) :
    ((boxReference nodes nodeMesh R point).filter (fun u => u.2=a)).card ≤ 8193^4 := by
  have hh : ((boxReference nodes nodeMesh R point).filter (fun u => u.2=a)).card ≤
      (indexBox (wzDyadicCellIndex nodeMesh (point a)) 4096).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro u hu
      obtain ⟨hu,hua⟩ := mem_filter.mp hu
      simpa only [mem_coe,hua] using (mem_filter.mp hu).2
    · intro u hu z hz huz
      exact Prod.ext huz ((mem_filter.mp hu).2.trans (mem_filter.mp hz).2.symm)
  simpa only [indexBox_card,show 2*4096+1=8193 by norm_num] using hh

/-- All original natural-number weights are preserved under the tag map;
only the proved number of possible tags appears in the reference mass. -/
theorem boxReference_mass {α : Type*} (nodes : Finset Index) (nodeMesh : ℝ)
    (R : Finset α) (point : α → E4) (w : α → ℕ) :
    (∑u∈boxReference nodes nodeMesh R point,w u.2) ≤ 8193^4*(∑a∈R,w a) := by
  let S := boxReference nodes nodeMesh R point
  have hmap : ∀u∈S,u.2∈R := by
    intro u hu
    exact (mem_product.mp (mem_filter.mp hu).1).2
  calc
    _ = ∑a∈R,∑u∈S.filter (fun u => u.2=a),w u.2 :=
      (sum_fiberwise_of_maps_to hmap (fun u => w u.2)).symm
    _ = ∑a∈R,(S.filter (fun u => u.2=a)).card*w a := by
      apply sum_congr rfl
      intro a _ha
      calc
        _ = ∑_u∈S.filter (fun u => u.2=a),w a := by
          apply sum_congr rfl
          intro u hu
          rw [(mem_filter.mp hu).2]
        _ = _ := by simp
    _ ≤ ∑a∈R,8193^4*w a := by
      apply sum_le_sum
      intro a _ha
      exact Nat.mul_le_mul_right (w a) (box_reference_duplication nodes nodeMesh R point a)
    _ = _ := by rw [mul_sum]

/-- A fixed node's vertex fiber injects into the original reference fiber.
Its weight cap therefore incurs no node-duplication factor. -/
theorem fixed_node_vertex_mass {α β : Type*} (nodes : Finset Index) (nodeMesh : ℝ)
    (R : Finset α) (point : α → E4) (w : α → ℕ) (loc : α → β) (n : Index) (b : β) :
    (∑u∈(boxReference nodes nodeMesh R point).filter (fun u => u.1=n ∧ loc u.2=b),w u.2) ≤
      ∑a∈R.filter (fun a => loc a=b),w a := by
  let S := (boxReference nodes nodeMesh R point).filter (fun u => u.1=n ∧ loc u.2=b)
  have hi : Set.InjOn Prod.snd (S:Set (Index × α)) := by
    intro u hu z hz huz
    exact Prod.ext ((mem_filter.mp hu).2.1.trans (mem_filter.mp hz).2.1.symm) huz
  have hs : S.image Prod.snd ⊆ R.filter (fun a => loc a=b) := by
    intro a ha
    obtain ⟨u,hu,rfl⟩ := mem_image.mp ha
    obtain ⟨hu,_hun,hub⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨(mem_product.mp (mem_filter.mp hu).1).2,hub⟩
  calc
    _ = ∑a∈S.image Prod.snd,w a := (sum_image hi).symm
    _ ≤ _ := sum_le_sum_of_subset hs

theorem referenceLift_subset_box {α : Type*} (T : Finset (Index × (Index × ℤ)))
    (v : Index → E4) (nodeMesh H Delta : ℝ)
    (hm : 0 < nodeMesh) (hH : 0 < H) (hD : 0 < Delta)
    (hHD : H ≤ Delta) (hscale : Delta ≤ 2*nodeMesh)
    (hv4 : ∀n,v n (3:Fin 4)=1) (hv : ∀n,‖v n‖ ≤ 2)
    (hanchor : ∀c∈T,∃x z : E4,wzDyadicCellIndex nodeMesh x=c.1 ∧
      dist z x ≤ 2*H ∧ packetLabel (v c.1) H Delta z=c.2)
    (R : Finset α) (point : α → E4) :
    referenceLift T v H Delta R point ⊆ boxReference (T.image Prod.fst) nodeMesh R point := by
  intro u hu
  obtain ⟨hu,hun⟩ := mem_filter.mp hu
  obtain ⟨c,hc,hcu⟩ := mem_image.mp hun
  refine mem_filter.mpr ⟨hu,?_⟩
  rw [←hcu]
  exact hit_node_mem_box T v nodeMesh H Delta hm hH hD hHD hscale hv4 hv hanchor (point u.2) c hc

lemma occupiedLabels_nodes {α : Type*} (A : Finset α) (point vertex : α → E4)
    (nodeMesh H Delta : ℝ) (v : Index → E4) :
    (occupiedLabels A point vertex nodeMesh H Delta v).image Prod.fst =
      A.image (fun a => wzDyadicCellIndex nodeMesh (point a)) := by
  ext n
  simp only [occupiedLabels,mem_image]
  constructor
  · rintro ⟨c,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨a,ha,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨_,⟨a,ha,rfl⟩,rfl⟩

theorem rounded_currentLift_subset_box {α : Type*} (A R : Finset α) (hAR : A⊆R)
    (point : α → E4) (nodeMesh H Delta : ℝ) (hm : 0 < nodeMesh)
    (hH : 0 < H) (hHD : H ≤ Delta) (hscale : Delta ≤ 2*nodeMesh) :
    currentLift A point nodeMesh ⊆
      boxReference (A.image (fun a => wzDyadicCellIndex nodeMesh (point a))) nodeMesh R
        (fun a => roundedVertex H (point a)) := by
  intro u hu
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
  refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem _ ha,hAR ha⟩,?_⟩
  apply node_mem_box nodeMesh Delta hm hscale (point a) (roundedVertex H (point a))
  have hh := roundedVertex_distance H hH (point a)
  nlinarith

/-- Packet membership requires matching node tags. -/
def taggedPacket {α : Type*} (v : Index → E4) (H Delta : ℝ) (point : α → E4)
    (c : Index × (Index × ℤ)) (u : Index × α) : Prop :=
  c.1=u.1 ∧ NativeScaledLinePackets.packet (v c.1) H Delta 64 512 c.2 (point u.2)

/-- For each fixed node-tagged reference label, only the packet factor
remains. No predecessor is silently moved to another node's direction. -/
theorem tagged_packet_overlap {α : Type*} (T : Finset (Index × (Index × ℤ)))
    (v : Index → E4) (H Delta : ℝ) (point : α → E4) (u : Index × α) :
    (T.filter (fun c => taggedPacket v H Delta point c u)).card ≤ 257^4*1025 := by
  calc
    _ ≤ ((T.image Prod.snd).filter (fun c =>
        NativeScaledLinePackets.packet (v u.1) H Delta 64 512 c (point u.2))).card := by
      apply card_le_card_of_injOn Prod.snd
      · intro c hc
        obtain ⟨hcT,hcn,hcp⟩ := mem_filter.mp hc
        exact mem_filter.mpr ⟨mem_image_of_mem Prod.snd hcT,by simpa only [hcn] using hcp⟩
      · intro c hc d hd hcd
        exact Prod.ext ((mem_filter.mp hc).2.1.trans (mem_filter.mp hd).2.1.symm) hcd
    _ ≤ _ := by
      simpa only [show 4*64+1=257 by norm_num,show 2*512+1=1025 by norm_num] using
        NativeScaledLinePackets.packet_overlap (T.image Prod.snd) (v u.1) H Delta 64 512 (point u.2)

end NativeNodalReferenceLift
