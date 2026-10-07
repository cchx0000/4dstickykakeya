import Theorems.Thm_StickyKakeya4_native_scaled_line_packets

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeNodalPacketOverlap
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalDiameterCount NativeQuantizedProjectionGrains NativeQuantizedLinePackets

lemma normal_norm_le_infDist (P : Submodule ℝ E4) (x : E4) :
    ‖normal P x‖ ≤ Metric.infDist x (P:Set E4) := by
  apply (Metric.le_infDist (show (P:Set E4).Nonempty from ⟨0,P.zero_mem⟩)).mpr
  intro u hu
  have hz : normal P u=0 := P.starProjection_orthogonal_apply_eq_zero hu
  have he : normal P (x-u)=normal P x := by rw [map_sub,hz,sub_zero]
  calc
    _ = ‖normal P (x-u)‖ := congrArg norm he.symm
    _ ≤ ‖x-u‖ := Pᗮ.norm_starProjection_apply_le _
    _ = dist x u := (dist_eq_norm x u).symm

/-- A graph direction controls the physical displacement from its normal
distance and its fourth coordinate. -/
theorem graph_displacement (v w : E4) (hv4 : v (3:Fin 4)=1) (hv : ‖v‖ ≤ 2)
    (eps T : ℝ) (hn : Metric.infDist w (Submodule.span ℝ {v}:Set E4) ≤ eps)
    (ht : |w (3:Fin 4)| ≤ T) : ‖w‖ ≤ 3*eps+2*T := by
  let P : Submodule ℝ E4 := Submodule.span ℝ {v}
  let e : E4 := normal P w
  have he : ‖e‖ ≤ eps := (normal_norm_le_infDist P w).trans hn
  obtain ⟨t,htv⟩ := Submodule.mem_span_singleton.mp (P.starProjection_apply_mem w)
  have hw : w=t • v+e := by
    dsimp [e,normal]
    rw [Submodule.starProjection_orthogonal_val,htv]
    abel
  have hw4 : w (3:Fin 4)=t+e (3:Fin 4) := by
    rw [hw]
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,hv4,mul_one]
  have he4 : |e (3:Fin 4)| ≤ eps := (coordinate_abs_le_norm e (3:Fin 4)).trans he
  have ht' : |t| ≤ T+eps := by
    calc
      _ = |w (3:Fin 4)-e (3:Fin 4)| := by rw [hw4]; ring_nf
      _ ≤ |w (3:Fin 4)|+|e (3:Fin 4)| := abs_sub _ _
      _ ≤ T+eps := add_le_add ht he4
  calc
    _ ≤ ‖t • v‖+‖e‖ := by rw [hw]; exact norm_add_le _ _
    _ = |t| * ‖v‖+‖e‖ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ (T+eps)*2+eps := add_le_add
      (mul_le_mul ht' hv (norm_nonneg v) ((abs_nonneg t).trans ht')) he
    _ = _ := by ring

theorem packet_anchor_distance (v : E4) (H Delta : ℝ) (hH : 0 < H) (hD : 0 < Delta)
    (hHD : H ≤ Delta) (hv4 : v (3:Fin 4)=1) (hv : ‖v‖ ≤ 2) (x y : E4)
    (hxy : NativeScaledLinePackets.packet v H Delta 64 512 (packetLabel v H Delta x) y) :
    dist y x ≤ 1800*Delta := by
  obtain ⟨hn,ht⟩ := NativeScaledLinePackets.rounded_packet_geometry v H Delta hH hD x y hxy
  have hh := graph_displacement v (y-x) hv4 hv (258*H) (513*Delta) hn
    (by simpa only [PiLp.sub_apply] using ht)
  rw [dist_eq_norm]
  nlinarith

/-- The node belongs to the original anchor, while the packet belongs to
its rounded vertex. Their explicit rounding error is retained. -/
theorem original_anchor_distance (v : E4) (H Delta : ℝ) (hH : 0 < H) (hD : 0 < Delta)
    (hHD : H ≤ Delta) (hv4 : v (3:Fin 4)=1) (hv : ‖v‖ ≤ 2) (x z y : E4)
    (hr : dist z x ≤ 2*H)
    (hzy : NativeScaledLinePackets.packet v H Delta 64 512 (packetLabel v H Delta z) y) :
    dist y x ≤ 1802*Delta := by
  have hz := packet_anchor_distance v H Delta hH hD hHD hv4 hv z y hzy
  calc
    _ ≤ dist y z+dist z x := dist_triangle _ _ _
    _ ≤ 1800*Delta+2*H := add_le_add hz hr
    _ ≤ _ := by linarith

theorem node_mem_box (nodeMesh Delta : ℝ) (hm : 0 < nodeMesh)
    (hscale : Delta ≤ 2*nodeMesh) (x y : E4) (hxy : dist y x ≤ 1802*Delta) :
    wzDyadicCellIndex nodeMesh x∈indexBox (wzDyadicCellIndex nodeMesh y) 4096 := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have hc : |x j-y j| ≤ 1802*Delta := by
    have hh := PiLp.dist_apply_le x y j
    rw [Real.dist_eq,dist_comm x y] at hh
    exact hh.trans hxy
  have hs : |x j/nodeMesh-y j/nodeMesh| ≤ (4096:ℝ) := by
    rw [←sub_div,abs_div,abs_of_pos hm]
    apply (div_le_iff₀ hm).mpr
    nlinarith
  exact floor_mem_interval 4096 hs

def hits (T : Finset (Index × (Index × ℤ))) (v : Index → E4)
    (H Delta : ℝ) (y : E4) : Finset (Index × (Index × ℤ)) :=
  T.filter (fun c => NativeScaledLinePackets.packet (v c.1) H Delta 64 512 c.2 y)

theorem hit_node_mem_box (T : Finset (Index × (Index × ℤ))) (v : Index → E4)
    (nodeMesh H Delta : ℝ) (hm : 0 < nodeMesh) (hH : 0 < H) (hD : 0 < Delta)
    (hHD : H ≤ Delta) (hscale : Delta ≤ 2*nodeMesh)
    (hv4 : ∀n,v n (3:Fin 4)=1) (hv : ∀n,‖v n‖ ≤ 2)
    (hanchor : ∀c∈T,∃x z : E4,wzDyadicCellIndex nodeMesh x=c.1 ∧
      dist z x ≤ 2*H ∧ packetLabel (v c.1) H Delta z=c.2)
    (y : E4) (c : Index × (Index × ℤ)) (hc : c∈hits T v H Delta y) :
    c.1∈indexBox (wzDyadicCellIndex nodeMesh y) 4096 := by
  obtain ⟨hcT,hcy⟩ := mem_filter.mp hc
  obtain ⟨x,z,hxn,hr,hzc⟩ := hanchor c hcT
  have hh := original_anchor_distance (v c.1) H Delta hH hD hHD (hv4 c.1) (hv c.1) x z y hr
    (by simpa only [hzc] using hcy)
  simpa only [hxn] using node_mem_box nodeMesh Delta hm hscale x y hh

/-- The overlap is uniform even when every node chooses a different
graph direction. Each label has a true original anchor and a rounded vertex. -/
theorem nodal_packet_overlap (T : Finset (Index × (Index × ℤ))) (v : Index → E4)
    (nodeMesh H Delta : ℝ) (hm : 0 < nodeMesh) (hH : 0 < H) (hD : 0 < Delta)
    (hHD : H ≤ Delta) (hscale : Delta ≤ 2*nodeMesh)
    (hv4 : ∀n,v n (3:Fin 4)=1) (hv : ∀n,‖v n‖ ≤ 2)
    (hanchor : ∀c∈T,∃x z : E4,wzDyadicCellIndex nodeMesh x=c.1 ∧
      dist z x ≤ 2*H ∧ packetLabel (v c.1) H Delta z=c.2)
    (y : E4) : (hits T v H Delta y).card ≤ 8193^4*(257^4*1025) := by
  have hh : (hits T v H Delta y).card ≤
      (257^4*1025)*(indexBox (wzDyadicCellIndex nodeMesh y) 4096).card := by
    apply card_le_mul_card_image_of_maps_to (f:=Prod.fst)
    · intro c hc
      exact hit_node_mem_box T v nodeMesh H Delta hm hH hD hHD hscale hv4 hv hanchor y c hc
    · intro n _hn
      calc
        _ ≤ ((T.image Prod.snd).filter (fun c => NativeScaledLinePackets.packet (v n) H Delta 64 512 c y)).card := by
          apply card_le_card_of_injOn Prod.snd
          · intro c hc
            obtain ⟨hc,hcn⟩ := mem_filter.mp hc
            obtain ⟨hcT,hcy⟩ := mem_filter.mp hc
            exact mem_filter.mpr ⟨mem_image_of_mem Prod.snd hcT,by simpa only [hcn] using hcy⟩
          · intro c hc d hd hcd
            exact Prod.ext ((mem_filter.mp hc).2.trans (mem_filter.mp hd).2.symm) hcd
        _ ≤ 257^4*1025 := by
          simpa only [show 4*64+1=257 by norm_num,show 2*512+1=1025 by norm_num] using
            NativeScaledLinePackets.packet_overlap (T.image Prod.snd) (v n) H Delta 64 512 y
  simpa only [indexBox_card,show 2*4096+1=8193 by norm_num,Nat.mul_comm] using hh

theorem nodal_duplication (T : Finset (Index × (Index × ℤ))) (v : Index → E4)
    (nodeMesh H Delta : ℝ) (hm : 0 < nodeMesh) (hH : 0 < H) (hD : 0 < Delta)
    (hHD : H ≤ Delta) (hscale : Delta ≤ 2*nodeMesh)
    (hv4 : ∀n,v n (3:Fin 4)=1) (hv : ∀n,‖v n‖ ≤ 2)
    (hanchor : ∀c∈T,∃x z : E4,wzDyadicCellIndex nodeMesh x=c.1 ∧
      dist z x ≤ 2*H ∧ packetLabel (v c.1) H Delta z=c.2)
    (y : E4) : ((hits T v H Delta y).image Prod.fst).card ≤ 8193^4 := by
  have hs : (hits T v H Delta y).image Prod.fst ⊆ indexBox (wzDyadicCellIndex nodeMesh y) 4096 := by
    intro n hn
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hn
    exact hit_node_mem_box T v nodeMesh H Delta hm hH hD hHD hscale hv4 hv hanchor y c hc
  simpa only [indexBox_card,show 2*4096+1=8193 by norm_num] using card_le_card hs

/-- The first map is the original point. The second map is its actual
rounded vertex. The occupied labels are computed before any reference lift. -/
def occupiedLabels {α : Type*} (A : Finset α) (point vertex : α → E4)
    (nodeMesh H Delta : ℝ) (v : Index → E4) : Finset (Index × (Index × ℤ)) :=
  A.image (fun a => (wzDyadicCellIndex nodeMesh (point a),
    packetLabel (v (wzDyadicCellIndex nodeMesh (point a))) H Delta (vertex a)))

theorem occupiedLabels_anchors {α : Type*} (A : Finset α) (point vertex : α → E4)
    (nodeMesh H Delta : ℝ) (v : Index → E4) (hr : ∀a∈A,dist (vertex a) (point a) ≤ 2*H) :
    ∀c∈occupiedLabels A point vertex nodeMesh H Delta v,
      ∃x z : E4,wzDyadicCellIndex nodeMesh x=c.1 ∧ dist z x ≤ 2*H ∧
        packetLabel (v c.1) H Delta z=c.2 := by
  intro c hc
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hc
  exact ⟨point a,vertex a,rfl,hr a ha,rfl⟩

/-- A source-facing overlap theorem for literal original and rounded
centers. No overlap or node-count certificate is an input. -/
theorem occupied_overlap {α : Type*} (A : Finset α) (point vertex : α → E4)
    (nodeMesh H Delta : ℝ) (v : Index → E4)
    (hm : 0 < nodeMesh) (hH : 0 < H) (hD : 0 < Delta)
    (hHD : H ≤ Delta) (hscale : Delta ≤ 2*nodeMesh)
    (hv4 : ∀n,v n (3:Fin 4)=1) (hv : ∀n,‖v n‖ ≤ 2)
    (hr : ∀a∈A,dist (vertex a) (point a) ≤ 2*H) (y : E4) :
    (hits (occupiedLabels A point vertex nodeMesh H Delta v) v H Delta y).card ≤
      8193^4*(257^4*1025) ∧
    ((hits (occupiedLabels A point vertex nodeMesh H Delta v) v H Delta y).image Prod.fst).card ≤ 8193^4 := by
  have ha := occupiedLabels_anchors A point vertex nodeMesh H Delta v hr
  exact ⟨nodal_packet_overlap _ v nodeMesh H Delta hm hH hD hHD hscale hv4 hv ha y,
    nodal_duplication _ v nodeMesh H Delta hm hH hD hHD hscale hv4 hv ha y⟩

end NativeNodalPacketOverlap
