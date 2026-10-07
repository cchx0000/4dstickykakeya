import Theorems.Thm_StickyKakeya4_native_quantized_line_packets

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace NativeScaledLinePackets
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalDiameterCount NativeQuantizedProjectionGrains NativeQuantizedLinePackets

def packet (v : E4) (H Delta : ℝ) (C S : ℕ) (c : Index × ℤ) (x : E4) : Prop :=
  packetLabel v H Delta x∈neighbors c (2*C) S

def occurrences {α : Type*} (A : Finset α) (loc : α → Index) (mesh : ℝ)
    (v : E4) (H Delta : ℝ) (C S : ℕ) (c : Index × ℤ) : Finset α :=
  A.filter (fun a => packet v H Delta C S c (cellCenter mesh (loc a)))

/-- Arbitrary fixed integer row widths, including the additional displacement
created by replacing old points with physical cube centers. -/
theorem packetLabel_mem_neighbors_of_row (v : E4) (H Delta : ℝ)
    (hH : 0 < H) (hD : 0 < Delta) (C S : ℕ) (hC : 0 < C)
    (x y : E4) (hline : Metric.infDist (y-x) (Submodule.span ℝ {v}:Set E4) ≤ (C:ℝ)*H)
    (hheight : |y (3:Fin 4)-x (3:Fin 4)| ≤ (S:ℝ)*Delta) :
    packet v H Delta C S (packetLabel v H Delta x) y := by
  apply mem_product.mpr
  constructor
  · apply label_mem_box_of_normal_bound (Submodule.span ℝ {v}) H hH y x (2*C)
    have hCr : (0:ℝ) < C := by exact_mod_cast hC
    have hh := normal_norm_le_of_near (Submodule.span ℝ {v}) ((C:ℝ)*H) (by positivity) (y-x) hline
    simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using hh
  · have hh : |y (3:Fin 4)/Delta-x (3:Fin 4)/Delta| ≤ (S:ℝ) := by
      rw [←sub_div,abs_div,abs_of_pos hD]
      exact (div_le_iff₀ hD).mpr hheight
    exact floor_mem_interval S hh

theorem packet_geometry (v : E4) (H Delta : ℝ) (hH : 0 < H) (hD : 0 < Delta)
    (C S : ℕ) (x y : E4) (hxy : packet v H Delta C S (packetLabel v H Delta x) y) :
    Metric.infDist (y-x) (Submodule.span ℝ {v}:Set E4) ≤ 2*(2*(C:ℝ)+1)*H ∧
      |y (3:Fin 4)-x (3:Fin 4)| ≤ ((S:ℝ)+1)*Delta := by
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using neighbors_geometry v H Delta hH hD x y (2*C) S hxy

theorem row_subset_occurrences {α : Type*} (A B : Finset α) (hBA : B⊆A)
    (loc : α → Index) (mesh : ℝ) (v : E4) (H Delta : ℝ) (hH : 0 < H) (hD : 0 < Delta)
    (C S : ℕ) (hC : 0 < C) (x : E4)
    (hrow : ∀b∈B,Metric.infDist (cellCenter mesh (loc b)-x) (Submodule.span ℝ {v}:Set E4) ≤ (C:ℝ)*H ∧
      |cellCenter mesh (loc b) (3:Fin 4)-x (3:Fin 4)| ≤ (S:ℝ)*Delta) :
    B⊆occurrences A loc mesh v H Delta C S (packetLabel v H Delta x) := by
  intro b hb
  exact mem_filter.mpr ⟨hBA hb,packetLabel_mem_neighbors_of_row v H Delta hH hD C S hC x
    (cellCenter mesh (loc b)) (hrow b hb).1 (hrow b hb).2⟩

theorem packet_overlap (T : Finset (Index × ℤ)) (v : E4) (H Delta : ℝ) (C S : ℕ) (x : E4) :
    (T.filter (fun c => packet v H Delta C S c x)).card ≤ (4*C+1)^4*(2*S+1) := by
  have hs : T.filter (fun c => packet v H Delta C S c x) ⊆ neighbors (packetLabel v H Delta x) (2*C) S := by
    intro c hc
    exact (mem_neighbors_symm _ _ _ _).mp (mem_filter.mp hc).2
  have he : 2*(2*C)+1=4*C+1 := by ring
  simpa only [neighbors_card,he] using card_le_card hs

/-- Counts packet membership of each unchanged original occurrence label. -/
theorem occurrence_overlap {α : Type*} (T : Finset (Index × ℤ)) (A : Finset α)
    (loc : α → Index) (mesh : ℝ) (v : E4) (H Delta : ℝ) (C S : ℕ) (a : α) :
    (T.filter (fun c => a∈occurrences A loc mesh v H Delta C S c)).card ≤ (4*C+1)^4*(2*S+1) := by
  apply le_trans (card_le_card (show T.filter (fun c => a∈occurrences A loc mesh v H Delta C S c) ⊆
      T.filter (fun c => packet v H Delta C S c (cellCenter mesh (loc a))) from ?_))
    (packet_overlap T v H Delta C S (cellCenter mesh (loc a)))
  intro c hc
  exact mem_filter.mpr ⟨(mem_filter.mp hc).1,(mem_filter.mp (mem_filter.mp hc).2).2⟩

/-- Safe parameters after rounding both the row point and its anchor to
physical centers: 52H in the line distance and 256Delta+2H in height. -/
theorem rounded_row_subset {α : Type*} (A B : Finset α) (hBA : B⊆A)
    (loc : α → Index) (mesh : ℝ) (v : E4) (H Delta : ℝ)
    (hH : 0 < H) (hD : 0 < Delta) (hHD : H ≤ Delta) (x : E4)
    (hrow : ∀b∈B,Metric.infDist (cellCenter mesh (loc b)-x) (Submodule.span ℝ {v}:Set E4) ≤ 52*H ∧
      |cellCenter mesh (loc b) (3:Fin 4)-x (3:Fin 4)| ≤ 256*Delta+2*H) :
    B⊆occurrences A loc mesh v H Delta 64 512 (packetLabel v H Delta x) := by
  apply row_subset_occurrences A B hBA loc mesh v H Delta hH hD 64 512 (by decide) x
  intro b hb
  obtain ⟨hl,ht⟩ := hrow b hb
  constructor <;> norm_num <;> nlinarith

theorem rounded_occurrence_overlap {α : Type*} (T : Finset (Index × ℤ)) (A : Finset α)
    (loc : α → Index) (mesh : ℝ) (v : E4) (H Delta : ℝ) (a : α) :
    (T.filter (fun c => a∈occurrences A loc mesh v H Delta 64 512 c)).card ≤ 257^4*1025 := by
  simpa only [show 4*64+1=257 by norm_num,show 2*512+1=1025 by norm_num] using
    occurrence_overlap T A loc mesh v H Delta 64 512 a

theorem rounded_packet_geometry (v : E4) (H Delta : ℝ) (hH : 0 < H) (hD : 0 < Delta)
    (x y : E4) (hxy : packet v H Delta 64 512 (packetLabel v H Delta x) y) :
    Metric.infDist (y-x) (Submodule.span ℝ {v}:Set E4) ≤ 258*H ∧
      |y (3:Fin 4)-x (3:Fin 4)| ≤ 513*Delta := by
  simpa only [Nat.cast_ofNat,show (2:ℝ)*(2*64+1)=258 by norm_num,show (512:ℝ)+1=513 by norm_num] using
    packet_geometry v H Delta hH hD 64 512 x y hxy

end NativeScaledLinePackets
