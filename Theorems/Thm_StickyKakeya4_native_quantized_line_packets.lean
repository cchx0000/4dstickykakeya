import Theorems.Thm_StickyKakeya4_native_quantized_projection_grains

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

noncomputable section
namespace NativeQuantizedLinePackets
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry
open NativeCubicalDiameterCount NativeQuantizedProjectionGrains
open scoped BigOperators

def packetLabel (v : E4) (H Delta : ℝ) (x : E4) : Index × ℤ :=
  (label (Submodule.span ℝ {v}) H x,⌊x (3:Fin 4)/Delta⌋)

def neighbors (c : Index × ℤ) (R S : ℕ) : Finset (Index × ℤ) :=
  indexBox c.1 R ×ˢ Icc (c.2-(S:ℤ)) (c.2+S)

lemma neighbors_card (c : Index × ℤ) (R S : ℕ) :
    (neighbors c R S).card=(2*R+1)^4*(2*S+1) := by
  have hi : (Icc (c.2-(S:ℤ)) (c.2+S)).card=2*S+1 := by
    have hh : ((Icc (c.2-(S:ℤ)) (c.2+S)).card:ℤ)=2*(S:ℤ)+1 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp only [neighbors,card_product,indexBox_card,hi]

lemma mem_indexBox_symm (k l : Index) (R : ℕ) : k∈indexBox l R ↔ l∈indexBox k R := by
  simp only [indexBox,Fintype.mem_piFinset,mem_Icc]
  constructor <;> intro h j <;> have hj := h j <;> omega

lemma mem_neighbors_symm (c d : Index × ℤ) (R S : ℕ) :
    c∈neighbors d R S ↔ d∈neighbors c R S := by
  simp only [neighbors,mem_product,mem_Icc]
  constructor
  · rintro ⟨hp,hl,hu⟩
    exact ⟨(mem_indexBox_symm _ _ _).mp hp,by omega,by omega⟩
  · rintro ⟨hp,hl,hu⟩
    exact ⟨(mem_indexBox_symm _ _ _).mpr hp,by omega,by omega⟩

lemma floor_mem_interval {x y : ℝ} (M : ℕ) (hxy : |x-y| ≤ M) :
    ⌊x⌋∈Icc (⌊y⌋-(M:ℤ)) (⌊y⌋+M) := by
  obtain ⟨hl,hu⟩ := abs_le.mp hxy
  refine mem_Icc.mpr ⟨?_,?_⟩
  · simpa only [Int.floor_sub_natCast] using Int.floor_mono (show y-(M:ℝ) ≤ x by linarith)
  · simpa only [Int.floor_add_natCast] using Int.floor_mono (show x ≤ y+(M:ℝ) by linarith)

lemma abs_sub_le_of_floor_mem {x y : ℝ} (M : ℕ)
    (hxy : ⌊x⌋∈Icc (⌊y⌋-(M:ℤ)) (⌊y⌋+M)) : |x-y| ≤ (M:ℝ)+1 := by
  obtain ⟨hl,hu⟩ := mem_Icc.mp hxy
  have hlR : (⌊y⌋:ℝ)-(M:ℝ) ≤ (⌊x⌋:ℝ) := by exact_mod_cast hl
  have huR : (⌊x⌋:ℝ) ≤ (⌊y⌋:ℝ)+(M:ℝ) := by exact_mod_cast hu
  have hxl := Int.floor_le x
  have hxu := Int.lt_floor_add_one x
  have hyl := Int.floor_le y
  have hyu := Int.lt_floor_add_one y
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma label_mem_box_of_normal_bound (P : Submodule ℝ E4) (H : ℝ) (hH : 0 < H)
    (x y : E4) (R : ℕ) (hxy : ‖normal P (x-y)‖ ≤ (R:ℝ)*H) :
    label P H x∈indexBox (label P H y) R := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have hc : |normal P x j-normal P y j| ≤ (R:ℝ)*H := by
    simpa only [map_sub,PiLp.sub_apply] using (coordinate_abs_le_norm (normal P (x-y)) j).trans hxy
  have hd : |normal P x j/H-normal P y j/H| ≤ (R:ℝ) := by
    rw [←sub_div,abs_div,abs_of_pos hH]
    exact (div_le_iff₀ hH).mpr hc
  exact floor_mem_interval R hd

lemma near_of_label_mem_box (P : Submodule ℝ E4) (H : ℝ) (hH : 0 < H)
    (x y : E4) (R : ℕ) (hxy : label P H x∈indexBox (label P H y) R) :
    Metric.infDist (x-y) (P:Set E4) ≤ 2*((R:ℝ)+1)*H := by
  have hc (j : Fin 4) : |normal P (x-y) j| ≤ ((R:ℝ)+1)*H := by
    have hj := (Fintype.mem_piFinset.mp hxy) j
    have hd := abs_sub_le_of_floor_mem R hj
    rw [←sub_div,abs_div,abs_of_pos hH] at hd
    have hh := (div_le_iff₀ hH).mp hd
    simpa only [map_sub,PiLp.sub_apply] using hh
  have hs : ‖normal P (x-y)‖^2 ≤ 4*(((R:ℝ)+1)*H)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑_j : Fin 4,(((R:ℝ)+1)*H)^2 := by
        apply sum_le_sum
        intro j _hj
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc j) 2
      _ = _ := by simp
  have hnon : 0 ≤ ((R:ℝ)+1)*H := by positivity
  have hn : ‖normal P (x-y)‖ ≤ 2*((R:ℝ)+1)*H := by nlinarith [norm_nonneg (normal P (x-y))]
  exact (infDist_le_normal_norm P (x-y)).trans hn

/-- Actual approximate short rows are covered by a fixed label neighborhood.
The normal estimate uses the proved approximate projection bound. -/
theorem packetLabel_mem_neighbors (v : E4) (H Delta : ℝ) (hH : 0 < H) (hD : 0 < Delta)
    (x y : E4) (hline : Metric.infDist (y-x) (Submodule.span ℝ {v}:Set E4) ≤ 50*H)
    (hheight : |y (3:Fin 4)-x (3:Fin 4)| ≤ 256*Delta) :
    packetLabel v H Delta y∈neighbors (packetLabel v H Delta x) 100 256 := by
  apply mem_product.mpr
  constructor
  · apply label_mem_box_of_normal_bound (Submodule.span ℝ {v}) H hH y x 100
    have hh := normal_norm_le_of_near (Submodule.span ℝ {v}) (50*H) (by positivity) (y-x) hline
    norm_num at hh ⊢
    linarith
  · have hh : |y (3:Fin 4)/Delta-x (3:Fin 4)/Delta| ≤ (256:ℝ) := by
      rw [←sub_div,abs_div,abs_of_pos hD]
      exact (div_le_iff₀ hD).mpr hheight
    exact floor_mem_interval 256 hh

/-- Label neighborhoods are genuine enlarged parallel line packets when
viewed from an actual anchor point. -/
theorem neighbors_geometry (v : E4) (H Delta : ℝ) (hH : 0 < H) (hD : 0 < Delta)
    (x y : E4) (R S : ℕ)
    (hxy : packetLabel v H Delta y∈neighbors (packetLabel v H Delta x) R S) :
    Metric.infDist (y-x) (Submodule.span ℝ {v}:Set E4) ≤ 2*((R:ℝ)+1)*H ∧
      |y (3:Fin 4)-x (3:Fin 4)| ≤ ((S:ℝ)+1)*Delta := by
  obtain ⟨hp,ht⟩ := mem_product.mp hxy
  refine ⟨near_of_label_mem_box (Submodule.span ℝ {v}) H hH y x R hp,?_⟩
  have hh := abs_sub_le_of_floor_mem S ht
  rw [←sub_div,abs_div,abs_of_pos hD] at hh
  exact (div_le_iff₀ hD).mp hh

def packet (v : E4) (H Delta : ℝ) (c : Index × ℤ) (x : E4) : Prop :=
  packetLabel v H Delta x∈neighbors c 100 256

def occurrences {α : Type*} (A : Finset α) (loc : α → Index) (mesh : ℝ)
    (v : E4) (H Delta : ℝ) (c : Index × ℤ) : Finset α :=
  A.filter (fun a => packet v H Delta c (cellCenter mesh (loc a)))

theorem packet_geometry (v : E4) (H Delta : ℝ) (hH : 0 < H) (hD : 0 < Delta)
    (x y : E4) (hxy : packet v H Delta (packetLabel v H Delta x) y) :
    Metric.infDist (y-x) (Submodule.span ℝ {v}:Set E4) ≤ 202*H ∧
      |y (3:Fin 4)-x (3:Fin 4)| ≤ 257*Delta := by
  simpa only [Nat.cast_ofNat,show (2:ℝ)*(100+1)=202 by norm_num,show (256:ℝ)+1=257 by norm_num] using
    neighbors_geometry v H Delta hH hD x y 100 256 hxy

/-- The row labels themselves are retained, with no geometric completion. -/
theorem row_subset_occurrences {α : Type*} (A B : Finset α) (hBA : B⊆A)
    (loc : α → Index) (mesh : ℝ) (v : E4) (H Delta : ℝ) (hH : 0 < H) (hD : 0 < Delta)
    (x : E4)
    (hrow : ∀b∈B,Metric.infDist (cellCenter mesh (loc b)-x) (Submodule.span ℝ {v}:Set E4) ≤ 50*H ∧
      |cellCenter mesh (loc b) (3:Fin 4)-x (3:Fin 4)| ≤ 256*Delta) :
    B⊆occurrences A loc mesh v H Delta (packetLabel v H Delta x) := by
  intro b hb
  exact mem_filter.mpr ⟨hBA hb,packetLabel_mem_neighbors v H Delta hH hD x (cellCenter mesh (loc b))
    (hrow b hb).1 (hrow b hb).2⟩

/-- Every point lies in at most K distinct enlarged packet labels. -/
theorem packet_overlap (T : Finset (Index × ℤ)) (v : E4) (H Delta : ℝ) (x : E4) :
    (T.filter (fun c => packet v H Delta c x)).card ≤ 201^4*513 := by
  have hs : T.filter (fun c => packet v H Delta c x) ⊆ neighbors (packetLabel v H Delta x) 100 256 := by
    intro c hc
    exact (mem_neighbors_symm _ _ _ _).mp (mem_filter.mp hc).2
  have hh := card_le_card hs
  simpa only [neighbors_card,show 2*100+1=201 by norm_num,show 2*256+1=513 by norm_num] using hh

/-- The same bound holds for each original occurrence label, even when its
vertex map is noninjective. Weighted accounting can therefore keep its weight. -/
theorem occurrence_overlap {α : Type*} (T : Finset (Index × ℤ)) (A : Finset α)
    (loc : α → Index) (mesh : ℝ) (v : E4) (H Delta : ℝ) (a : α) :
    (T.filter (fun c => a∈occurrences A loc mesh v H Delta c)).card ≤ 201^4*513 := by
  apply le_trans (card_le_card (show T.filter (fun c => a∈occurrences A loc mesh v H Delta c) ⊆
      T.filter (fun c => packet v H Delta c (cellCenter mesh (loc a))) from ?_))
    (packet_overlap T v H Delta (cellCenter mesh (loc a)))
  intro c hc
  exact mem_filter.mpr ⟨(mem_filter.mp hc).1,(mem_filter.mp (mem_filter.mp hc).2).2⟩

end NativeQuantizedLinePackets
