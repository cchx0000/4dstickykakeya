import Theorems.Thm_StickyKakeya4_native_original_cell_chart_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable section
namespace NativeCubicalDiameterCount
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalCellChartGeometry

def indexBox (k : Index) (M : ℕ) : Finset Index :=
  Fintype.piFinset (fun j => Icc (k j-(M:ℤ)) (k j+M))

lemma indexBox_card (k : Index) (M : ℕ) : (indexBox k M).card=(2*M+1)^4 := by
  have hi (j : Fin 4) : (Icc (k j-(M:ℤ)) (k j+M)).card=2*M+1 := by
    have hh : ((Icc (k j-(M:ℤ)) (k j+M)).card:ℤ)=2*(M:ℤ)+1 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp only [indexBox,Fintype.card_piFinset,Fin.prod_univ_four,hi]
  ring

def capacity (mesh D : ℝ) : ℕ := (2*⌊D/mesh⌋₊+1)^4

lemma coordinate_gap_le {mesh : ℝ} (hm : 0 < mesh) (k l : Index)
    (D : ℝ) (hD : dist (cellCenter mesh k) (cellCenter mesh l) ≤ D)
    (j : Fin 4) : |(k j:ℝ)-(l j:ℝ)| ≤ D/mesh := by
  have hh : |(cellCenter mesh k) j-(cellCenter mesh l) j| ≤ D :=
    (show |(cellCenter mesh k) j-(cellCenter mesh l) j| ≤
      dist (cellCenter mesh k) (cellCenter mesh l) by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le (cellCenter mesh k) (cellCenter mesh l) j).trans hD
  have he : (cellCenter mesh k) j-(cellCenter mesh l) j=mesh*((k j:ℝ)-(l j:ℝ)) := by
    dsimp [cellCenter]
    ring
  rw [he,abs_mul,abs_of_pos hm] at hh
  exact (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hh)

lemma mem_indexBox_of_dist {mesh : ℝ} (hm : 0 < mesh) (k l : Index)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : dist (cellCenter mesh k) (cellCenter mesh l) ≤ D) :
    k∈indexBox l ⌊D/mesh⌋₊ := by
  have hfloor : ((⌊D/mesh⌋₊:ℕ):ℤ)=⌊D/mesh⌋ := by
    rw [←Int.floor_toNat,Int.toNat_of_nonneg (Int.floor_nonneg.mpr (div_nonneg hD0 hm.le))]
  apply Fintype.mem_piFinset.mpr
  intro j
  have hh := abs_le.mp (coordinate_gap_le hm k l D hD j)
  have hhi : k j-l j ≤ ⌊D/mesh⌋ := Int.le_floor.mpr (by push_cast; exact hh.2)
  have hlo : l j-k j ≤ ⌊D/mesh⌋ := Int.le_floor.mpr (by push_cast; linarith [hh.1])
  apply mem_Icc.mpr
  rw [hfloor]
  omega

/-- Distinct original cubical labels in a bounded-diameter set occupy a
literal finite integer box. No grid separation certificate is required. -/
theorem card_le_of_center_diameter (A : Finset Index) {mesh : ℝ} (hm : 0 < mesh)
    (D : ℝ) (hD0 : 0 ≤ D)
    (H : ∀k∈A,∀l∈A,dist (cellCenter mesh k) (cellCenter mesh l) ≤ D) :
    A.card ≤ capacity mesh D := by
  by_cases hAn : A.Nonempty
  · obtain ⟨l,hl⟩ := hAn
    have hsub : A⊆indexBox l ⌊D/mesh⌋₊ := by
      intro k hk
      exact mem_indexBox_of_dist hm k l D hD0 (H k hk l hl)
    simpa only [indexBox_card,capacity] using card_le_card hsub
  · simp only [not_nonempty_iff_eq_empty.mp hAn,card_empty]
    exact Nat.zero_le _

lemma capacity_le_real {mesh D : ℝ} (hm : 0 < mesh) (hD : 0 ≤ D) :
    (capacity mesh D:ℝ) ≤ (2*(D/mesh)+1)^4 := by
  have hf := Nat.floor_le (div_nonneg hD hm.le)
  have hh : (0:ℝ) ≤ 2*(⌊D/mesh⌋₊:ℝ)+1 := by positivity
  have hle : 2*(⌊D/mesh⌋₊:ℝ)+1 ≤ 2*(D/mesh)+1 := by linarith
  simpa only [capacity,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
    pow_le_pow_left₀ hh hle 4

theorem card_le_real_of_center_diameter (A : Finset Index) {mesh : ℝ} (hm : 0 < mesh)
    (D : ℝ) (hD0 : 0 ≤ D)
    (H : ∀k∈A,∀l∈A,dist (cellCenter mesh k) (cellCenter mesh l) ≤ D) :
    (A.card:ℝ) ≤ (2*(D/mesh)+1)^4 :=
  (show (A.card:ℝ) ≤ capacity mesh D by exact_mod_cast card_le_of_center_diameter A hm D hD0 H).trans
    (capacity_le_real hm hD0)

end NativeCubicalDiameterCount
