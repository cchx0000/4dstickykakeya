import Theorems.Thm_StickyKakeya4_original_height_interval_cap
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalSeparatedHeightCap
open Classical
lemma floor_injective_of_separated (Z : Finset ℝ) {delta : ℝ} (hd : 0 < delta)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|) : Set.InjOn (fun z : ℝ => ⌊z/delta⌋) (↑Z) := by
  intro z hz w hw heq
  change ⌊z/delta⌋=⌊w/delta⌋ at heq
  by_contra hne
  have hlz := (le_div_iff₀ hd).mp (Int.floor_le (z/delta))
  have huw := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (w/delta))
  have hlw := (le_div_iff₀ hd).mp (Int.floor_le (w/delta))
  have huz := (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (z/delta))
  rw [heq] at hlz huz
  have hgap : |z-w| < delta := abs_lt.mpr ⟨by nlinarith,by nlinarith⟩
  exact (not_lt_of_ge (hsep z hz w hw hne)) hgap
theorem separated_interval_cap (Z : Finset ℝ) {delta : ℝ} (hd : 0 < delta)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|) (c r : ℝ) (hr : 0 ≤ r) :
    ((Z.filter (fun z => c ≤ z ∧ z ≤ c+r)).card : ℝ) ≤ r/delta+2 := by
  let P := Z.filter (fun z => c ≤ z ∧ z ≤ c+r)
  let Q := Finset.Icc ⌊c/delta⌋ ⌊(c+r)/delta⌋
  have hmaps : Set.MapsTo (fun z : ℝ => ⌊z/delta⌋) (↑P) (↑Q) := by
    intro z hz
    obtain ⟨_hz,hlo,hhi⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_Icc.mpr ⟨Int.floor_mono (div_le_div_of_nonneg_right hlo hd.le),Int.floor_mono (div_le_div_of_nonneg_right hhi hd.le)⟩
  have hinj : Set.InjOn (fun z : ℝ => ⌊z/delta⌋) (↑P) := by
    intro z hz w hw he
    exact floor_injective_of_separated Z hd hsep (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hw).1 he
  exact (Nat.cast_le.mpr (Finset.card_le_card_of_injOn _ hmaps hinj)).trans
    (OriginalHeightIntervalCap.floor_interval_card delta c r hd hr)
theorem original_coarse_height_fiber_cap (Z : Finset ℝ) {delta width : ℝ}
    (hd : 0 < delta) (hw : 0 < width)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|) (k : ℤ) :
    ((Z.filter (fun z => ⌊z/width⌋=k)).card : ℝ) ≤ width/delta+2 := by
  have hsub : Z.filter (fun z => ⌊z/width⌋=k) ⊆
      Z.filter (fun z => width*(k:ℝ) ≤ z ∧ z ≤ width*(k:ℝ)+width) := by
    intro z hz
    obtain ⟨hzZ,hzk⟩ := Finset.mem_filter.mp hz
    have hl := (le_div_iff₀ hw).mp (Int.floor_le (z/width))
    have hu := (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (z/width))
    rw [hzk] at hl hu
    exact Finset.mem_filter.mpr ⟨hzZ,by nlinarith,by nlinarith⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (separated_interval_cap Z hd hsep (width*(k:ℝ)) width hw.le)
end OriginalSeparatedHeightCap
