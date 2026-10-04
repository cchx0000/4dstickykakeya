import Theorems.Thm_StickyKakeya4_original_macro_grain_readback
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalLiteralHeightWindow
open Classical Finset NativeTangentGridCoarsening OriginalMacroGrainReadback
open scoped BigOperators
variable {P : Type*}
def window (E : Finset P) (height : P → ℝ) (q : ℝ) (k : ℤ) : Finset P :=
  E.filter (fun p => ⌊height p/q⌋=k)
/-- The selected height interval is a literal original floor interval. -/
theorem actual_height_image (E : Finset P) (height : P → ℝ) (q : ℝ) (k : ℤ) :
    (window E height q k).image height=(E.image height).filter (fun z => ⌊z/q⌋=k) := by
  ext z
  simp only [window,mem_image,mem_filter]
  constructor
  · rintro ⟨p,⟨hp,hpk⟩,rfl⟩
    exact ⟨⟨p,hp,rfl⟩,hpk⟩
  · rintro ⟨⟨p,hp,rfl⟩,hpk⟩
    exact ⟨p,⟨hp,hpk⟩,rfl⟩
/-- Whole original horizontal fibers survive inside the chosen scheduled
 interval, so their original X/Y profiles are unchanged. -/
theorem whole_height_fiber (E : Finset P) (height : P → ℝ) (q : ℝ) (k : ℤ) (z : ℝ)
    (hz : ⌊z/q⌋=k) : slice (window E height q k) height z=slice E height z := by
  ext p
  simp only [OriginalMacroGrainReadback.slice,window,mem_filter]
  constructor
  · rintro ⟨⟨hp,_⟩,hpz⟩
    exact ⟨hp,hpz⟩
  · rintro ⟨hp,hpz⟩
    exact ⟨⟨hp,by simpa only [hpz] using hz⟩,hpz⟩
/-- A genuine original height interval with the expected q/delta mass is
 selected directly from the original global height population. -/
theorem exists_populated_height_window (E : Finset P) (height : P → ℝ)
    {delta q K : ℝ} (hd : 0 < delta) (hq : 0 < q) (hq1 : q ≤ 1) (hK : 0 < K)
    (hbox : ∀ z ∈ E.image height, |z| ≤ 1)
    (hmass : 1 ≤ K*delta*((E.image height).card:ℝ)) :
    ∃ k ∈ (E.image height).image (fun z => ⌊z/q⌋),
      (window E height q k).Nonempty ∧
      q ≤ 4*K*delta*((window E height q k).image height).card := by
  let Z := E.image height
  let bins := Z.image (fun z => ⌊z/q⌋)
  have hZ : Z.Nonempty := by
    by_contra h
    have hz : Z.card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h)
    change 1 ≤ K*delta*(Z.card:ℝ) at hmass
    rw [hz,Nat.cast_zero,mul_zero] at hmass
    norm_num at hmass
  obtain ⟨k,hk,hmax⟩ := exists_max_image bins (fun k => (Z.filter (fun z => ⌊z/q⌋=k)).card) (hZ.image _)
  have hcount : (Z.card:ℝ) ≤ (bins.card:ℝ)*((Z.filter (fun z => ⌊z/q⌋=k)).card:ℝ) := by
    have hs : (Z.card:ℝ)=∑ j ∈ bins, ((Z.filter (fun z => ⌊z/q⌋=j)).card:ℝ) := by
      exact_mod_cast card_eq_sum_card_image (fun z : ℝ => ⌊z/q⌋) Z
    rw [hs]
    calc
      _ ≤ ∑ _j ∈ bins, ((Z.filter (fun z => ⌊z/q⌋=k)).card:ℝ) :=
        sum_le_sum (fun j hj => Nat.cast_le.mpr (hmax j hj))
      _ = _ := by simp
  have hbins : (bins.card:ℝ) ≤ 4/q := by
    have hh := scalar_interval_grid_card Z id (c := -1) hq (by norm_num : (0:ℝ)≤2)
      (fun z hz => ⟨(abs_le.mp (hbox z hz)).1,by change z ≤ -1+2; linarith [(abs_le.mp (hbox z hz)).2]⟩)
    have hi : 1 ≤ 1/q := (le_div_iff₀ hq).mpr (by simpa using hq1)
    apply hh.trans
    rw [show 2/q=2*(1/q) by ring,show 4/q=4*(1/q) by ring]
    linarith only [hi]
  have hcap := hcount.trans (mul_le_mul_of_nonneg_right hbins (Nat.cast_nonneg _))
  have hmul := mul_le_mul_of_nonneg_left hcap (mul_nonneg hK.le hd.le)
  have hm : 1 ≤ K*delta*((4/q)*((Z.filter (fun z => ⌊z/q⌋=k)).card:ℝ)) := hmass.trans hmul
  have hp := mul_le_mul_of_nonneg_right hm hq.le
  have heq : (K*delta*((4/q)*((Z.filter (fun z => ⌊z/q⌋=k)).card:ℝ)))*q=
      4*K*delta*((Z.filter (fun z => ⌊z/q⌋=k)).card:ℝ) := by field_simp
  rw [one_mul,heq] at hp
  refine ⟨k,hk,?_,?_⟩
  · obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
    obtain ⟨p,hpE,rfl⟩ := mem_image.mp hz
    exact ⟨p,mem_filter.mpr ⟨hpE,hzk⟩⟩
  · rw [actual_height_image]
    exact hp
end OriginalLiteralHeightWindow
