import Mathlib.Tactic
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace OriginalHeightIntervalCap

noncomputable section
open Classical

/-- An original mesh height retains its exact integer index under division
by the original mesh spacing and the literal floor map. -/
lemma floor_original_mesh {delta z : ℝ} (hdelta : 0 < delta)
    {k : ℤ} (hz : z = delta * (k : ℝ)) : ⌊z / delta⌋ = k := by
  rw [hz]
  have hcancel : delta * (k : ℝ) / delta = (k : ℝ) := by
    field_simp
  rw [hcancel, Int.floor_intCast]

/-- The floor index is injective on the original mesh-height set. -/
lemma original_floor_injective (Z : Finset ℝ) {delta : ℝ}
    (hdelta : 0 < delta)
    (hmesh : ∀ z ∈ Z, ∃ k : ℤ, z = delta * (k : ℝ)) :
    Set.InjOn (fun z : ℝ => ⌊z / delta⌋) (↑Z) := by
  intro z hz w hw heq
  obtain ⟨k, hk⟩ := hmesh z hz
  obtain ⟨l, hl⟩ := hmesh w hw
  have hkl : k = l := by
    simpa only [floor_original_mesh hdelta hk, floor_original_mesh hdelta hl] using heq
  rw [hk, hl, hkl]

/-- Count the integer floor indices of an interval in the original mesh. -/
lemma floor_interval_card (delta c r : ℝ) (hdelta : 0 < delta) (hr : 0 ≤ r) :
    ((Finset.Icc ⌊c / delta⌋ ⌊(c + r) / delta⌋).card : ℝ) ≤ r / delta + 2 := by
  have hlohi : ⌊c / delta⌋ ≤ ⌊(c + r) / delta⌋ :=
    Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hdelta.le)
  have hc : ((Finset.Icc ⌊c / delta⌋ ⌊(c + r) / delta⌋).card : ℤ) =
      ⌊(c + r) / delta⌋ + 1 - ⌊c / delta⌋ :=
    Int.card_Icc_of_le _ _ (by omega)
  have hcast : ((Finset.Icc ⌊c / delta⌋ ⌊(c + r) / delta⌋).card : ℝ) =
      (⌊(c + r) / delta⌋ : ℝ) + 1 - (⌊c / delta⌋ : ℝ) := by
    exact_mod_cast hc
  have hh := Int.floor_le ((c + r) / delta)
  have hl := Int.lt_floor_add_one (c / delta)
  rw [hcast, add_div]
  rw [add_div] at hh
  linarith

/-- Every retained original mesh height in a real interval maps injectively
into the integer interval between its two floor indices. -/
theorem original_interval_cap_add_two (Z : Finset ℝ) {delta : ℝ}
    (hdelta : 0 < delta)
    (hmesh : ∀ z ∈ Z, ∃ k : ℤ, z = delta * (k : ℝ))
    (c r : ℝ) (hr : 0 ≤ r) :
    ((Z.filter (fun z => c ≤ z ∧ z ≤ c + r)).card : ℝ) ≤ r / delta + 2 := by
  let P := Z.filter (fun z => c ≤ z ∧ z ≤ c + r)
  let Q := Finset.Icc ⌊c / delta⌋ ⌊(c + r) / delta⌋
  have hmaps : Set.MapsTo (fun z : ℝ => ⌊z / delta⌋) (↑P) (↑Q) := by
    intro z hz
    obtain ⟨_, hzc, hzr⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_Icc.mpr
      ⟨Int.floor_mono (div_le_div_of_nonneg_right hzc hdelta.le),
        Int.floor_mono (div_le_div_of_nonneg_right hzr hdelta.le)⟩
  have hinj : Set.InjOn (fun z : ℝ => ⌊z / delta⌋) (↑P) := by
    intro z hz w hw heq
    exact original_floor_injective Z hdelta hmesh
      (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hw).1 heq
  have hcard : P.card ≤ Q.card :=
    Finset.card_le_card_of_injOn (fun z : ℝ => ⌊z / delta⌋) hmaps hinj
  exact (Nat.cast_le.mpr hcard).trans (floor_interval_card delta c r hdelta hr)

/-- The native Section 19 interval cap, with unchanged original heights.
No time-AD certificate or coarsened relabeling is required. -/
theorem original_interval_cap (Z : Finset ℝ) {delta : ℝ}
    (hdelta : 0 < delta)
    (hmesh : ∀ z ∈ Z, ∃ k : ℤ, z = delta * (k : ℝ))
    (c r : ℝ) (hr : delta ≤ r) :
    ((Z.filter (fun z => c ≤ z ∧ z ≤ c + r)).card : ℝ) ≤ 3 * r / delta := by
  have hratio : 1 ≤ r / delta := (le_div_iff₀ hdelta).mpr (by simpa using hr)
  have hcap := original_interval_cap_add_two Z hdelta hmesh c r (hdelta.le.trans hr)
  calc
    ((Z.filter (fun z => c ≤ z ∧ z ≤ c + r)).card : ℝ) ≤ r / delta + 2 := hcap
    _ ≤ 3 * r / delta := by
      have heq : 3 * r / delta = 3 * (r / delta) := by ring
      rw [heq]
      linarith

/-- Convert original-mesh density to the native growth ratio at time scale
rho squared, with the explicit interval cap H = 3 rho squared / delta. -/
theorem density_ratio {N delta rho lambda : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hdensity : lambda * rho ≤ N * delta) :
    lambda / (3 * rho) ≤ N / (3 * rho ^ 2 / delta) := by
  have hH : 0 < 3 * rho ^ 2 / delta := by positivity
  apply (le_div_iff₀ hH).mpr
  have hid : lambda / (3 * rho) * (3 * rho ^ 2 / delta) = lambda * rho / delta := by
    field_simp
  rw [hid]
  exact (div_le_iff₀ hdelta).mpr hdensity

/-- Original mesh spacing and density simultaneously supply the actual
interval cap and the resulting density-to-cap ratio. -/
theorem original_height_cap_and_ratio (Z : Finset ℝ) {N delta rho lambda : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hscale : delta ≤ rho ^ 2)
    (hmesh : ∀ z ∈ Z, ∃ k : ℤ, z = delta * (k : ℝ))
    (hdensity : lambda * rho ≤ N * delta) :
    (∀ c : ℝ, ((Z.filter (fun z => c ≤ z ∧ z ≤ c + rho ^ 2)).card : ℝ)
      ≤ 3 * rho ^ 2 / delta) ∧
    lambda / (3 * rho) ≤ N / (3 * rho ^ 2 / delta) := by
  exact ⟨fun c => original_interval_cap Z hdelta hmesh c (rho ^ 2) hscale,
    density_ratio hdelta hrho hdensity⟩

end
end OriginalHeightIntervalCap
