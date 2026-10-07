import Theorems.Thm_StickyKakeya4_native_configured_time_coarsening
import Theorems.Thm_StickyKakeya4_original_separated_height_cap
import Theorems.Thm_StickyKakeya4_height_graph_residue_separation

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

noncomputable section
namespace NativeConfiguredHeightCaps
open Classical Finset NativeConfiguredTimeCoarsening SeparatedAlignmentPatches

/-- Actual midpoint heights retain their translation. Only their
difference is used in the already proved separated-height count. -/
theorem finalTime_gap (delta : ℝ) (hd : 0 < delta) (q : ℕ) (hq : 0 < q)
    (a b : ℤ) (hmod : a%(q:ℤ)=b%(q:ℤ)) (hne : a≠b) :
    (delta/512)*(q:ℝ) ≤ |finalTime delta a-finalTime delta b| := by
  have hh := real_residue_spacing hq hmod hne
  have he : |finalTime delta a-finalTime delta b| = (delta/512)*|(a:ℝ)-(b:ℝ)| := by
    unfold finalTime
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < delta/512)]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

theorem time_image_separation (H : Finset ℤ) (delta : ℝ) (hd : 0 < delta)
    (q : ℕ) (hq : 0 < q) (hres : ∀ a∈H, ∀ b∈H, a%(q:ℤ)=b%(q:ℤ)) :
    ∀ z∈H.image (finalTime delta), ∀ w∈H.image (finalTime delta), z≠w →
      (delta/512)*(q:ℝ) ≤ |z-w| := by
  intro z hz w hw hzw
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
  obtain ⟨b, hb, rfl⟩ := mem_image.mp hw
  exact finalTime_gap delta hd q hq a b (hres a ha b hb) (fun he => hzw (congrArg _ he))

/-- Literal final midpoint heights supply the interval cap. q=1 is the
unconditional mesh; a retained global q=8 color supplies the output-tube
mesh without moving any point or dropping the affine time offset. -/
theorem time_image_interval_cap (H : Finset ℤ) (delta : ℝ) (hd : 0 < delta)
    (q : ℕ) (hq : 0 < q) (hres : ∀ a∈H, ∀ b∈H, a%(q:ℤ)=b%(q:ℤ))
    (c r : ℝ) (hr : 0 ≤ r) :
    (((H.image (finalTime delta)).filter (fun z => c≤z ∧ z≤c+r)).card:ℝ) ≤
      r/((delta/512)*(q:ℝ))+2 := by
  exact OriginalSeparatedHeightCap.separated_interval_cap _ (by positivity)
    (time_image_separation H delta hd q hq hres) c r hr

theorem unconditional_interval_cap (H : Finset ℤ) (delta : ℝ) (hd : 0 < delta)
    (c r : ℝ) (hr : 0 ≤ r) :
    (((H.image (finalTime delta)).filter (fun z => c≤z ∧ z≤c+r)).card:ℝ) ≤
      r/(delta/512)+2 := by
  simpa only [Nat.cast_one, mul_one] using time_image_interval_cap H delta hd 1
    (by decide) (by intro a _ b _; simp) c r hr

theorem residue_eight_interval_cap (H : Finset ℤ) (delta : ℝ) (hd : 0 < delta)
    (hres : ∀ a∈H, ∀ b∈H, a%8=b%8) (c r : ℝ) (hr : 0 ≤ r) :
    (((H.image (finalTime delta)).filter (fun z => c≤z ∧ z≤c+r)).card:ℝ) ≤
      r/(delta/64)+2 := by
  have he : (delta/512)*(8:ℝ)=delta/64 := by ring
  simpa only [Nat.cast_ofNat, he] using time_image_interval_cap H delta hd 8
    (by decide) hres c r hr

end NativeConfiguredHeightCaps
