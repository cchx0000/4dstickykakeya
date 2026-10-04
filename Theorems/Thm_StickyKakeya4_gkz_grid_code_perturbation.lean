import Theorems.Thm_StickyKakeya4_gkz_original_ratio_gap
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZGridCodePerturbation
open ActualRoundedAdditiveEnergy NativeTangentGridCoarsening

/-- Actual original values close to integer codes have an explicit occupied
floor-image bound in terms of those literal codes. -/
theorem floor_image_le_code_image {X : Type*} (P : Finset X)
    (value : X → ℝ) (code : X → ℤ) {delta E : ℝ}
    (hd : 0 < delta) (hE : 0 ≤ E)
    (herr : ∀ p∈P, |value p-delta*(code p:ℝ)| ≤ E*delta) :
    ((P.image (fun p => rounded delta (value p))).card : ℝ) ≤
      (2*E+2)*(P.image code).card := by
  apply image_card_le_real_mul_of_fiber_images P
    (fun p => rounded delta (value p)) code (2*E+2)
  intro z _
  apply scalar_centered_grid_card _ value (c := delta*(z:ℝ)) hd hE
  intro p hp
  obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
  simpa only [hc] using herr p hp

/-- The reverse comparison also keeps all original codes and the full floor
error. It is useful for rounded self-sums and signed dilates. -/
theorem code_image_le_floor_image {X : Type*} (P : Finset X)
    (value : X → ℝ) (code : X → ℤ) {delta E : ℝ}
    (hd : 0 < delta) (hE : 0 ≤ E)
    (herr : ∀ p∈P, |value p-delta*(code p:ℝ)| ≤ E*delta) :
    ((P.image code).card : ℝ) ≤
      (2*E+4)*(P.image (fun p => rounded delta (value p))).card := by
  apply image_card_le_real_mul_of_fiber_images P code
    (fun p => rounded delta (value p)) (2*E+4)
  intro j _
  let D := (P.filter (fun p => rounded delta (value p)=j)).image code
  have hgrid (z : ℤ) : ⌊(delta*(z:ℝ))/delta⌋=z := by
    have he : (delta*(z:ℝ))/delta=(z:ℝ) := by field_simp
    rw [he, Int.floor_intCast]
  apply (scalar_injective_grid_centered_card D (fun z => delta*(z:ℝ))
    (r := delta) (R := E+1) (c := delta*(j:ℝ)) hd (by linarith) ?_ ?_).trans (by linarith)
  · intro z _ w _ hzw
    simpa only [hgrid] using hzw
  · intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
    have he := herr p hp
    have hr := round_error hd (value p)
    rw [hc] at hr
    have hr' : |value p-delta*(j:ℝ)| ≤ delta :=
      (abs_of_nonneg hr.1).le.trans hr.2.le
    have he' : |delta*(code p:ℝ)-value p| ≤ E*delta := by
      simpa only [abs_sub_comm] using he
    exact (abs_sub_le (delta*(code p:ℝ)) (value p) (delta*(j:ℝ))).trans (by linarith)

/-- Bounded real dilation increases an actual occupied mesh cover only by
the explicit one-dimensional packing factor. -/
theorem bounded_dilation_floor_image {X : Type*} (P : Finset X) (value : X → ℝ)
    {delta a L : ℝ} (hd : 0 < delta) (hL : 0 ≤ L) (ha : |a| ≤ L) :
    ((P.image (fun p => rounded delta (a*value p))).card : ℝ) ≤
      (2*L+2)*(P.image (fun p => rounded delta (value p))).card := by
  apply image_card_le_real_mul_of_fiber_images P
    (fun p => rounded delta (a*value p)) (fun p => rounded delta (value p)) (2*L+2)
  intro j _
  apply scalar_centered_grid_card _ (fun p => a*value p) (c := a*(delta*(j:ℝ))) hd hL
  intro p hp
  obtain ⟨_, hc⟩ := Finset.mem_filter.mp hp
  have hr := round_error hd (value p)
  rw [hc] at hr
  have hr' : |value p-delta*(j:ℝ)| ≤ delta :=
    (abs_of_nonneg hr.1).le.trans hr.2.le
  have hm := mul_le_mul ha hr' (abs_nonneg _) hL
  have hid : a*value p-a*(delta*(j:ℝ))=a*(value p-delta*(j:ℝ)) := by ring
  simpa only [hid, abs_mul] using hm

end GKZGridCodePerturbation
