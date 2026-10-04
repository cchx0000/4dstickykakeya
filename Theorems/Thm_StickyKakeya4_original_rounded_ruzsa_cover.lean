import Theorems.Thm_StickyKakeya4_gkz_dilate_rounded_sums
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical
open scoped Pointwise

namespace OriginalRoundedRuzsaCover
open ActualRoundedAdditiveEnergy GKZGridCodePerturbation GKZDilateRoundedSums

def cells (delta : ℝ) (X : Finset ℝ) : Finset ℤ := X.image (rounded delta)

lemma sum_cells_product (delta : ℝ) (X Y : Finset ℝ) :
    cells delta (X+Y)=(X.product Y).image (fun p => rounded delta (p.1+p.2)) := by
  have he : X+Y=(X.product Y).image (fun p => p.1+p.2) := by
    simpa only [Finset.image_id'] using image_add_image X Y (fun x => x) (fun y => y)
  unfold cells
  rw [he,Finset.image_image]
  rfl

lemma sub_cells_product (delta : ℝ) (X Y : Finset ℝ) :
    cells delta (X-Y)=(X.product Y).image (fun p => rounded delta (p.1-p.2)) := by
  have he : X-Y=(X.product Y).image (fun p => p.1-p.2) := by
    simpa only [Finset.image_id'] using image_sub_image X Y (fun x => x) (fun y => y)
  unfold cells
  rw [he,Finset.image_image]
  rfl

private lemma sum_round_error {delta : ℝ} (hd : 0 < delta) (x y : ℝ) :
    |x+y-delta*((rounded delta x+rounded delta y:ℤ):ℝ)| ≤ 2*delta := by
  have hx := round_error hd x
  have hy := round_error hd y
  have he : x+y-delta*((rounded delta x+rounded delta y:ℤ):ℝ)=
      (x-delta*(rounded delta x:ℝ))+(y-delta*(rounded delta y:ℝ)) := by push_cast; ring
  rw [he,abs_of_nonneg (by linarith only [hx.1,hy.1])]
  linarith only [hx.2,hy.2]

private lemma sub_round_error {delta : ℝ} (hd : 0 < delta) (x y : ℝ) :
    |x-y-delta*((rounded delta x-rounded delta y:ℤ):ℝ)| ≤ 1*delta := by
  have hx := round_error hd x
  have hy := round_error hd y
  have he : x-y-delta*((rounded delta x-rounded delta y:ℤ):ℝ)=
      (x-delta*(rounded delta x:ℝ))-(y-delta*(rounded delta y:ℝ)) := by push_cast; ring
  rw [he,one_mul]
  exact abs_le.mpr ⟨by linarith only [hx.1,hy.2],by linarith only [hx.2,hy.1]⟩

/-- Actual sum covers and integer sum codes differ by only the full proved
rounding-error factors. No exact floor-addition identity is used. -/
theorem sum_rounding_comparison (X Y : Finset ℝ) {delta : ℝ} (hd : 0 < delta) :
    ((cells delta X+cells delta Y).card:ℝ) ≤ 8*(cells delta (X+Y)).card ∧
      ((cells delta (X+Y)).card:ℝ) ≤ 6*(cells delta X+cells delta Y).card := by
  have hI : cells delta X+cells delta Y=(X.product Y).image
      (fun p => rounded delta p.1+rounded delta p.2) := image_add_image X Y _ _
  have hcode := code_image_le_floor_image (X.product Y) (fun p => p.1+p.2)
    (fun p => rounded delta p.1+rounded delta p.2) hd (by norm_num : (0:ℝ) ≤ 2)
    (fun p _hp => sum_round_error hd p.1 p.2)
  have hfloor := floor_image_le_code_image (X.product Y) (fun p => p.1+p.2)
    (fun p => rounded delta p.1+rounded delta p.2) hd (by norm_num : (0:ℝ) ≤ 2)
    (fun p _hp => sum_round_error hd p.1 p.2)
  norm_num only at hcode hfloor
  rw [hI,sum_cells_product]
  exact ⟨hcode,hfloor⟩

/-- Actual differences retain their own rounding error; negation is never
silently identified with floor-code negation. -/
theorem sub_rounding_comparison (X Y : Finset ℝ) {delta : ℝ} (hd : 0 < delta) :
    ((cells delta X-cells delta Y).card:ℝ) ≤ 6*(cells delta (X-Y)).card ∧
      ((cells delta (X-Y)).card:ℝ) ≤ 4*(cells delta X-cells delta Y).card := by
  have hI : cells delta X-cells delta Y=(X.product Y).image
      (fun p => rounded delta p.1-rounded delta p.2) := image_sub_image X Y _ _
  have hcode := code_image_le_floor_image (X.product Y) (fun p => p.1-p.2)
    (fun p => rounded delta p.1-rounded delta p.2) hd (by norm_num : (0:ℝ) ≤ 1)
    (fun p _hp => sub_round_error hd p.1 p.2)
  have hfloor := floor_image_le_code_image (X.product Y) (fun p => p.1-p.2)
    (fun p => rounded delta p.1-rounded delta p.2) hd (by norm_num : (0:ℝ) ≤ 1)
    (fun p _hp => sub_round_error hd p.1 p.2)
  norm_num only at hcode hfloor
  rw [hI,sub_cells_product]
  exact ⟨hcode,hfloor⟩

/-- A genuine rounded-cover all-add Ruzsa inequality, derived from mathlib's
proved finite Plunnecke/Ruzsa theorem and the actual original rounding maps. -/
theorem original_rounded_sum_triangle (X Y Z : Finset ℝ) {delta : ℝ} (hd : 0 < delta) :
    ((cells delta (X+Z)).card:ℝ)*(cells delta Y).card ≤
      384*((cells delta (X+Y)).card:ℝ)*(cells delta (Y+Z)).card := by
  have hXZ := (sum_rounding_comparison X Z hd).2
  have hXY := (sum_rounding_comparison X Y hd).1
  have hYZ := (sum_rounding_comparison Y Z hd).1
  have hRT : ((cells delta X+cells delta Z).card:ℝ)*(cells delta Y).card ≤
      ((cells delta X+cells delta Y).card:ℝ)*(cells delta Y+cells delta Z).card := by
    exact_mod_cast Finset.ruzsa_triangle_inequality_add_add_add (cells delta X) (cells delta Y) (cells delta Z)
  have hprod := mul_le_mul hXY hYZ (Nat.cast_nonneg _)
    (show 0 ≤ 8*((cells delta (X+Y)).card:ℝ) by positivity)
  have h1 := mul_le_mul_of_nonneg_right hXZ (show (0:ℝ) ≤ (cells delta Y).card from Nat.cast_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hRT (by norm_num : (0:ℝ) ≤ 6)
  have h3 := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ) ≤ 6)
  nlinarith only [h1,h2,h3]

/-- The original difference-cover form needed for signed polynomial words. -/
theorem original_rounded_sub_sum_triangle (X Y Z : Finset ℝ) {delta : ℝ} (hd : 0 < delta) :
    ((cells delta (X-Z)).card:ℝ)*(cells delta Y).card ≤
      256*((cells delta (X+Y)).card:ℝ)*(cells delta (Z+Y)).card := by
  have hXZ := (sub_rounding_comparison X Z hd).2
  have hXY := (sum_rounding_comparison X Y hd).1
  have hZY := (sum_rounding_comparison Z Y hd).1
  have hRT : ((cells delta X-cells delta Z).card:ℝ)*(cells delta Y).card ≤
      ((cells delta X+cells delta Y).card:ℝ)*(cells delta Z+cells delta Y).card := by
    exact_mod_cast Finset.ruzsa_triangle_inequality_sub_add_add (cells delta X) (cells delta Y) (cells delta Z)
  have hprod := mul_le_mul hXY hZY (Nat.cast_nonneg _)
    (show 0 ≤ 8*((cells delta (X+Y)).card:ℝ) by positivity)
  have h1 := mul_le_mul_of_nonneg_right hXZ (show (0:ℝ) ≤ (cells delta Y).card from Nat.cast_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hRT (by norm_num : (0:ℝ) ≤ 4)
  have h3 := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ) ≤ 4)
  nlinarith only [h1,h2,h3]

end OriginalRoundedRuzsaCover
