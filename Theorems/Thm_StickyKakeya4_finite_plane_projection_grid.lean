import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening
import Theorems.Thm_StickyKakeya4_projection_pair_slope_interval

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Finset
open scoped BigOperators

noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

/-- The explicit parameter mesh. -/
def mesh (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- All original equally spaced slopes in [0,1). -/
def slopes (n : ℕ) : Finset ℝ :=
  (Finset.range (n + 1)).image (fun k : ℕ => mesh n * k)

/-- The actual finite two-parameter projection family. -/
def parameters (n : ℕ) : Finset (ℝ × ℝ) := slopes n ×ˢ slopes n

lemma mesh_pos (n : ℕ) : 0 < mesh n := by unfold mesh; positivity

lemma slopes_card (n : ℕ) : (slopes n).card = n + 1 := by
  unfold slopes
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro i j hij
  have h := (mul_left_cancel₀ (ne_of_gt (mesh_pos n)) hij)
  exact_mod_cast h

lemma mesh_mul_slopes_card (n : ℕ) : mesh n * ((slopes n).card : ℝ) = 1 := by
  rw [slopes_card]
  simp only [mesh, Nat.cast_add, Nat.cast_one]
  field_simp

lemma slopes_card_pos (n : ℕ) : 0 < ((slopes n).card : ℝ) := by
  rw [slopes_card]
  positivity

lemma parameters_card (n : ℕ) :
    ((parameters n).card : ℝ) = ((slopes n).card : ℝ) ^ 2 := by
  simp only [parameters, Finset.card_product, Nat.cast_mul, pow_two]

lemma slope_abs_le_one {n : ℕ} {u : ℝ} (hu : u ∈ slopes n) : |u| ≤ 1 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  have hin : i < n + 1 := Finset.mem_range.mp hi
  have hic : (i : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hin.le
  have hpos := mesh_pos n
  rw [abs_of_nonneg (mul_nonneg hpos.le (Nat.cast_nonneg i))]
  calc
    mesh n * (i : ℝ) ≤ mesh n * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left hic hpos.le
    _ = 1 := by unfold mesh; field_simp

/-- Count literal slope-grid points in every real interval, with no distribution hypothesis. -/
theorem slope_interval_count (n : ℕ) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (((slopes n).filter (fun u => |u - c| ≤ r)).card : ℝ) ≤
      (2 * r + 2 * mesh n) * (slopes n).card := by
  have hsub : (slopes n).filter (fun u => |u - c| ≤ r) ⊆
      (slopes n).filter (fun u => c - r ≤ u ∧ u ≤ c - r + 2 * r) := by
    intro u hu
    obtain ⟨hs, hb⟩ := Finset.mem_filter.mp hu
    have hh := abs_le.mp hb
    exact Finset.mem_filter.mpr ⟨hs, by constructor <;> linarith⟩
  have hgrid : ∀ u ∈ slopes n, ∃ k : ℤ, u = mesh n * (k : ℝ) := by
    intro u hu
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨(i : ℤ), by simp⟩
  have hh := OriginalHeightIntervalCap.original_interval_cap_add_two
    (slopes n) (mesh_pos n) hgrid (c - r) (2 * r) (by positivity)
  calc
    _ ≤ (((slopes n).filter (fun u => c - r ≤ u ∧ u ≤ c - r + 2 * r)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ 2 * r / mesh n + 2 := hh
    _ = (2 * r + 2 * mesh n) * (slopes n).card := by
      rw [slopes_card]
      simp only [mesh, Nat.cast_add, Nat.cast_one]
      field_simp

/-- Sup norm of a concrete three-dimensional secant. -/
def distance3 (x y z : ℝ) : ℝ := max |x| (max |y| |z|)

lemma vertical_half_of_collision {x y z u v r : ℝ}
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) (hr : 0 ≤ r)
    (hfar : 4 * r ≤ distance3 x y z)
    (hx : |x - u * z| ≤ r) (hy : |y - v * z| ≤ r) :
    distance3 x y z / 2 ≤ |z| := by
  have hxx := ProjectionPairSlopeInterval.horizontal_le_radius_add_vertical hu hx
  have hyy := ProjectionPairSlopeInterval.horizontal_le_radius_add_vertical hv hy
  have hd : distance3 x y z ≤ r + |z| :=
    max_le hxx (max_le hyy (by linarith))
  linarith

lemma residual_slope_interval {x z u r d : ℝ}
    (hr : 0 ≤ r) (hd : 0 < d) (hz : d / 2 ≤ |z|)
    (hx : |x - u * z| ≤ r) :
    |u - x / z| ≤ 2 * r / d := by
  have hzpos : 0 < |z| := by linarith
  have hzne : z ≠ 0 := abs_pos.mp hzpos
  have hid : u - x / z = -(x - u * z) / z := by field_simp; ring
  calc
    |u - x / z| = |x - u * z| / |z| := by rw [hid, abs_div, abs_neg]
    _ ≤ r / |z| := div_le_div_of_nonneg_right hx hzpos.le
    _ ≤ 2 * r / d := by
      apply (div_le_div_iff₀ hzpos hd).2
      nlinarith [mul_nonneg hr (sub_nonneg.mpr hz)]

/-- The exact two-coordinate projection collision set. -/
def collisions (n : ℕ) (x y z r : ℝ) : Finset (ℝ × ℝ) :=
  (parameters n).filter (fun uv => |x - uv.1 * z| ≤ r ∧ |y - uv.2 * z| ≤ r)

/-- Concrete grid count for far secants. All small-ball parameter counts are derived. -/
theorem collision_count_far (n : ℕ) {x y z r : ℝ}
    (hr : 0 ≤ r) (hd : 0 < distance3 x y z)
    (hfar : 4 * r ≤ distance3 x y z) :
    ((collisions n x y z r).card : ℝ) ≤
      (4 * r / distance3 x y z + 2 * mesh n) ^ 2 * (parameters n).card := by
  have hm := mesh_pos n
  let d := distance3 x y z
  let U := (slopes n).filter (fun u => |u - x / z| ≤ 2 * r / d)
  let V := (slopes n).filter (fun v => |v - y / z| ≤ 2 * r / d)
  have hsub : collisions n x y z r ⊆ U ×ˢ V := by
    intro uv huv
    obtain ⟨hg, hx, hy⟩ := Finset.mem_filter.mp huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hg
    have hz := vertical_half_of_collision (slope_abs_le_one hu) (slope_abs_le_one hv)
      hr hfar hx hy
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hu, residual_slope_interval hr hd hz hx⟩,
       Finset.mem_filter.mpr ⟨hv, residual_slope_interval hr hd hz hy⟩⟩
  have hrad : 0 ≤ 2 * r / d := by dsimp [d]; positivity
  have hU := slope_interval_count n (x / z) hrad
  have hV := slope_interval_count n (y / z) hrad
  have hC : 0 ≤ (2 * (2 * r / d) + 2 * mesh n) * (slopes n).card := by positivity
  calc
    _ ≤ ((U ×ˢ V).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = (U.card : ℝ) * (V.card : ℝ) := by simp only [Finset.card_product, Nat.cast_mul]
    _ ≤ ((2 * (2 * r / d) + 2 * mesh n) * (slopes n).card) ^ 2 := by
      rw [pow_two]
      exact mul_le_mul hU hV (by positivity) hC
    _ = _ := by rw [parameters_card]; dsimp [d]; ring

/-- On the fixed bounded chart, a secant's bad-parameter fraction is at most
64 r² / d². This includes both the near and far cases and the literal mesh error. -/
theorem collision_count (n : ℕ) {x y z r : ℝ}
    (hr : mesh n ≤ r) (hd : 0 < distance3 x y z) (htop : distance3 x y z ≤ 2) :
    ((collisions n x y z r).card : ℝ) ≤
      (64 * r ^ 2 / (distance3 x y z) ^ 2) * (parameters n).card := by
  have hm := mesh_pos n
  have hrpos := hm.trans_le hr
  let d := distance3 x y z
  have hdpos : 0 < d := hd
  have hratio : 0 ≤ r / d := by positivity
  by_cases hfar : 4 * r ≤ d
  · have hh := collision_count_far n hrpos.le hd hfar
    have hmesh : 2 * mesh n ≤ 4 * r / d := by
      apply (le_div_iff₀ hdpos).2
      have h1 := mul_le_mul_of_nonneg_left htop (show 0 ≤ 2 * mesh n by positivity)
      nlinarith
    have hcoeff : (4 * r / d + 2 * mesh n) ^ 2 ≤ 64 * r ^ 2 / d ^ 2 := by
      have he : 64 * r ^ 2 / d ^ 2 = (8 * r / d) ^ 2 := by ring
      rw [he]
      have hlo : 0 ≤ 4 * r / d + 2 * mesh n := by positivity
      have hhi : 4 * r / d + 2 * mesh n ≤ 8 * r / d := by
        calc
          _ ≤ 4 * r / d + 4 * r / d := add_le_add (le_refl _) hmesh
          _ = _ := by ring
      nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))
  · have hnear : d ≤ 4 * r := le_of_not_ge hfar
    have hcoeff : 1 ≤ 64 * r ^ 2 / d ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hdpos)).2
      nlinarith [sq_nonneg (4 * r - d)]
    calc
      _ ≤ ((parameters n).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      _ = 1 * ((parameters n).card : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by positivity)

end FinitePlaneProjectionGrid
