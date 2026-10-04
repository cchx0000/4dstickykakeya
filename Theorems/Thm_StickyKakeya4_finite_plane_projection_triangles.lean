import Theorems.Thm_StickyKakeya4_finite_plane_projection_grid

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Finset
open scoped BigOperators
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

lemma product_filter_card_sum (S T : Finset ℝ) (p : ℝ × ℝ → Prop) :
    (((S ×ˢ T).filter p).card : ℝ) =
      ∑ u ∈ S, ((T.filter (fun v => p (u, v))).card : ℝ) := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma scalar_affine_count (n : ℕ) {a c r : ℝ} (ha : a ≠ 0) (hr : 0 ≤ r) :
    (((slopes n).filter (fun u => |c + u * a| ≤ r)).card : ℝ) ≤
      (2 * r / |a| + 2 * mesh n) * (slopes n).card := by
  have hap : 0 < |a| := abs_pos.mpr ha
  have hsub : (slopes n).filter (fun u => |c + u * a| ≤ r) ⊆
      (slopes n).filter (fun u => |u - (-c / a)| ≤ r / |a|) := by
    intro u hu
    obtain ⟨hs, h⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨hs, ?_⟩
    have hid : u - (-c / a) = (c + u * a) / a := by field_simp; ring
    rw [hid, abs_div]
    exact div_le_div_of_nonneg_right h hap.le
  calc
    _ ≤ (((slopes n).filter (fun u => |u - (-c / a)| ≤ r / |a|)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ (2 * (r / |a|) + 2 * mesh n) * (slopes n).card :=
      slope_interval_count n (-c / a) (div_nonneg hr hap.le)
    _ = _ := by ring

/-- Actual affine-determinant small-value parameters. -/
def strips (n : ℕ) (a b c r : ℝ) : Finset (ℝ × ℝ) :=
  (parameters n).filter (fun uv => |c + uv.1 * a + uv.2 * b| ≤ r)

lemma affine_strip_count_second (n : ℕ) {a b c r : ℝ}
    (hb : b ≠ 0) (hr : 0 ≤ r) :
    ((strips n a b c r).card : ℝ) ≤
      (2 * r / |b| + 2 * mesh n) * (parameters n).card := by
  unfold strips parameters
  rw [product_filter_card_sum]
  calc
    _ ≤ ∑ _u ∈ slopes n, (2 * r / |b| + 2 * mesh n) * (slopes n).card := by
      exact Finset.sum_le_sum (fun u _hu => scalar_affine_count n (a := b) (c := c + u * a) (r := r) hb hr)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product,
        Nat.cast_mul]; ring

lemma product_filter_card_sum_right (S T : Finset ℝ) (p : ℝ × ℝ → Prop) :
    (((S ×ˢ T).filter p).card : ℝ) =
      ∑ v ∈ T, ((S.filter (fun u => p (u, v))).card : ℝ) := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma affine_strip_count_first (n : ℕ) {a b c r : ℝ}
    (ha : a ≠ 0) (hr : 0 ≤ r) :
    ((strips n a b c r).card : ℝ) ≤
      (2 * r / |a| + 2 * mesh n) * (parameters n).card := by
  unfold strips parameters
  rw [product_filter_card_sum_right]
  have he (u v : ℝ) : c + u * a + v * b = (c + v * b) + u * a := by ring
  simp_rw [he]
  calc
    _ ≤ ∑ _v ∈ slopes n, (2 * r / |a| + 2 * mesh n) * (slopes n).card := by
      exact Finset.sum_le_sum (fun v _hv => scalar_affine_count n (a := a) (c := c + v * b) (r := r) ha hr)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_product,
        Nat.cast_mul]; ring

lemma constant_bound_of_strip {a b c u v r : ℝ}
    (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (h : |c + u * a + v * b| ≤ r) :
    |c| ≤ r + |a| + |b| := by
  have hid : c = (c + u * a + v * b) + (-(u * a) - v * b) := by ring
  calc
    |c| = |(c + u * a + v * b) + (-(u * a) - v * b)| := congrArg abs hid
    _ ≤ |c + u * a + v * b| + |-(u * a) - v * b| := abs_add_le _ _
    _ ≤ r + (|u * a| + |v * b|) := by
      exact add_le_add h (by simpa only [abs_neg] using abs_sub (-(u * a)) (v * b))
    _ ≤ r + (1 * |a| + 1 * |b|) := by
      rw [abs_mul, abs_mul]
      exact add_le_add (le_refl r) (add_le_add
        (mul_le_mul_of_nonneg_right hu (abs_nonneg a))
        (mul_le_mul_of_nonneg_right hv (abs_nonneg b)))
    _ = _ := by ring

/-- A nonzero constant term cannot create a thin strip when both gradient
components are too small. This is the needed empty-case argument. -/
lemma strip_large_gradient {a b c u v r A : ℝ}
    (hA : 0 < A) (hr : r ≤ A / 2) (hcross : A ≤ distance3 a b c)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (h : |c + u * a + v * b| ≤ r) :
    A / 4 ≤ |a| ∨ A / 4 ≤ |b| := by
  by_contra hnot
  have ha : |a| < A / 4 := lt_of_not_ge (fun hh => hnot (Or.inl hh))
  have hb : |b| < A / 4 := lt_of_not_ge (fun hh => hnot (Or.inr hh))
  have hc := constant_bound_of_strip hu hv h
  have hclt : |c| < A := by linarith
  have hmax : distance3 a b c < A :=
    max_lt (by linarith) (max_lt (by linarith) hclt)
  linarith

/-- Finite strip-grid counting for the actual affine projected area.
The upper bound includes all constants, arbitrary strip positions, and the mesh error. -/
theorem affine_strip_count (n : ℕ) {a b c r A : ℝ}
    (hr : 0 ≤ r) (hA : 0 < A) (hcross : A ≤ distance3 a b c) :
    ((strips n a b c r).card : ℝ) ≤
      (8 * r / A + 2 * mesh n) * (parameters n).card := by
  have hm := mesh_pos n
  by_cases hsmall : r ≤ A / 2
  · by_cases hempty : (strips n a b c r).Nonempty
    · obtain ⟨uv, huv⟩ := hempty
      obtain ⟨hg, hs⟩ := Finset.mem_filter.mp huv
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp hg
      have hgrad := strip_large_gradient hA hsmall hcross
        (slope_abs_le_one hu) (slope_abs_le_one hv) hs
      have hcoef : ∀ d : ℝ, A / 4 ≤ |d| →
          2 * r / |d| + 2 * mesh n ≤ 8 * r / A + 2 * mesh n := by
        intro d hd
        have hdp : 0 < |d| := by linarith
        apply add_le_add _ (le_refl _)
        apply (div_le_div_iff₀ hdp hA).2
        nlinarith [mul_nonneg hr (sub_nonneg.mpr hd)]
      rcases hgrad with ha | hb
      · have hane : a ≠ 0 := abs_pos.mp (by linarith)
        exact (affine_strip_count_first n hane hr).trans
          (mul_le_mul_of_nonneg_right (hcoef a ha) (by positivity))
      · have hbne : b ≠ 0 := abs_pos.mp (by linarith)
        exact (affine_strip_count_second n hbne hr).trans
          (mul_le_mul_of_nonneg_right (hcoef b hb) (by positivity))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  · have hrlarge : A / 2 ≤ r := le_of_not_ge hsmall
    have hcoef : 1 ≤ 8 * r / A + 2 * mesh n := by
      have hh : 4 ≤ 8 * r / A := (le_div_iff₀ hA).2 (by linarith)
      linarith
    calc
      _ ≤ ((parameters n).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      _ = 1 * ((parameters n).card : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- Actual determinant of the two projected secants, equal to an affine
function with the three original cross-product coordinates. -/
theorem projected_determinant_identity (x y z x' y' z' u v : ℝ) :
    (x - u * z) * (y' - v * z') - (y - v * z) * (x' - u * z') =
      (x * y' - y * x') + u * (y * z' - z * y') + v * (z * x' - x * z') := by
  ring

/-- The actual projected-triangle estimate, with no assumed projection certificate. -/
theorem projected_triangle_count (n : ℕ) {x y z x' y' z' r A : ℝ}
    (hr : 0 ≤ r) (hA : 0 < A)
    (hcross : A ≤ distance3 (y * z' - z * y') (z * x' - x * z') (x * y' - y * x')) :
    (((parameters n).filter (fun uv =>
      |(x - uv.1 * z) * (y' - uv.2 * z') -
        (y - uv.2 * z) * (x' - uv.1 * z')| ≤ r)).card : ℝ) ≤
      (8 * r / A + 2 * mesh n) * (parameters n).card := by
  simp_rw [projected_determinant_identity]
  exact affine_strip_count n hr hA hcross

end FinitePlaneProjectionGrid
