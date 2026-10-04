import Theorems.Thm_StickyKakeya4_finite_plane_projection_original_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Finset
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

lemma dist3_nonneg (p q : Point3) : 0 ≤ dist3 p q := by
  rw [dist3_eq_norm]
  exact norm_nonneg _

lemma dist3_coordinate_bounds (p q : Point3) :
    |p.1 - q.1| ≤ dist3 p q ∧ |p.2.1 - q.2.1| ≤ dist3 p q ∧
      |p.2.2 - q.2.2| ≤ dist3 p q := by
  dsimp [dist3, distance3]
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

lemma determinant_point_perturbation {a b x y x' y' d e : ℝ}
    (hd : 0 ≤ d) (ha : |a| ≤ d) (hb : |b| ≤ d)
    (hx : |x - x'| ≤ e) (hy : |y - y'| ≤ e) :
    |a * x - b * y| ≤ |a * x' - b * y'| + 2 * d * e := by
  have herr : |a * (x - x') - b * (y - y')| ≤ 2 * d * e := by
    calc
      _ ≤ |a * (x - x')| + |b * (y - y')| := abs_sub _ _
      _ ≤ d * e + d * e := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul ha hx (abs_nonneg _) hd)
          (mul_le_mul hb hy (abs_nonneg _) hd)
      _ = _ := by ring
  calc
    _ = |(a * x' - b * y') + (a * (x - x') - b * (y - y'))| := by congr 1; ring
    _ ≤ |a * x' - b * y'| + |a * (x - x') - b * (y - y')| := abs_add_le _ _
    _ ≤ _ := add_le_add le_rfl herr

/-- Moving the third ORIGINAL point by e changes each cross-product component
by at most 2 d e, where d is the same original secant's sup-norm length. -/
theorem crossSize_point_perturbation (p q s s' : Point3) {e : ℝ}
    (hnear : dist3 s s' ≤ e) :
    crossSize p q s ≤ crossSize p q s' + 2 * dist3 p q * e := by
  have hd := dist3_nonneg p q
  have hdir := dist3_coordinate_bounds p q
  have hdx : |q.1 - p.1| ≤ dist3 p q := by simpa only [abs_sub_comm] using hdir.1
  have hdy : |q.2.1 - p.2.1| ≤ dist3 p q := by simpa only [abs_sub_comm] using hdir.2.1
  have hdz : |q.2.2 - p.2.2| ≤ dist3 p q := by simpa only [abs_sub_comm] using hdir.2.2
  have hmove := dist3_coordinate_bounds s s'
  have hex : |(s.1 - p.1) - (s'.1 - p.1)| ≤ e := by
    simpa only [sub_sub_sub_cancel_right] using hmove.1.trans hnear
  have hey : |(s.2.1 - p.2.1) - (s'.2.1 - p.2.1)| ≤ e := by
    simpa only [sub_sub_sub_cancel_right] using hmove.2.1.trans hnear
  have hez : |(s.2.2 - p.2.2) - (s'.2.2 - p.2.2)| ≤ e := by
    simpa only [sub_sub_sub_cancel_right] using hmove.2.2.trans hnear
  have hc1 := determinant_point_perturbation hd hdy hdz hez hey
  have hc2 := determinant_point_perturbation hd hdz hdx hex hez
  have hc3 := determinant_point_perturbation hd hdx hdy hey hex
  have hb1 : |(q.2.1 - p.2.1) * (s'.2.2 - p.2.2) -
      (q.2.2 - p.2.2) * (s'.2.1 - p.2.1)| ≤ crossSize p q s' := le_max_left _ _
  have hb2 : |(q.2.2 - p.2.2) * (s'.1 - p.1) -
      (q.1 - p.1) * (s'.2.2 - p.2.2)| ≤ crossSize p q s' :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hb3 : |(q.1 - p.1) * (s'.2.1 - p.2.1) -
      (q.2.1 - p.2.1) * (s'.1 - p.1)| ≤ crossSize p q s' :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact max_le (hc1.trans (add_le_add hb1 le_rfl))
    (max_le (hc2.trans (add_le_add hb2 le_rfl)) (hc3.trans (add_le_add hb3 le_rfl)))

/-- Whole-fiber transport widens the ORIGINAL cross tube by exactly 2e. -/
lemma original_cross_tube_point_transport (p q s s' : Point3) {w e : ℝ}
    (hnear : dist3 s s' ≤ e) (hcross : crossSize p q s' ≤ w * dist3 p q) :
    crossSize p q s ≤ (w + 2 * e) * dist3 p q := by
  have hh := crossSize_point_perturbation p q s s' hnear
  nlinarith

/-- Literal original Finset membership transport, suitable for charging every
fine label in a coarse representative's height fiber. -/
theorem originalCrossTube_transport {X : Type*} (B : Finset X) (b : X → Point3)
    {i j k l : X} {w e : ℝ} (hk : k ∈ B) (hnear : dist3 (b k) (b l) ≤ e)
    (hl : l ∈ originalCrossTube B b i j w) :
    k ∈ originalCrossTube B b i j (w + 2 * e) := by
  exact Finset.mem_filter.mpr ⟨hk, original_cross_tube_point_transport (b i) (b j) (b k) (b l)
    hnear (Finset.mem_filter.mp hl).2⟩

end FinitePlaneProjectionGrid
