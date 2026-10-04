import Theorems.Thm_StickyKakeya4_finite_plane_projection_original_b

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Finset
noncomputable section
open Classical

namespace FinitePlaneProjectionGrid

lemma cross_height_component_bounds (p q s : Point3) :
    |(q.1 - p.1) * (s.2.1 - p.2.1) - (q.2.1 - p.2.1) * (s.1 - p.1)| ≤ crossSize p q s ∧
    |(q.1 - p.1) * (s.2.2 - p.2.2) - (q.2.2 - p.2.2) * (s.1 - p.1)| ≤ crossSize p q s := by
  dsimp [crossSize, distance3]
  constructor
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · rw [abs_sub_comm]
    exact (le_max_left _ _).trans (le_max_right _ _)

lemma determinant_height_bound {a b x y d w eta : ℝ}
    (hd : 0 < d) (hb : d ≤ |b|) (ha : |a| ≤ eta * d) (hy : |y| ≤ 2)
    (hcross : |a * y - b * x| ≤ w * d) : |x| ≤ w + 2 * eta := by
  have hprod : |b| * |x| ≤ w * d + (eta * d) * 2 := by
    calc
      _ = |b * x| := (abs_mul _ _).symm
      _ = |a * y - (a * y - b * x)| := by congr 1; ring
      _ ≤ |a * y| + |a * y - b * x| := abs_sub _ _
      _ ≤ (eta * d) * 2 + w * d := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul ha hy (abs_nonneg _) (by linarith [abs_nonneg a])) hcross
      _ = _ := by ring
  have hlow := mul_le_mul_of_nonneg_right hb (abs_nonneg x)
  nlinarith

lemma determinant_affine_bound {a b x y d w eta : ℝ}
    (hd : 0 < d) (heta : 0 < eta) (hw : 0 ≤ w) (ha : eta * d ≤ |a|)
    (hcross : |a * y - b * x| ≤ w * d) : |y - (b / a) * x| ≤ w / eta := by
  have haabs : 0 < |a| := (mul_pos heta hd).trans_le ha
  have ha0 : a ≠ 0 := abs_pos.mp haabs
  have he : y - (b / a) * x = (a * y - b * x) / a := by field_simp
  rw [he, abs_div]
  apply (div_le_iff₀ haabs).2
  have hratio : w * d ≤ w / eta * |a| := by
    have hm := mul_le_mul_of_nonneg_left ha hw
    have hdiv := div_le_div_of_nonneg_right hm heta.le
    have hcancel : w * (eta * d) / eta = w * d := by field_simp
    rw [hcancel] at hdiv
    calc
      _ ≤ w * |a| / eta := hdiv
      _ = _ := by ring
  exact hcross.trans hratio

/-- A near-vertical ORIGINAL secant controls heights. Otherwise its ORIGINAL
cross tube is an ordinary affine graph-deviation tube over the height axis. -/
theorem original_cross_tube_dichotomy (p q s : Point3) {w eta : ℝ}
    (hd : 0 < dist3 p q) (hw : 0 ≤ w) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hp : |p.2.1| ≤ 1 ∧ |p.2.2| ≤ 1) (hs : |s.2.1| ≤ 1 ∧ |s.2.2| ≤ 1)
    (hcross : crossSize p q s ≤ w * dist3 p q) :
    (|(q.1 - p.1)| < eta * dist3 p q → |s.1 - p.1| ≤ w + 2 * eta) ∧
    (eta * dist3 p q ≤ |q.1 - p.1| →
      |s.2.1 - p.2.1 - ((q.2.1 - p.2.1) / (q.1 - p.1)) * (s.1 - p.1)| ≤ w / eta ∧
      |s.2.2 - p.2.2 - ((q.2.2 - p.2.2) / (q.1 - p.1)) * (s.1 - p.1)| ≤ w / eta) := by
  have hc := cross_height_component_bounds p q s
  have hc1 := hc.1.trans hcross
  have hc2 := hc.2.trans hcross
  have hdrev : dist3 p q = max |q.1 - p.1| (max |q.2.1 - p.2.1| |q.2.2 - p.2.2|) := by
    simp only [dist3, distance3, abs_sub_comm]
  constructor
  · intro hnear
    have hsmall : |q.1 - p.1| < dist3 p q := by nlinarith
    have hmax : dist3 p q ≤ max |q.2.1 - p.2.1| |q.2.2 - p.2.2| := by
      rcases (le_max_iff.mp (le_of_eq hdrev)) with hbad | hgood
      · exact (not_le_of_gt hsmall hbad).elim
      · exact hgood
    have hy : |s.2.1 - p.2.1| ≤ 2 := (abs_sub _ _).trans (by linarith [hp.1, hs.1])
    have hz : |s.2.2 - p.2.2| ≤ 2 := (abs_sub _ _).trans (by linarith [hp.2, hs.2])
    rcases le_max_iff.mp hmax with hdy | hdz
    · exact determinant_height_bound hd hdy hnear.le hy hc1
    · exact determinant_height_bound hd hdz hnear.le hz hc2
  · intro hfar
    exact ⟨determinant_affine_bound hd heta hw hfar hc1,
      determinant_affine_bound hd heta hw hfar hc2⟩

/-- Actual original affine graph tube over the original height coordinate. -/
def originalAffineGraphTube {X : Type*} (B : Finset X) (b : X → Point3)
    (a1 a2 c1 c2 w : ℝ) : Finset X :=
  B.filter (fun k => |(b k).2.1 - a1 * (b k).1 - c1| ≤ w ∧
    |(b k).2.2 - a2 * (b k).1 - c2| ≤ w)

/-- ORIGINAL height-interval counts and ORIGINAL affine-deviation counts imply
precisely the cross-tube premise used in the common projection theorem. -/
theorem originalCrossTube_card_of_height_affine_caps {X : Type*}
    (B : Finset X) (b : X → Point3) {w eta kappa epsilon : ℝ}
    (hw : 0 ≤ w) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hbounded : ∀ k ∈ B, |(b k).2.1| ≤ 1 ∧ |(b k).2.2| ≤ 1)
    (hheight : ∀ c : ℝ,
      ((B.filter (fun k => |(b k).1 - c| ≤ w + 2 * eta)).card : ℝ) ≤ kappa * B.card)
    (haffine : ∀ a1 a2 c1 c2 : ℝ,
      ((originalAffineGraphTube B b a1 a2 c1 c2 (w / eta)).card : ℝ) ≤ epsilon * B.card)
    {i j : X} (hi : i ∈ B) (_hj : j ∈ B) (hd : 0 < dist3 (b i) (b j)) :
    ((originalCrossTube B b i j w).card : ℝ) ≤ max kappa epsilon * B.card := by
  by_cases hnear : |(b j).1 - (b i).1| < eta * dist3 (b i) (b j)
  · have hsub : originalCrossTube B b i j w ⊆
        B.filter (fun k => |(b k).1 - (b i).1| ≤ w + 2 * eta) := by
      intro k hk
      obtain ⟨hkB, hkc⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hkB,
        (original_cross_tube_dichotomy (b i) (b j) (b k) hd hw heta heta1
          (hbounded i hi) (hbounded k hkB) hkc).1 hnear⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((hheight _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  · let a1 := ((b j).2.1 - (b i).2.1) / ((b j).1 - (b i).1)
    let a2 := ((b j).2.2 - (b i).2.2) / ((b j).1 - (b i).1)
    let c1 := (b i).2.1 - a1 * (b i).1
    let c2 := (b i).2.2 - a2 * (b i).1
    have hsub : originalCrossTube B b i j w ⊆
        originalAffineGraphTube B b a1 a2 c1 c2 (w / eta) := by
      intro k hk
      obtain ⟨hkB, hkc⟩ := Finset.mem_filter.mp hk
      have hh := (original_cross_tube_dichotomy (b i) (b j) (b k) hd hw heta heta1
        (hbounded i hi) (hbounded k hkB) hkc).2 (le_of_not_gt hnear)
      refine Finset.mem_filter.mpr ⟨hkB, ?_, ?_⟩
      · convert hh.1 using 1
        dsimp [a1, c1]
        congr 1
        ring
      · convert hh.2 using 1
        dsimp [a2, c2]
        congr 1
        ring
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      ((haffine a1 a2 c1 c2).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))

end FinitePlaneProjectionGrid
