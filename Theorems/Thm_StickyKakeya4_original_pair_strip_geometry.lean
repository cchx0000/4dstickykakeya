import Theorems.Thm_StickyKakeya4_planar_strip_intersection

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

noncomputable section
namespace OriginalPairStripGeometry
open PlanarStripIntersection

abbrev Point := ℝ × ℝ
abbrev Pair := Point × Point

def scale (z : Pair) : ℝ := boxDistance z.1 z.2
def normalX (z : Pair) : ℝ := -(z.2.2-z.1.2)/scale z
def normalY (z : Pair) : ℝ := (z.2.1-z.1.1)/scale z
def offset (z : Pair) : ℝ := normalX z*z.1.1+normalY z*z.1.2

theorem scale_pos (z : Pair) (hne : z.1≠z.2) : 0<scale z := by
  by_contra h
  have hm : max |z.2.1-z.1.1| |z.2.2-z.1.2|≤0 := le_of_not_gt h
  have hx : |z.2.1-z.1.1|=0 := le_antisymm ((le_max_left _ _).trans hm) (abs_nonneg _)
  have hy : |z.2.2-z.1.2|=0 := le_antisymm ((le_max_right _ _).trans hm) (abs_nonneg _)
  exact hne (Prod.ext (sub_eq_zero.mp (abs_eq_zero.mp hx)).symm
    (sub_eq_zero.mp (abs_eq_zero.mp hy)).symm)

/-- The normal comes from the actual ordered pair direction; no cell center
or independent angular representative is introduced. -/
theorem original_pair_normalized (z : Pair) (hne : z.1≠z.2) :
    |normalX z|≤1 ∧ |normalY z|≤1 ∧ (|normalX z|=1 ∨ |normalY z|=1) := by
  have hs := scale_pos z hne
  have hx : |normalX z|=|z.2.2-z.1.2|/scale z := by
    simp only [normalX,abs_div,abs_neg,abs_of_pos hs]
  have hy : |normalY z|=|z.2.1-z.1.1|/scale z := by
    simp only [normalY,abs_div,abs_of_pos hs]
  have hbx : |normalX z|≤1 := by
    rw [hx]
    apply (div_le_iff₀ hs).mpr
    simpa only [one_mul,scale,boxDistance] using (le_max_right |z.2.1-z.1.1| |z.2.2-z.1.2|)
  have hby : |normalY z|≤1 := by
    rw [hy]
    apply (div_le_iff₀ hs).mpr
    simpa only [one_mul,scale,boxDistance] using (le_max_left |z.2.1-z.1.1| |z.2.2-z.1.2|)
  refine ⟨hbx,hby,?_⟩
  rcases le_total |z.2.1-z.1.1| |z.2.2-z.1.2| with h|h
  · left
    rw [hx]
    have heq : scale z=|z.2.2-z.1.2| := max_eq_right h
    rw [← heq]
    exact div_self (ne_of_gt hs)
  · right
    rw [hy]
    have heq : scale z=|z.2.1-z.1.1| := max_eq_left h
    rw [← heq]
    exact div_self (ne_of_gt hs)

theorem original_pair_on_line (z : Pair) :
    PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) z.1=0 ∧
    PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) z.2=0 := by
  constructor
  · unfold PlanarStripIntersection.residual offset
    ring
  · unfold PlanarStripIntersection.residual offset normalX normalY
    simp only [div_eq_mul_inv]
    ring

def linePoint (z : Pair) (t : ℝ) : Point :=
  (z.1.1+t*(z.2.1-z.1.1),z.1.2+t*(z.2.2-z.1.2))

theorem affine_pair_line_residual (z : Pair) (t : ℝ) :
    PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) (linePoint z t)=0 := by
  unfold PlanarStripIntersection.residual offset normalX normalY linePoint
  simp only [div_eq_mul_inv]
  ring

/-- A genuine bounded-distance witness to the original pair line lies in
the normalized strip of twice that width. This records the fixed physical
width conversion explicitly. -/
theorem near_original_pair_line
    (z : Pair) (hne : z.1≠z.2) (p : Point) (t delta : ℝ)
    (hx : |p.1-(linePoint z t).1|≤delta)
    (hy : |p.2-(linePoint z t).2|≤delta) :
    |PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) p|≤2*delta := by
  have hn := original_pair_normalized z hne
  have hzero := affine_pair_line_residual z t
  have heq : PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) p =
      normalX z*(p.1-(linePoint z t).1)+normalY z*(p.2-(linePoint z t).2) := by
    unfold PlanarStripIntersection.residual at hzero ⊢
    nlinarith only [hzero]
  have h1 := mul_le_mul hn.1 hx (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h2 := mul_le_mul hn.2.1 hy (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  rw [heq]
  have h := abs_add_le (normalX z*(p.1-(linePoint z t).1))
    (normalY z*(p.2-(linePoint z t).2))
  simp only [abs_mul] at h
  nlinarith only [h,h1,h2]

end OriginalPairStripGeometry
