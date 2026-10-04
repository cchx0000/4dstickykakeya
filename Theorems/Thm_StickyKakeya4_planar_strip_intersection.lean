import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

namespace PlanarStripIntersection

def residual (a b c : ℝ) (p : ℝ × ℝ) : ℝ := a*p.1+b*p.2-c

def determinant (a b c d : ℝ) : ℝ := a*d-b*c

def boxDistance (p q : ℝ × ℝ) : ℝ := max |q.1-p.1| |q.2-p.2|

lemma abs_combination_le_four {u v s t w : ℝ} (_hw : 0≤w)
    (hu : |u|≤1) (hv : |v|≤1) (hs : |s|≤2*w) (ht : |t|≤2*w) :
    |u*s-v*t|≤4*w := by
  have h1 := mul_le_mul hu hs (abs_nonneg s) (by norm_num : (0:ℝ)≤1)
  have h2 := mul_le_mul hv ht (abs_nonneg t) (by norm_num : (0:ℝ)≤1)
  have h := abs_sub (u*s) (v*t)
  rw [abs_mul,abs_mul] at h
  nlinarith only [h,h1,h2]

/-- Two genuine common strip points control both coordinates through the
actual determinant, without an inverse-matrix or angle hypothesis. -/
theorem common_point_coordinate_bounds
    (a b c d e f w : ℝ) (p q : ℝ × ℝ) (hw : 0≤w)
    (ha : |a|≤1) (hb : |b|≤1) (hc : |c|≤1) (hd : |d|≤1)
    (hp : |residual a b e p|≤w) (hq : |residual a b e q|≤w)
    (hp' : |residual c d f p|≤w) (hq' : |residual c d f q|≤w) :
    |determinant a b c d| * |q.1-p.1|≤4*w ∧
      |determinant a b c d| * |q.2-p.2|≤4*w := by
  have hfirst : |residual a b e q-residual a b e p|≤2*w :=
    (abs_sub _ _).trans (by linarith)
  have hsecond : |residual c d f q-residual c d f p|≤2*w :=
    (abs_sub _ _).trans (by linarith)
  have hx : determinant a b c d*(q.1-p.1)=
      d*(residual a b e q-residual a b e p)-b*(residual c d f q-residual c d f p) := by
    unfold determinant residual
    ring
  have hy : determinant a b c d*(q.2-p.2)=
      a*(residual c d f q-residual c d f p)-c*(residual a b e q-residual a b e p) := by
    unfold determinant residual
    ring
  constructor
  · rw [← abs_mul,hx]
    exact abs_combination_le_four hw hd hb hfirst hsecond
  · rw [← abs_mul,hy]
    exact abs_combination_le_four hw ha hc hsecond hfirst

/-- A long overlap witnessed by original points forces an actual small
determinant. The width/separation ratio remains explicit. -/
theorem determinant_bound_of_common_separation
    (a b c d e f w rho : ℝ) (p q : ℝ × ℝ) (hw : 0≤w) (hrho : 0<rho)
    (ha : |a|≤1) (hb : |b|≤1) (hc : |c|≤1) (hd : |d|≤1)
    (hp : |residual a b e p|≤w) (hq : |residual a b e q|≤w)
    (hp' : |residual c d f p|≤w) (hq' : |residual c d f q|≤w)
    (hsep : rho<boxDistance p q) :
    |determinant a b c d|≤4*w/rho := by
  have hcoords := common_point_coordinate_bounds a b c d e f w p q hw ha hb hc hd hp hq hp' hq'
  have hmax : |determinant a b c d| * boxDistance p q≤4*w := by
    unfold boxDistance
    rcases le_total |q.1-p.1| |q.2-p.2| with h|h
    · rw [max_eq_right h]
      exact hcoords.2
    · rw [max_eq_left h]
      exact hcoords.1
  apply (le_div_iff₀ hrho).mpr
  exact (mul_le_mul_of_nonneg_left hsep.le (abs_nonneg _)).trans hmax

/-- A lower determinant bound gives a point-centered intersection ball. -/
theorem transverse_intersection_ball
    (a b c d e f w theta : ℝ) (p q : ℝ × ℝ) (hw : 0≤w) (htheta : 0<theta)
    (ha : |a|≤1) (hb : |b|≤1) (hc : |c|≤1) (hd : |d|≤1)
    (hp : |residual a b e p|≤w) (hq : |residual a b e q|≤w)
    (hp' : |residual c d f p|≤w) (hq' : |residual c d f q|≤w)
    (hdet : theta≤|determinant a b c d|) :
    boxDistance p q≤4*w/theta := by
  have hcoords := common_point_coordinate_bounds a b c d e f w p q hw ha hb hc hd hp hq hp' hq'
  apply max_le
  · apply (le_div_iff₀ htheta).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hdet (abs_nonneg (q.1-p.1))).trans hcoords.1
  · apply (le_div_iff₀ htheta).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hdet (abs_nonneg (q.2-p.2))).trans hcoords.2

lemma unit_coordinate_transfer {u v D r r0 s0 target t w : ℝ}
    (hu : |u|=1) (hv : |v|≤1) (hr : |r|≤w) (hr0 : |r0|≤w)
    (hs0 : |s0|≤w) (ht : |t|≤2)
    (heq : u*target=v*(r-r0)+D*t+u*s0) :
    |target|≤3*w+2*|D| := by
  have hdiff : |r-r0|≤2*w := (abs_sub _ _).trans (by linarith)
  have h1 := mul_le_mul hv hdiff (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h2 := mul_le_mul_of_nonneg_left ht (abs_nonneg D)
  have h3 : |u*s0|≤w := by rw [abs_mul,hu,one_mul]; exact hs0
  calc
    _ = |u*target| := by rw [abs_mul,hu,one_mul]
    _ = |v*(r-r0)+D*t+u*s0| := by rw [heq]
    _ ≤ (|v| * |r-r0|+|D| * |t|)+|u*s0| := by
      have h := (abs_add_le (v*(r-r0)+D*t) (u*s0)).trans
        (add_le_add (abs_add_le (v*(r-r0)) (D*t)) (le_refl |u*s0|))
      simpa only [abs_mul] using h
    _ ≤ _ := by nlinarith only [h1,h2,h3]

/-- One genuine common point and a small determinant control the entire
bounded original point domain. No direction center is substituted. -/
theorem bounded_strip_containment
    (a b c d e f w : ℝ) (p z : ℝ × ℝ)
    (hunit : |a|=1 ∨ |b|=1) (hc : |c|≤1) (hd : |d|≤1)
    (hp : |residual a b e p|≤w) (hz : |residual a b e z|≤w)
    (hp' : |residual c d f p|≤w)
    (hx : |z.1-p.1|≤2) (hy : |z.2-p.2|≤2) :
    |residual c d f z|≤3*w+2*|determinant a b c d| := by
  rcases hunit with ha|hb
  · apply unit_coordinate_transfer ha hc hz hp hp' hy
    unfold determinant residual
    ring
  · have h := unit_coordinate_transfer (D := -determinant a b c d) (target := residual c d f z) hb hd hz hp hp' hx
      (by unfold determinant residual; ring)
    simpa only [abs_neg] using h

/-- Native rho0 thickening uses w=rho0^2 explicitly; before substituting
those native scales, the actual bound is eleven times width/separation. -/
theorem long_overlap_containment
    (a b c d e f w rho : ℝ) (p q z : ℝ × ℝ) (hw : 0≤w)
    (hrho : 0<rho) (hrho1 : rho≤1)
    (ha : |a|≤1) (hb : |b|≤1) (hc : |c|≤1) (hd : |d|≤1)
    (hunit : |a|=1 ∨ |b|=1)
    (hp : |residual a b e p|≤w) (hq : |residual a b e q|≤w)
    (hp' : |residual c d f p|≤w) (hq' : |residual c d f q|≤w)
    (hz : |residual a b e z|≤w) (hsep : rho<boxDistance p q)
    (hx : |z.1-p.1|≤2) (hy : |z.2-p.2|≤2) :
    |residual c d f z|≤11*w/rho := by
  have hdet := determinant_bound_of_common_separation a b c d e f w rho p q hw hrho ha hb hc hd hp hq hp' hq' hsep
  have hcontain := bounded_strip_containment a b c d e f w p z hunit hc hd hp hz hp' hx hy
  have hwdiv : w≤w/rho := by
    apply (le_div_iff₀ hrho).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hrho1 hw]
  simp only [mul_div_assoc] at hdet ⊢
  nlinarith only [hdet,hcontain,hwdiv]

end PlanarStripIntersection
