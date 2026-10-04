import Theorems.Thm_StickyKakeya4_planar_strip_intersection
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

noncomputable section
namespace PlanarFrostmanBallConversion
open PlanarStripIntersection

def euclideanDistance (p q : ℝ × ℝ) : ℝ := Real.sqrt ((q.1-p.1)^2+(q.2-p.2)^2)

theorem euclidean_le_two_box (p q : ℝ × ℝ) :
    euclideanDistance p q≤2*boxDistance p q := by
  have hx : |q.1-p.1|≤boxDistance p q := le_max_left _ _
  have hy : |q.2-p.2|≤boxDistance p q := le_max_right _ _
  have hr : 0≤boxDistance p q := (abs_nonneg _).trans hx
  have hxs := pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hys := pow_le_pow_left₀ (abs_nonneg _) hy 2
  apply (Real.sqrt_le_left (mul_nonneg (by norm_num) hr)).mpr
  simp only [sq_abs] at hxs hys
  nlinarith only [hxs,hys,sq_nonneg (boxDistance p q)]

/-- The actual infinity ball is contained in the Euclidean ball at twice
the radius, including closed boundary points. -/
theorem box_ball_card_le
    (Pts : Finset (ℝ × ℝ)) (p : ℝ × ℝ) (r : ℝ) :
    (Pts.filter (fun q => boxDistance p q≤r)).card ≤
      (Pts.filter (fun q => euclideanDistance p q≤2*r)).card := by
  classical
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqP,hqr⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_filter.mpr ⟨hqP,?_⟩
  exact (euclidean_le_two_box p q).trans (by nlinarith only [hqr])

/-- Source Euclidean Frostman counts give native infinity-ball counts with
factor at most four when t<=2. The exact queried radius is 2r. -/
theorem box_frostman_bound
    (Pts : Finset (ℝ × ℝ)) (p : ℝ × ℝ) (K t r : ℝ)
    (hK : 0≤K) (hr : 0≤r) (ht : t≤2)
    (hball : ((Pts.filter (fun q => euclideanDistance p q≤2*r)).card : ℝ)≤
      K*(2*r)^t*Pts.card) :
    ((Pts.filter (fun q => boxDistance p q≤r)).card : ℝ)≤4*K*r^t*Pts.card := by
  have hpow : (2:ℝ)^t≤4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) ht
    norm_num only [Real.rpow_two,show (2:ℝ)^2=4 by norm_num] at h
    exact h
  have hmul := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hr t)
  rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤2) hr] at hmul
  have htotal := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul hK)
    (Nat.cast_nonneg Pts.card)
  have hcard : ((Pts.filter (fun q => boxDistance p q≤r)).card : ℝ)≤
      ((Pts.filter (fun q => euclideanDistance p q≤2*r)).card : ℝ) := by
    exact_mod_cast box_ball_card_le Pts p r
  have h := hcard.trans (hball.trans htotal)
  nlinarith only [h]

/-- The actual diagonal charge follows from the original mesh-scale ball
profile, rather than an assumed lower cardinality of P. -/
theorem diagonal_charge
    (Pts : Finset (ℝ × ℝ)) (hPts : Pts.Nonempty) (delta K t : ℝ) (hdelta : 0≤delta)
    (hball : ∀ p∈Pts, ((Pts.filter (fun q => euclideanDistance p q≤delta)).card : ℝ)≤
      K*delta^t*Pts.card) :
    (Pts.card : ℝ)≤K*delta^t*(Pts.card : ℝ)^2 := by
  classical
  obtain ⟨p,hp⟩ := hPts
  have hmem : p∈Pts.filter (fun q => euclideanDistance p q≤delta) := by
    apply Finset.mem_filter.mpr
    refine ⟨hp,?_⟩
    simpa only [euclideanDistance,sub_self,zero_pow (by decide : 2≠0),zero_add,Real.sqrt_zero] using hdelta
  have hone : (1:ℝ)≤(Pts.filter (fun q => euclideanDistance p q≤delta)).card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨p,hmem⟩
  have h := mul_le_mul_of_nonneg_right (hone.trans (hball p hp)) (Nat.cast_nonneg Pts.card)
  nlinarith only [h]

end PlanarFrostmanBallConversion
