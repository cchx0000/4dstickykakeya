import Theorems.Thm_StickyKakeya4_original_shading_center_profile
import Theorems.Thm_StickyKakeya4_original_shading_grid_geometry
import Theorems.Thm_StickyKakeya4_original_clipped_unit_tube
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalShadingBoxProfile
open Classical OriginalPairStripGeometry PlanarFrostmanBallConversion PlanarStripIntersection
open OriginalShadingGridGeometry OriginalClippedUnitTube

/-- Two actual points in one arbitrary R-box lie in the Euclidean
4R-ball centered at either original point. -/
theorem original_common_box_euclidean (p q x : Point) (R : ℝ)
    (hp : InBox p x R) (hq : InBox q x R) : euclideanDistance p q≤4*R := by
  have hx : |q.1-p.1|≤2*R := (abs_sub_le q.1 x.1 p.1).trans (by
    rw [abs_sub_comm x.1]
    linarith only [hq.1,hp.1])
  have hy : |q.2-p.2|≤2*R := (abs_sub_le q.2 x.2 p.2).trans (by
    rw [abs_sub_comm x.2]
    linarith only [hq.2,hp.2])
  have hmax : boxDistance p q≤2*R := max_le hx hy
  exact (euclidean_le_two_box p q).trans (by linarith only [hmax])

/-- The explicit spatial halving doubles the box radius and center when
lifting back to original coordinates. -/
theorem original_half_box_lift (p x : Point) (R : ℝ)
    (hp : InBox (halfPoint p) x R) : InBox p (2*x.1,2*x.2) (2*R) := by
  constructor
  · change |p.1-2*x.1|≤2*R
    rw [show p.1-2*x.1=2*(p.1/2-x.1) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh : |p.1/2-x.1|≤R := hp.1
    linarith only [hh]
  · change |p.2-2*x.2|≤2*R
    rw [show p.2-2*x.2=2*(p.2/2-x.2) by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh : |p.2/2-x.2|≤R := hp.2
    linarith only [hh]

/-- A nonempty box in halved coordinates lifts to an actual original
8R-ball, with its center chosen from the same original shading. -/
theorem original_half_common_box_euclidean (p q x : Point) (R : ℝ)
    (hp : InBox (halfPoint p) x R) (hq : InBox (halfPoint q) x R) :
    euclideanDistance p q≤8*R := by
  have hh := original_common_box_euclidean p q (2*x.1,2*x.2) (2*R)
    (original_half_box_lift p x R hp) (original_half_box_lift q x R hq)
  nlinarith only [hh]

/-- Original-center profiles give the arbitrary-center box profile needed
by the coarse-shading engine. The constant eight includes spatial halving. -/
theorem original_half_box_profile_from_centers
    (Y : Finset Point) (rho K b : ℝ) (hrho : 0<rho) (hK : 1≤K)
    (_hb : 0≤b) (hb1 : b≤1)
    (hcenter : ∀ p∈Y, ∀ L : ℝ, rho≤L →
      ((Y.filter (fun q => euclideanDistance p q≤L)).card : ℝ)≤K*L^b*Y.card)
    (x : Point) (R : ℝ) (hR : rho≤R) :
    ((Y.filter (fun p => InBox (halfPoint p) x R)).card : ℝ)≤8*K*R^b*Y.card := by
  have hRp : 0<R := hrho.trans_le hR
  have hK0 : 0≤K := by linarith only [hK]
  by_cases hnonempty : (Y.filter (fun p => InBox (halfPoint p) x R)).Nonempty
  · obtain ⟨p,hp⟩ := hnonempty
    have hsub : Y.filter (fun q => InBox (halfPoint q) x R)⊆
        Y.filter (fun q => euclideanDistance p q≤8*R) := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,
        original_half_common_box_euclidean p q x R
          (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2⟩
    have hball := hcenter p (Finset.mem_filter.mp hp).1 (8*R) (by linarith only [hR,hRp])
    have h8 : (8:ℝ)^b≤8 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ)≤8) hb1
    have hpow : (8*R)^b≤8*R^b := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤8) hRp.le]
      exact mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg hRp.le b)
    have hscale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hK0) (Nat.cast_nonneg Y.card)
    have hcard : ((Y.filter (fun q => InBox (halfPoint q) x R)).card : ℝ)≤
        (Y.filter (fun q => euclideanDistance p q≤8*R)).card :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hh := hcard.trans (hball.trans hscale)
    nlinarith only [hh]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty,Finset.card_empty,Nat.cast_zero]
    positivity

end OriginalShadingBoxProfile
