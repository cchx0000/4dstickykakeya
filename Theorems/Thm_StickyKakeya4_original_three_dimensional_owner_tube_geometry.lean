import Theorems.Thm_StickyKakeya4_original_three_dimensional_slab_projection
import Theorems.Thm_StickyKakeya4_original_three_dimensional_tube_incidence_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace OriginalThreeDimensionalOwnerTubeGeometry
open OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalTubeSlab
open OriginalThreeDimensionalSlabProjection OriginalTubeGraphPairGeometry

lemma original_distance_triangle (x y z : Point3) :
    distance3 x z ≤ distance3 x y+distance3 y z := by
  simp only [distance3_eq_euclidean]
  exact dist_triangle _ _ _

lemma original_coordinate_box_distance (x y : Point3) (B : ℝ)
    (hB : 0 ≤ B) (hxy : ∀ j,|x j-y j| ≤ B) : distance3 x y ≤ 2*B := by
  have h0 := pow_le_pow_left₀ (abs_nonneg _) (hxy 0) 2
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (hxy 1) 2
  have h2 := pow_le_pow_left₀ (abs_nonneg _) (hxy 2) 2
  rw [sq_abs] at h0 h1 h2
  unfold distance3
  apply (Real.sqrt_le_left (by positivity : 0 ≤ 2*B)).mpr
  nlinarith only [h0,h1,h2,sq_nonneg B]

/-- Moving BOTH original endpoints to nearby actual owners has a loss
proportional to the original inverse separation. It is not a constant-mesh
perturbation theorem. -/
theorem original_pair_owner_tube_perturbation (p q u v x : Point3)
    (rho r h : ℝ) (hr : 0 < r) (hh : 0 ≤ h) (hrho1 : rho ≤ 1)
    (hp : ∀ j,|p j| ≤ 1) (hx : ∀ j,|x j| ≤ 2)
    (hsep : r ≤ distance3 p q)
    (hu : distance3 p u ≤ h) (hv : distance3 q v ≤ h)
    (htube : x∈physicalTube3 p q rho) :
    x∈physicalTube3 u v (rho+2*h+32*h/r) := by
  obtain ⟨t,ht⟩ := htube
  have htime := original_affine_parameter_bound p q x rho r t hr hrho1 hsep hp hx ht
  have herr (j : Fin 3) :
      |linePoint3 p q t j-linePoint3 u v t j| ≤ h+2*|t| * h := by
    have hpj := (original_coordinate_le_distance p u j).trans hu
    have hqj := (original_coordinate_le_distance q v j).trans hv
    have hd := abs_sub (q j-v j) (p j-u j)
    have hm := mul_le_mul_of_nonneg_left hd (abs_nonneg t)
    have hs := abs_add_le (p j-u j) (t*((q j-v j)-(p j-u j)))
    rw [abs_mul] at hs
    have he : (p j-u j)+t*((q j-v j)-(p j-u j))=
        linePoint3 p q t j-linePoint3 u v t j := by dsimp [linePoint3]; ring
    rw [he] at hs
    have ht2 := mul_le_mul_of_nonneg_left (show |q j-v j|+|p j-u j| ≤ 2*h by linarith only [hpj,hqj]) (abs_nonneg t)
    nlinarith only [hs,hm,ht2,hpj]
  have hd := original_coordinate_box_distance (linePoint3 p q t) (linePoint3 u v t)
    (h+2*|t| * h) (by positivity) herr
  have htriangle := original_distance_triangle x (linePoint3 p q t) (linePoint3 u v t)
  have hm := mul_le_mul_of_nonneg_right htime hh
  have he : (8/r)*h=8*h/r := by ring
  rw [he] at hm
  have hm4 : 4*|t| * h ≤ 32*h/r := by
    calc
      _ = 4*(|t| * h) := by ring
      _ ≤ 4*(8*h/r) := mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by ring
  have hlarge : 2*(h+2*|t| * h) ≤ 2*h+32*h/r := by
    linarith only [hm4]
  refine ⟨t,?_⟩
  exact htriangle.trans ((add_le_add ht (hd.trans hlarge)).trans_eq (by ring))

/-- The actual Delta/4 owner net turns a32Delta rich pair tube into an
original owner-pair tube of width160Delta/r, with the scale loss explicit. -/
theorem original_delta_owner_tube (p q u v x : Point3) (Delta r : ℝ)
    (hDelta : 0 < Delta) (hsmall : 32*Delta ≤ 1) (hr : 0 < r)
    (hp : ∀ j,|p j| ≤ 1) (hq : ∀ j,|q j| ≤ 1) (hx : ∀ j,|x j| ≤ 1)
    (hsep : r ≤ distance3 p q)
    (hu : distance3 p u ≤ Delta/4) (hv : distance3 q v ≤ Delta/4)
    (htube : x∈physicalTube3 p q (32*Delta)) :
    x∈physicalTube3 u v (160*Delta/r) := by
  have hr4 := hsep.trans (original_box_distance_le_four p q hp hq)
  obtain ⟨t,ht⟩ := original_pair_owner_tube_perturbation p q u v x (32*Delta) r (Delta/4)
    hr (by positivity) hsmall hp (fun j => (hx j).trans (by norm_num)) hsep hu hv htube
  refine ⟨t,ht.trans ?_⟩
  apply (le_div_iff₀ hr).mpr
  have he : (32*Delta+2*(Delta/4)+32*(Delta/4)/r)*r=
      (65/2:ℝ)*Delta*r+8*Delta := by field_simp; ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hr4 (show 0 ≤ (65/2:ℝ)*Delta by positivity)
  nlinarith only [hm,hDelta]

end OriginalThreeDimensionalOwnerTubeGeometry
