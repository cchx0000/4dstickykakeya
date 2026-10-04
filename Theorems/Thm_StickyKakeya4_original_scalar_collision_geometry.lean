import Theorems.Thm_StickyKakeya4_vector_graph_collision_energy
import Theorems.Thm_StickyKakeya4_original_pair_strip_physical_bridge

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
noncomputable section
open Classical
namespace OriginalScalarCollisionGeometry
open PlanarShiftedNearEnergy VectorGraphCollisionEnergy
abbrev Point := ℝ × ℝ

def det (v w : Point) : ℝ := v.1*w.2-v.2*w.1

lemma same_grid_norm_le {eta : ℝ} (heta : 0 < eta) {x y : Point}
    (hgrid : roundPoint eta x=roundPoint eta y) : ‖x-y‖ ≤ eta := by
  have hh := same_planar_grid_close heta hgrid
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs,max_le_iff] using hh

/-- A large original scalar difference forces a large original A difference
when the original B secant has a lower length bound. -/
theorem original_collision_separation {eta d t s : ℝ} {a a' v : Point} {c c' : ℝ}
    (heta : 0 < eta) (hd : 0 ≤ d) (_ht : 0 ≤ t)
    (hv : d ≤ ‖v‖) (hc : t ≤ |c-c'|) (hscale : s+eta ≤ d*t)
    (hgrid : roundPoint eta (a+c • v)=roundPoint eta (a'+c' • v)) : s ≤ ‖a-a'‖ := by
  have hg := same_grid_norm_le heta hgrid
  have hid : (c-c') • v = (a+c • v-(a'+c' • v))-(a-a') := by
    simp only [sub_smul]
    abel
  have htri := norm_sub_le (a+c • v-(a'+c' • v)) (a-a')
  rw [← hid,norm_smul,Real.norm_eq_abs] at htri
  have hm := mul_le_mul hc hv hd (abs_nonneg _)
  nlinarith only [htri,hg,hm,hscale]

/-- The same literal grid collision yields the homogeneous directional
relation used in the final actual-pair incidence count. -/
theorem original_collision_det {eta : ℝ} {a a' v : Point} {c c' : ℝ}
    (heta : 0 < eta)
    (hgrid : roundPoint eta (a+c • v)=roundPoint eta (a'+c' • v)) :
    |det v (a-a')| ≤ 2*eta*‖v‖ := by
  have hh := same_planar_grid_close heta hgrid
  have hid : det v (a-a')=det v (a+c • v-(a'+c' • v)) := by
    dsimp [det]
    ring
  have hv1 : |v.1| ≤ ‖v‖ := by
    simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_left |v.1| |v.2|
  have hv2 : |v.2| ≤ ‖v‖ := by
    simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_right |v.1| |v.2|
  have h1 := mul_le_mul hv1 hh.2 (abs_nonneg _) (norm_nonneg v)
  have h2 := mul_le_mul hv2 hh.1 (abs_nonneg _) (norm_nonneg v)
  rw [hid]
  have ha := abs_add_le (v.1*((a+c • v).2-(a'+c' • v).2))
    (-(v.2*((a+c • v).1-(a'+c' • v).1)))
  simp only [← sub_eq_add_neg,abs_neg,abs_mul] at ha
  change |det v (a+c • v-(a'+c' • v))| ≤ _
  dsimp [det] at ha ⊢
  dsimp at h1 h2
  nlinarith only [ha,h1,h2]

/-- Two original secants close to the same nonzero displacement are close
to each other. This is a determinant identity, without angular representatives. -/
theorem det_two_near_directions {u v w : Point} {eta s : ℝ}
    (_hs : 0 < s) (hw : s ≤ ‖w‖)
    (hu : |det u w| ≤ 2*eta*‖u‖) (hv : |det v w| ≤ 2*eta*‖v‖) :
    s*|det u v| ≤ 4*eta*‖u‖*‖v‖ := by
  have huf : |u.1| ≤ ‖u‖ := by simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_left |u.1| |u.2|
  have huv : |u.2| ≤ ‖u‖ := by simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_right |u.1| |u.2|
  have hvf : |v.1| ≤ ‖v‖ := by simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_left |v.1| |v.2|
  have hvv : |v.2| ≤ ‖v‖ := by simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_right |v.1| |v.2|
  have hx : |w.1| *|det u v| ≤ 4*eta*‖u‖*‖v‖ := by
    have hid : w.1*det u v=u.1*det w v-v.1*det w u := by dsimp [det]; ring
    have huv' : |det w u|=|det u w| := by dsimp [det]; rw [← abs_neg]; congr 1; ring
    have hvv' : |det w v|=|det v w| := by dsimp [det]; rw [← abs_neg]; congr 1; ring
    have hh := abs_add_le (u.1*det w v) (-(v.1*det w u))
    simp only [← sub_eq_add_neg,abs_neg] at hh
    rw [← hid,abs_mul] at hh
    simp only [abs_mul,huv',hvv'] at hh
    have h1 := mul_le_mul huf hv (abs_nonneg _) (norm_nonneg u)
    have h2 := mul_le_mul hvf hu (abs_nonneg _) (norm_nonneg v)
    nlinarith only [hh,h1,h2]
  have hy : |w.2| *|det u v| ≤ 4*eta*‖u‖*‖v‖ := by
    have hid : w.2*det u v=u.2*det w v-v.2*det w u := by dsimp [det]; ring
    have huv' : |det w u|=|det u w| := by dsimp [det]; rw [← abs_neg]; congr 1; ring
    have hvv' : |det w v|=|det v w| := by dsimp [det]; rw [← abs_neg]; congr 1; ring
    have hh := abs_add_le (u.2*det w v) (-(v.2*det w u))
    simp only [← sub_eq_add_neg,abs_neg] at hh
    rw [← hid,abs_mul] at hh
    simp only [abs_mul,huv',hvv'] at hh
    have h1 := mul_le_mul huv hv (abs_nonneg _) (norm_nonneg u)
    have h2 := mul_le_mul hvv hu (abs_nonneg _) (norm_nonneg v)
    nlinarith only [hh,h1,h2]
  have hmax : ‖w‖*|det u v| ≤ 4*eta*‖u‖*‖v‖ := by
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_mul_of_nonneg _ _ (abs_nonneg _)]
    exact max_le hx hy
  exact (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans hmax
end OriginalScalarCollisionGeometry
