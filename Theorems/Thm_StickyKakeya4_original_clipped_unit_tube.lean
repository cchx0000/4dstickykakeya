import Theorems.Thm_StickyKakeya4_original_representative_shading
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
namespace OriginalClippedUnitTube
open Classical OriginalPairStripGeometry OriginalUnitLineParameters
open OriginalUnitParameterPhysical OriginalRepresentativeShading

def scaledResidual (z : Pair) (p : Point) : ℝ :=
  unitX z*p.1+unitY z*p.2-unitOffset z/2

def longitudinal (z : Pair) (p : Point) : ℝ := -unitY z*p.1+unitX z*p.2

def clippedTube (z : Pair) (w : ℝ) : Set Point :=
  {p | |scaledResidual z p|≤w ∧ |longitudinal z p|≤1}

def corePoint (z : Pair) (t : ℝ) : Point :=
  (unitOffset z/2*unitX z-t*unitY z,unitOffset z/2*unitY z+t*unitX z)

def halfPoint (p : Point) : Point := (p.1/2,p.2/2)

def normalChart (z : Pair) : Fin 4 :=
  if 1≤2*unitX z then 0 else if 2*unitX z≤ -1 then 1 else
    if 1≤2*unitY z then 2 else 3

def chartCondition (i : Fin 4) (z : Pair) : Prop :=
  match i with
  | ⟨0,_⟩ => 1≤2*unitX z
  | ⟨1,_⟩ => 2*unitX z≤ -1
  | ⟨2,_⟩ => 1≤2*unitY z
  | _ => 2*unitY z≤ -1

theorem original_unit_coordinate_bounds (z : Pair) (hz : z.1≠z.2) :
    |unitX z|≤1 ∧ |unitY z|≤1 := by
  have hs := original_unit_normal_square z hz
  constructor <;> apply abs_le.mpr <;> constructor <;>
    nlinarith [sq_nonneg (unitX z),sq_nonneg (unitY z)]

theorem original_normal_chart_valid (z : Pair) (hz : z.1≠z.2) :
    chartCondition (normalChart z) z := by
  have hs := original_unit_normal_square z hz
  unfold normalChart
  split_ifs with hx hx' hy
  · exact hx
  · exact hx'
  · exact hy
  · change 2*unitY z≤ -1
    by_contra hy'
    have hxx : 0≤(1-2*unitX z)*(1+2*unitX z) := mul_nonneg (by linarith) (by linarith)
    have hyy : 0<(1-2*unitY z)*(1+2*unitY z) := mul_pos (by linarith) (by linarith)
    nlinarith only [hxx,hyy,hs]

/-- A common signed chart excludes antipodal normals quantitatively. -/
theorem original_same_chart_sum_square (z u : Pair)
    (hz : z.1≠z.2) (hu : u.1≠u.2) (heq : normalChart z=normalChart u) :
    1≤(unitX z+unitX u)^2+(unitY z+unitY u)^2 := by
  have hzc := original_normal_chart_valid z hz
  have huc := original_normal_chart_valid u hu
  rw [← heq] at huc
  generalize normalChart z=i at hzc huc
  fin_cases i <;> simp only [chartCondition] at hzc huc <;>
    nlinarith [sq_nonneg (unitX z+unitX u),sq_nonneg (unitY z+unitY u)]

/-- The centerline is a literal unit segment of the parameter line. -/
theorem original_core_point_coordinates (z : Pair) (hz : z.1≠z.2) (t : ℝ) :
    scaledResidual z (corePoint z t)=0 ∧ longitudinal z (corePoint z t)=t := by
  have hs := original_unit_normal_square z hz
  constructor
  · calc
      _ = unitOffset z/2*(unitX z^2+unitY z^2-1) := by
        dsimp [scaledResidual,corePoint]; ring
      _ = 0 := by rw [hs]; ring
  · calc
      _ = t*(unitX z^2+unitY z^2) := by dsimp [longitudinal,corePoint]; ring
      _ = t := by rw [hs,mul_one]

theorem original_core_point_mem (z : Pair) (hz : z.1≠z.2) (w t : ℝ)
    (hw : 0≤w) (ht : |t|≤1) : corePoint z t∈clippedTube z w := by
  obtain ⟨hres,hlong⟩ := original_core_point_coordinates z hz t
  exact ⟨by simpa only [hres,abs_zero] using hw,by simpa only [hlong] using ht⟩

/-- Halving the original source gives actual shaded points in the clipped
length-two rectangle. Its normal half-width is 3rho. -/
theorem original_shading_half_mem_clipped
    (Pts : Finset Point) (G : Finset Pair) (rho : ℝ) (z : Pair) (p : Point)
    (hz : z.1≠z.2) (hbox : ∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1)
    (hp : p∈originalShading Pts G rho z) : halfPoint p∈clippedTube z (3*rho) := by
  obtain ⟨hpP,q,_hqG,hnear⟩ := Finset.mem_filter.mp hp
  have hzero : unitResidual (p,q) p=0 := by dsimp [unitResidual,unitOffset]; ring
  have hres := original_parameter_residual_compare (p,q) z p (2*rho) (2*rho)
    (hbox p hpP) hnear.1 hnear.2.1 hnear.2.2
  rw [hzero,abs_zero] at hres
  obtain ⟨hnx,hny⟩ := original_unit_coordinate_bounds z hz
  obtain ⟨hpx,hpy⟩ := hbox p hpP
  constructor
  · have he : scaledResidual z (halfPoint p)=unitResidual z p/2 := by
      dsimp [scaledResidual,halfPoint,unitResidual]; ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [hres]
  · have hh := abs_add_le (-unitY z*(p.1/2)) (unitX z*(p.2/2))
    simp only [abs_mul,abs_neg,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
    change |-unitY z*(p.1/2)+unitX z*(p.2/2)|≤1
    have hx := mul_le_mul hny hpx (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hy := mul_le_mul hnx hpy (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    nlinarith only [hh,hx,hy]

end OriginalClippedUnitTube
