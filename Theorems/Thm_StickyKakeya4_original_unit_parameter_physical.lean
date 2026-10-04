import Theorems.Thm_StickyKakeya4_original_line_representative_charge
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalUnitParameterPhysical
open Classical
open OriginalPairStripGeometry OriginalPhysicalPairTube OriginalUnitLineParameters
open OriginalRadialSineGeometry BoundedOriginalAngleTubeTransfer OriginalPairStripPhysicalBridge

def unitResidual (z : Pair) (p : Point) : ℝ :=
  unitX z*p.1+unitY z*p.2-unitOffset z

/-- Exact conversion of the actual unit-normal residual to the original
sup-normalized strip residual. -/
theorem original_unit_strip_residual_identity (z : Pair) (p : Point) (hz : z.1≠z.2) :
    scale z*PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) p=
      -‖complexDifference z.1 z.2‖*unitResidual z p := by
  have hs := ne_of_gt (scale_pos z hz)
  have hn := ne_of_gt ((scale_pos z hz).trans_le (original_scale_le_complex_norm z.1 z.2))
  dsimp [unitResidual,unitOffset,unitX,unitY,PlanarStripIntersection.residual,offset,normalX,normalY]
  field_simp [hs,hn]
  ring

/-- The original unit-normal slab gives a genuine affine-line witness at
physical width twice its residual width. -/
theorem original_unit_residual_physical (Pts : Finset Point) (z : Pair) (p : Point) (w : ℝ)
    (hz : z.1≠z.2) (hp : p∈Pts) (hres : |unitResidual z p|≤w) :
    p∈physicalPairTube Pts (2*w) z := by
  have hs := scale_pos z hz
  have hn := original_complex_norm_le_two_scale z.1 z.2
  have habs := congrArg abs (original_unit_strip_residual_identity z p hz)
  simp only [abs_mul,abs_of_pos hs,abs_neg,abs_norm] at habs
  have hw : 0≤w := (abs_nonneg _).trans hres
  have hbound : scale z*|PlanarStripIntersection.residual
      (normalX z) (normalY z) (offset z) p|≤scale z*(2*w) := by
    rw [habs]
    calc
      _ ≤ ‖complexDifference z.1 z.2‖*w := mul_le_mul_of_nonneg_left hres (norm_nonneg _)
      _ ≤ (2*scale z)*w := mul_le_mul_of_nonneg_right hn hw
      _ = _ := by ring
  exact original_strip_subset_physical Pts (2*w) z hz
    (Finset.mem_filter.mpr ⟨hp,(mul_le_mul_iff_of_pos_left hs).mp hbound⟩)

/-- Actual Euclidean tube membership controls the original unit residual. -/
theorem original_physical_unit_residual (Pts : Finset Point) (z : Pair) (p : Point) (w : ℝ)
    (hz : z.1≠z.2) (hp : p∈physicalPairTube Pts w z) :
    |unitResidual z p|≤2*w := by
  have hs := scale_pos z hz
  have hn := original_scale_le_complex_norm z.1 z.2
  have hnpos := hs.trans_le hn
  have hstrip := (Finset.mem_filter.mp (physical_pair_tube_subset Pts w z hz hp)).2
  have hw : 0≤2*w := (abs_nonneg _).trans hstrip
  have habs := congrArg abs (original_unit_strip_residual_identity z p hz)
  simp only [abs_mul,abs_of_pos hs,abs_neg,abs_norm] at habs
  apply (mul_le_mul_iff_of_pos_left hnpos).mp
  calc
    _ = scale z*|PlanarStripIntersection.residual (normalX z) (normalY z) (offset z) p| := habs.symm
    _ ≤ scale z*(2*w) := mul_le_mul_of_nonneg_left hstrip hs.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hn hw

/-- A parameter comparison controls the residual at every bounded source
point, retaining the actual original line on both sides. -/
theorem original_parameter_residual_compare (z u : Pair) (p : Point) (A C : ℝ)
    (hp : |p.1|≤1 ∧ |p.2|≤1)
    (hx : |unitX z-unitX u|≤A) (hy : |unitY z-unitY u|≤A)
    (hc : |unitOffset z-unitOffset u|≤C) :
    |unitResidual u p|≤|unitResidual z p|+2*A+C := by
  have heq : unitResidual u p=unitResidual z p+
      ((unitX u-unitX z)*p.1+(unitY u-unitY z)*p.2-(unitOffset u-unitOffset z)) := by
    dsimp [unitResidual]; ring
  have hfirst : |(unitX u-unitX z)*p.1|≤A := by
    rw [abs_mul,abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left hp.1 (abs_nonneg _)).trans (by simpa using hx)
  have hsecond : |(unitY u-unitY z)*p.2|≤A := by
    rw [abs_mul,abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left hp.2 (abs_nonneg _)).trans (by simpa using hy)
  have hthird : |unitOffset u-unitOffset z|≤C := by simpa only [abs_sub_comm] using hc
  rw [heq]
  have hsum := abs_add_le ((unitX u-unitX z)*p.1) ((unitY u-unitY z)*p.2)
  have hdiff := abs_sub ((unitX u-unitX z)*p.1+(unitY u-unitY z)*p.2)
    (unitOffset u-unitOffset z)
  exact (abs_add_le _ _).trans (by linarith only [hsum,hdiff,hfirst,hsecond,hthird])

/-- Actual parameter closeness transfers original bounded physical support. -/
theorem original_parameter_support_transfer (Pts : Finset Point) (z u : Pair) (w A C : ℝ)
    (hz : z.1≠z.2) (hu : u.1≠u.2)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hx : |unitX z-unitX u|≤A) (hy : |unitY z-unitY u|≤A)
    (hc : |unitOffset z-unitOffset u|≤C) :
    physicalPairTube Pts w z⊆physicalPairTube Pts (4*w+4*A+2*C) u := by
  intro p hp
  have hpP := (Finset.mem_filter.mp hp).1
  have hres := original_parameter_residual_compare z u p A C (hbox p hpP) hx hy hc
  have hphys := original_physical_unit_residual Pts z p w hz hp
  have hout := original_unit_residual_physical Pts u p (2*w+2*A+C) hu hpP
    (by linarith only [hres,hphys])
  simpa only [show 2*(2*w+2*A+C)=4*w+4*A+2*C by ring] using hout

/-- Both original endpoints of a parameter-close pair lie in an actual
physical tube of the reference pair. No new endpoint is introduced. -/
theorem original_parameter_close_endpoints (Pts : Finset Point) (v z : Pair) (A C : ℝ)
    (hz : z.1≠z.2) (hvP : v∈Pts.product Pts)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hx : |unitX v-unitX z|≤A) (hy : |unitY v-unitY z|≤A)
    (hc : |unitOffset v-unitOffset z|≤C) :
    v∈(physicalPairTube Pts (4*A+2*C) z).product
      (physicalPairTube Pts (4*A+2*C) z) := by
  have hzero : unitResidual v v.1=0 ∧ unitResidual v v.2=0 := by
    constructor <;> dsimp [unitResidual,unitOffset,unitX,unitY] <;> ring
  have hpoint (p : Point) (hp : p∈Pts) (hzero : unitResidual v p=0) :
      p∈physicalPairTube Pts (4*A+2*C) z := by
    have hh := original_parameter_residual_compare v z p A C (hbox p hp) hx hy hc
    rw [hzero,abs_zero,zero_add] at hh
    have hout := original_unit_residual_physical Pts z p (2*A+C) hz hp hh
    simpa only [show 2*(2*A+C)=4*A+2*C by ring] using hout
  exact Finset.mem_product.mpr ⟨hpoint v.1 (Finset.mem_product.mp hvP).1 hzero.1,
    hpoint v.2 (Finset.mem_product.mp hvP).2 hzero.2⟩

end OriginalUnitParameterPhysical
