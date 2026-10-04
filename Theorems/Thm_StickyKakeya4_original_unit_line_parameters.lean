import Theorems.Thm_StickyKakeya4_original_two_hop_pair_family
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalUnitLineParameters
open OriginalPairStripGeometry NativeRadialClassPruning NativeRadialClassGeometry
open OriginalRadialSineGeometry OriginalPhysicalPairTube

def unitX (z : Pair) : ℝ := (z.2.2-z.1.2)/‖complexDifference z.1 z.2‖
def unitY (z : Pair) : ℝ := -(z.2.1-z.1.1)/‖complexDifference z.1 z.2‖
def unitOffset (z : Pair) : ℝ := unitX z*z.1.1+unitY z*z.1.2

/-- These parameters are the unit normal of the literal original pair line. -/
theorem original_unit_normal_trigonometric (z : Pair) (hz : z.1≠z.2) :
    unitX z=Real.sin (radialAngle z.1 z.2) ∧
    unitY z= -Real.cos (radialAngle z.1 z.2) := by
  have hn : 0<‖complexDifference z.1 z.2‖ :=
    (scale_pos z hz).trans_le (original_scale_le_complex_norm z.1 z.2)
  have hs := Complex.norm_mul_sin_arg (complexDifference z.1 z.2)
  have hc := Complex.norm_mul_cos_arg (complexDifference z.1 z.2)
  constructor
  · apply (div_eq_iff (ne_of_gt hn)).mpr
    simpa only [complexDifference,radialAngle,mul_comm] using hs.symm
  · apply (div_eq_iff (ne_of_gt hn)).mpr
    change ‖complexDifference z.1 z.2‖*Real.cos (radialAngle z.1 z.2)=z.2.1-z.1.1 at hc
    linarith only [hc]

theorem original_unit_normal_square (z : Pair) (hz : z.1≠z.2) :
    unitX z^2+unitY z^2=1 := by
  obtain ⟨hx,hy⟩ := original_unit_normal_trigonometric z hz
  rw [hx,hy,neg_sq]
  exact Real.sin_sq_add_cos_sq _

/-- Every original affine-line witness lies on the actual parameter line. -/
theorem original_line_point_parameter (z : Pair) (a : ℝ) :
    unitX z*(linePoint z a).1+unitY z*(linePoint z a).2=unitOffset z := by
  dsimp [unitX,unitY,unitOffset,linePoint]
  ring

/-- Reversing an original pair negates the entire oriented line parameter. -/
theorem original_unit_parameter_swap (z : Pair) :
    unitX z.swap= -unitX z ∧ unitY z.swap= -unitY z ∧
    unitOffset z.swap= -unitOffset z := by
  have hdiff : complexDifference z.2 z.1= -complexDifference z.1 z.2 := by
    apply Complex.ext <;> dsimp [complexDifference] <;> ring
  have hn : ‖complexDifference z.2 z.1‖=‖complexDifference z.1 z.2‖ := by
    rw [hdiff,norm_neg]
  dsimp [unitX,unitY,unitOffset,Prod.swap]
  rw [hn]
  constructor
  · ring
  constructor <;> ring

/-- Actual same-root angle closeness controls actual normal and offset
coordinates on the fixed original source box. -/
theorem original_same_root_parameter_close (p a b : Point) (rho : ℝ)
    (hpa : p≠a) (hpb : p≠b) (hp : |p.1|≤1 ∧ |p.2|≤1)
    (hang : |radialAngle p a-radialAngle p b|≤rho) :
    |unitX (p,a)-unitX (p,b)|≤rho ∧
    |unitY (p,a)-unitY (p,b)|≤rho ∧
    |unitOffset (p,a)-unitOffset (p,b)|≤2*rho := by
  obtain ⟨hxa,hya⟩ := original_unit_normal_trigonometric (p,a) hpa
  obtain ⟨hxb,hyb⟩ := original_unit_normal_trigonometric (p,b) hpb
  have hx : |unitX (p,a)-unitX (p,b)|≤rho := by
    rw [hxa,hxb]
    exact (Real.abs_sin_sub_sin_le _ _).trans hang
  have hy : |unitY (p,a)-unitY (p,b)|≤rho := by
    rw [hya,hyb,neg_sub_neg,abs_sub_comm]
    exact (Real.abs_cos_sub_cos_le _ _).trans hang
  refine ⟨hx,hy,?_⟩
  have heq : unitOffset (p,a)-unitOffset (p,b)=
      (unitX (p,a)-unitX (p,b))*p.1+(unitY (p,a)-unitY (p,b))*p.2 := by
    dsimp [unitOffset]; ring
  rw [heq]
  calc
    _ ≤ |unitX (p,a)-unitX (p,b)| * |p.1| + 
      |unitY (p,a)-unitY (p,b)| * |p.2| := by
      simpa only [abs_mul] using (abs_add_le
        ((unitX (p,a)-unitX (p,b))*p.1) ((unitY (p,a)-unitY (p,b))*p.2))
    _ ≤ |unitX (p,a)-unitX (p,b)| + |unitY (p,a)-unitY (p,b)| := by
      exact add_le_add (by nlinarith [abs_nonneg (unitX (p,a)-unitX (p,b))])
        (by nlinarith [abs_nonneg (unitY (p,a)-unitY (p,b))])
    _ ≤ _ := by linarith only [hx,hy]

/-- The two literal class hops control original line parameters. In
particular this does not infer line proximity from bounded point support. -/
theorem original_class_hops_parameter_close
    (Pts : Finset Point) (z u v : Pair) (rho : ℝ)
    (hrho : 0<rho) (hzroot : z.2∈Pts) (huroot : u.1∈Pts)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hz : z.1≠z.2) (hu : u.1≠u.2) (hv : v.1≠v.2)
    (hreverse : reverseClass rho z=reverseClass rho u)
    (hforward : forwardClass rho u=forwardClass rho v) :
    |unitX z-unitX v|≤2*rho ∧ |unitY z-unitY v|≤2*rho ∧
    |unitOffset z-unitOffset v|≤4*rho := by
  obtain ⟨hroot1,hangle1⟩ := reverse_class_geometry rho hrho z u hreverse
  obtain ⟨hroot2,hangle2⟩ := forward_class_geometry rho hrho u v hforward
  have hrev := original_same_root_parameter_close z.2 z.1 u.1 rho hz.symm
    (by simpa only [hroot1] using hu.symm) (hbox z.2 hzroot)
    (by simpa only [hroot1] using hangle1.le)
  have hfwd := original_same_root_parameter_close u.1 u.2 v.2 rho hu
    (by simpa only [hroot2] using hv) (hbox u.1 huroot)
    (by simpa only [hroot2] using hangle2.le)
  have heq : (z.2,u.1)=u.swap := Prod.ext hroot1 rfl
  have heq2 : (u.1,v.2)=v := Prod.ext hroot2 rfl
  change |unitX z.swap-unitX (z.2,u.1)|≤rho ∧
    |unitY z.swap-unitY (z.2,u.1)|≤rho ∧
    |unitOffset z.swap-unitOffset (z.2,u.1)|≤2*rho at hrev
  rw [heq,(original_unit_parameter_swap z).1,(original_unit_parameter_swap u).1,
    (original_unit_parameter_swap z).2.1,(original_unit_parameter_swap u).2.1,
    (original_unit_parameter_swap z).2.2,(original_unit_parameter_swap u).2.2,
    neg_sub_neg,neg_sub_neg,neg_sub_neg,abs_sub_comm (unitX u),
    abs_sub_comm (unitY u),abs_sub_comm (unitOffset u)] at hrev
  rw [heq2] at hfwd
  refine ⟨?_,?_,?_⟩
  · exact (abs_sub_le (unitX z) (unitX u) (unitX v)).trans (by linarith only [hrev.1,hfwd.1])
  · exact (abs_sub_le (unitY z) (unitY u) (unitY v)).trans (by linarith only [hrev.2.1,hfwd.2.1])
  · exact (abs_sub_le (unitOffset z) (unitOffset u) (unitOffset v)).trans
      (by linarith only [hrev.2.2,hfwd.2.2])

end OriginalUnitLineParameters
