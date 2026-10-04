import Theorems.Thm_StickyKakeya4_original_radial_sine_geometry
import Theorems.Thm_StickyKakeya4_original_pair_strip_physical_bridge
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace BoundedOriginalAngleTubeTransfer
open OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning
open OriginalRadialSineGeometry OriginalPairStripPhysicalBridge NativeRichPairTubeFamily

theorem original_complex_norm_le_two_scale (p q : Point) :
    ‖complexDifference p q‖≤2*scale (p,q) := by
  have h := Complex.norm_le_abs_re_add_abs_im (complexDifference p q)
  have h1 : |(complexDifference p q).re|≤scale (p,q) := le_max_left _ _
  have h2 : |(complexDifference p q).im|≤scale (p,q) := le_max_right _ _
  linarith only [h,h1,h2]

/-- Physical membership controls the weighted sine of the actual two
original secants, including points at the root. No far-distance division
or lower bound on the original pair length is used. -/
theorem original_physical_weighted_sine (Pts : Finset Point) (p a v : Point)
    (w : ℝ) (hne : p≠a) (hv : v∈physicalPairTube Pts w (p,a)) :
    ‖complexDifference p v‖*|Real.sin (radialAngle p a-radialAngle p v)|≤2*w := by
  have hstrip := (Finset.mem_filter.mp (physical_pair_tube_subset Pts w (p,a) hne hv)).2
  have hn := original_sine_residual_identity p a v hne
  have hs := scale_pos (p,a) hne
  have hsn := original_scale_le_complex_norm p a
  have hnp : 0<‖complexDifference p a‖ := hs.trans_le hsn
  have hw : 0≤2*w := (abs_nonneg _).trans hstrip
  have habs := congrArg abs hn
  simp only [abs_mul,abs_norm,abs_neg,abs_of_pos hs] at habs
  have hh : ‖complexDifference p a‖*‖complexDifference p v‖*
      |Real.sin (radialAngle p a-radialAngle p v)|≤‖complexDifference p a‖*(2*w) := by
    rw [habs]
    exact (mul_le_mul_of_nonneg_left hstrip hs.le).trans
      (mul_le_mul_of_nonneg_right hsn hw)
  apply (mul_le_mul_iff_of_pos_left hnp).mp
  simpa only [mul_assoc] using hh

/-- Actual same-root angle closeness transfers the ORIGINAL bounded-source
support from width w to width 4w+8rho. This is not a containment statement
for unbounded strips. The pair lengths only need to be nonzero. -/
theorem original_bounded_same_root_support_transfer
    (Pts : Finset Point) (p a b : Point) (w rho : ℝ)
    (hrho : 0≤rho) (hp : p∈Pts)
    (hbox : ∀ x∈Pts, |x.1|≤1 ∧ |x.2|≤1)
    (hpa : p≠a) (hpb : p≠b)
    (hangle : |radialAngle p a-radialAngle p b|≤rho) :
    physicalPairTube Pts w (p,a)⊆physicalPairTube Pts (4*w+8*rho) (p,b) := by
  classical
  intro v hv
  have hvP := (Finset.mem_filter.mp hv).1
  have hpbox := hbox p hp
  have hvbox := hbox v hvP
  have hx : |v.1-p.1|≤2 := (abs_sub _ _).trans (by linarith only [hpbox.1,hvbox.1])
  have hy : |v.2-p.2|≤2 := (abs_sub _ _).trans (by linarith only [hpbox.2,hvbox.2])
  have hvnorm : ‖complexDifference p v‖≤4 := by
    have hh := Complex.norm_le_abs_re_add_abs_im (complexDifference p v)
    change ‖complexDifference p v‖≤|v.1-p.1|+|v.2-p.2| at hh
    linarith only [hh,hx,hy]
  have hsinlip := Real.abs_sin_sub_sin_le
    (radialAngle p b-radialAngle p v) (radialAngle p a-radialAngle p v)
  have heq : (radialAngle p b-radialAngle p v)-(radialAngle p a-radialAngle p v)=
      -(radialAngle p a-radialAngle p b) := by ring
  rw [heq,abs_neg] at hsinlip
  have hsin : |Real.sin (radialAngle p b-radialAngle p v)|≤
      |Real.sin (radialAngle p a-radialAngle p v)|+rho := by
    have hh := abs_add_le (Real.sin (radialAngle p a-radialAngle p v))
      (Real.sin (radialAngle p b-radialAngle p v)-Real.sin (radialAngle p a-radialAngle p v))
    rw [show Real.sin (radialAngle p a-radialAngle p v)+
      (Real.sin (radialAngle p b-radialAngle p v)-Real.sin (radialAngle p a-radialAngle p v))=
        Real.sin (radialAngle p b-radialAngle p v) by ring] at hh
    exact hh.trans (add_le_add (le_refl _) (hsinlip.trans hangle))
  have hweighted := original_physical_weighted_sine Pts p a v w hpa hv
  have hbweighted : ‖complexDifference p v‖*|Real.sin (radialAngle p b-radialAngle p v)|≤
      2*w+4*rho := by
    have hh := mul_le_mul_of_nonneg_left hsin (norm_nonneg (complexDifference p v))
    have hlast := mul_le_mul_of_nonneg_right hvnorm hrho
    nlinarith only [hh,hweighted,hlast]
  have hs := scale_pos (p,b) hpb
  have hn := original_sine_residual_identity p b v hpb
  have habs := congrArg abs hn
  simp only [abs_mul,abs_norm,abs_neg,abs_of_pos hs] at habs
  have hnorm := original_complex_norm_le_two_scale p b
  have hres : scale (p,b)*|PlanarStripIntersection.residual
      (normalX (p,b)) (normalY (p,b)) (offset (p,b)) v|≤scale (p,b)*(4*w+8*rho) := by
    calc
      _ = ‖complexDifference p b‖*(‖complexDifference p v‖*
          |Real.sin (radialAngle p b-radialAngle p v)|) := by rw [← habs]; ring
      _ ≤ (2*scale (p,b))*(‖complexDifference p v‖*
          |Real.sin (radialAngle p b-radialAngle p v)|) :=
        mul_le_mul_of_nonneg_right hnorm (mul_nonneg (norm_nonneg _) (abs_nonneg _))
      _ ≤ (2*scale (p,b))*(2*w+4*rho) :=
        mul_le_mul_of_nonneg_left hbweighted (by positivity)
      _ = _ := by ring
  apply original_strip_subset_physical Pts (4*w+8*rho) (p,b) hpb
  exact Finset.mem_filter.mpr ⟨hvP,(mul_le_mul_iff_of_pos_left hs).mp hres⟩

end BoundedOriginalAngleTubeTransfer
