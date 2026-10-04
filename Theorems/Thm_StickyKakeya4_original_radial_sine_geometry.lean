import Theorems.Thm_StickyKakeya4_native_radial_class_pruning
import Theorems.Thm_StickyKakeya4_original_physical_pair_tube

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

noncomputable section
namespace OriginalRadialSineGeometry
open Classical OriginalPairStripGeometry OriginalPhysicalPairTube NativeRadialClassPruning

def complexDifference (p q : Point) : ℂ := ⟨q.1-p.1,q.2-p.2⟩

lemma original_scale_le_complex_norm (p q : Point) :
    scale (p,q)≤‖complexDifference p q‖ := by
  exact max_le (Complex.abs_re_le_norm (complexDifference p q))
    (Complex.abs_im_le_norm (complexDifference p q))

/-- Exact determinant identity for the angles of the original two secants. -/
theorem original_sine_residual_identity (p q v : Point) (hne : p≠q) :
    ‖complexDifference p q‖*‖complexDifference p v‖*
      Real.sin (radialAngle p q-radialAngle p v) =
      -(scale (p,q)*PlanarStripIntersection.residual (normalX (p,q))
        (normalY (p,q)) (offset (p,q)) v) := by
  let z := complexDifference p q
  let w := complexDifference p v
  have hn : ‖z‖*‖w‖*Real.sin (Complex.arg z-Complex.arg w)=
      z.im*w.re-z.re*w.im := by
    rw [Real.sin_sub]
    calc
      _ = (‖z‖*Real.sin z.arg)*(‖w‖*Real.cos w.arg)-
          (‖z‖*Real.cos z.arg)*(‖w‖*Real.sin w.arg) := by ring
      _ = _ := by rw [Complex.norm_mul_sin_arg,Complex.norm_mul_cos_arg,
        Complex.norm_mul_cos_arg,Complex.norm_mul_sin_arg]
  change ‖z‖*‖w‖*Real.sin (Complex.arg z-Complex.arg w)=_
  rw [hn]
  dsimp [z,w,complexDifference,PlanarStripIntersection.residual,offset,normalX,normalY]
  field_simp [ne_of_gt (scale_pos (p,q) hne)]
  ring

/-- A far original point in an original physical tube constrains the actual
angle to two antipodal narrow arcs, with no replacement direction. -/
theorem physical_tube_small_sine (P : Finset Point) (p q v : Point)
    (hne : p≠q) {rho tau : ℝ} (htau : 0<tau)
    (hfar : tau≤scale (p,v)) (hv : v∈physicalPairTube P rho (p,q)) :
    |Real.sin (radialAngle p q-radialAngle p v)| ≤ 2*rho/tau := by
  have hstrip := (Finset.mem_filter.mp (physical_pair_tube_subset P rho (p,q) hne hv)).2
  have hn := original_sine_residual_identity p q v hne
  have hscale := scale_pos (p,q) hne
  have hzn := original_scale_le_complex_norm p q
  have hwn := original_scale_le_complex_norm p v
  have hzpos : 0<‖complexDifference p q‖ := hscale.trans_le hzn
  have hrho : 0≤2*rho := (abs_nonneg _).trans hstrip
  have habs := congrArg abs hn
  simp only [abs_mul,abs_norm,abs_neg,abs_of_pos hscale] at habs
  have hh : ‖complexDifference p q‖*‖complexDifference p v‖*
      |Real.sin (radialAngle p q-radialAngle p v)| ≤
      ‖complexDifference p q‖*(2*rho) := by
    rw [habs]
    exact (mul_le_mul_of_nonneg_left hstrip hscale.le).trans
      (mul_le_mul_of_nonneg_right hzn hrho)
  have hcancel : ‖complexDifference p v‖*|Real.sin (radialAngle p q-radialAngle p v)|≤2*rho := by
    apply (mul_le_mul_iff_right₀ hzpos).mp
    simpa only [mul_assoc] using hh
  apply (le_div_iff₀ htau).mpr
  calc
    _ = tau*|Real.sin (radialAngle p q-radialAngle p v)| := by ring
    _ ≤ ‖complexDifference p v‖*|Real.sin (radialAngle p q-radialAngle p v)| :=
      mul_le_mul_of_nonneg_right (hfar.trans hwn) (abs_nonneg _)
    _ ≤ _ := hcancel

end OriginalRadialSineGeometry
