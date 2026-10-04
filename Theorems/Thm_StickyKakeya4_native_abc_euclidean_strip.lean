import Theorems.Thm_StickyKakeya4_native_planar_abc_input
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeABCEuclideanStrip
open Classical NativePlanarABCInput
/-- The factor-two strip allowance in the constructed native ABC input
 supplies the literal Euclidean unit-normal strip bound on the SAME B. -/
theorem actual_euclidean_strip_bound
    {mesh exponent ballK angularK density width lineFraction coverK : ℝ}
    (data : Data mesh exponent ballK angularK density (2*width) lineFraction coverK)
    (hw : 0 ≤ width) (aa dd cc : ℝ) (hunit : aa^2+dd^2=1) :
    ((data.B.filter (fun b => |aa*b.1+dd*b.2-cc| ≤ width)).card:ℝ) ≤
      lineFraction*(data.B.card:ℝ) := by
  let m := max |aa| |dd|
  have hma : |aa| ≤ m := le_max_left _ _
  have hmd : |dd| ≤ m := le_max_right _ _
  have hm0 : 0 ≤ m := (abs_nonneg aa).trans hma
  have ha := (sq_le_sq₀ (abs_nonneg aa) hm0).mpr hma
  have hd := (sq_le_sq₀ (abs_nonneg dd) hm0).mpr hmd
  rw [sq_abs] at ha hd
  have hmhalf : (1/2:ℝ) ≤ m := by nlinarith only [ha,hd,hunit,hm0]
  have hm : 0 < m := by linarith only [hmhalf]
  have hnorm : max |aa/m| |dd/m|=1 := by
    rw [abs_div,abs_div,abs_of_pos hm,max_div_div_right hm.le]
    exact div_self hm.ne'
  have hsub : data.B.filter (fun b => |aa*b.1+dd*b.2-cc| ≤ width) ⊆
      data.B.filter (fun b => |(aa/m)*b.1+(dd/m)*b.2-cc/m| ≤ 2*width) := by
    intro b hb
    obtain ⟨hb,hnear⟩ := Finset.mem_filter.mp hb
    apply Finset.mem_filter.mpr
    refine ⟨hb,?_⟩
    have hid : (aa/m)*b.1+(dd/m)*b.2-cc/m=(aa*b.1+dd*b.2-cc)/m := by ring
    rw [hid,abs_div,abs_of_pos hm]
    exact (div_le_div_of_nonneg_right hnear hm.le).trans
      ((div_le_iff₀ hm).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hmhalf hw]))
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (data.lineB (aa/m) (dd/m) (cc/m) hnorm)
end NativeABCEuclideanStrip
