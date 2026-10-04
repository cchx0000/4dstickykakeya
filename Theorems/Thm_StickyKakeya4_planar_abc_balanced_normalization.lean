import Theorems.Thm_StickyKakeya4_actual_planar_target_cover
import Theorems.Thm_StickyKakeya4_original_angular_alphabet_translation
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
noncomputable section
namespace PlanarABCBalancedNormalization
open Classical
abbrev Point := ℝ × ℝ
def source (a : Point) : Point := (1/8:ℝ) • a
def direction (anchor b : Point) : Point := (1/4:ℝ) • (b-anchor)
def scalar (c : ℝ) : ℝ := c/2
/-- Exact balanced normalization; the original scalar is only halved here,
 after source-Phi translation and graph-preserving projection. -/
lemma product_identity (a b anchor : Point) (c : ℝ) :
    source a+scalar c • direction anchor b=source (a+c • (b-anchor)) := by
  unfold source scalar direction
  module
lemma residual_identity (a target b anchor : Point) (c : ℝ) :
    source target-source a-scalar c • direction anchor b=(1/8:ℝ) • (target-a-c • (b-anchor)) := by
  unfold source scalar direction
  module
theorem balanced_error (a target b anchor : Point) (c : ℝ) {error : ℝ}
    (herror : ‖target-a-c • (b-anchor)‖ ≤ error) :
    ‖source a+scalar c • direction anchor b-source target‖ ≤ error/8 := by
  have hid : source a+scalar c • direction anchor b-source target=
      -(source target-source a-scalar c • direction anchor b) := by abel
  rw [hid,norm_neg,residual_identity,norm_smul]
  norm_num
  nlinarith
lemma source_box (a : Point) (ha : ‖a‖ ≤ 2) : ‖source a‖ ≤ 1 := by
  unfold source
  rw [norm_smul]
  norm_num
  nlinarith
lemma direction_box (anchor b : Point) (ha : ‖anchor‖ ≤ 2) (hb : ‖b‖ ≤ 2) :
    ‖direction anchor b‖ ≤ 1 := by
  have hh := norm_sub_le b anchor
  unfold direction
  rw [norm_smul]
  norm_num
  nlinarith
lemma scalar_box (c : ℝ) (hc : |c| ≤ 2) : |scalar c| ≤ 1 := by
  unfold scalar
  rw [abs_div]
  norm_num
  linarith
lemma source_injective : Function.Injective source := by
  intro x y h
  have hh := congrArg (fun p : Point => (8:ℝ) • p) h
  simpa [source,smul_smul] using hh
lemma direction_injective (anchor : Point) : Function.Injective (direction anchor) := by
  intro x y h
  have hh := congrArg (fun p : Point => (4:ℝ) • p) h
  have he : x-anchor=y-anchor := by simpa [direction,smul_smul] using hh
  have hh' := congrArg (fun p : Point => p+anchor) he
  simpa only [sub_add_cancel] using hh'
lemma scalar_injective : Function.Injective scalar := by
  intro x y h
  change x/2=y/2 at h
  linarith
/-- Same original target, uniform projected error, and exact new ABC mesh. -/
theorem projected_balanced_error (a target b anchor : Point) (c : ℝ) {error mesh : ℝ}
    (hm : 0 ≤ mesh) (hc : |c| ≤ 2)
    (hrel : ‖target-a-c • (b-anchor)‖ ≤ 2*error+(1+|c|)*mesh) :
    ‖source a+scalar c • direction anchor b-source target‖ ≤ (2*error+3*mesh)/8 := by
  have hh := balanced_error a target b anchor c hrel
  have hmul := mul_le_mul_of_nonneg_right hc hm
  nlinarith
lemma normalized_cover_factor {error mesh : ℝ} (hm : 0 < mesh) :
    (2*((2*error+3*mesh)/8)/(mesh/8)+2)^2=(4*error/mesh+8)^2 := by
  congr 1
  field_simp
  ring
end PlanarABCBalancedNormalization
