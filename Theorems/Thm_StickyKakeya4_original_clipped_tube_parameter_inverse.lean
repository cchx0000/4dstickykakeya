import Theorems.Thm_StickyKakeya4_original_clipped_unit_tube
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

noncomputable section
namespace OriginalClippedTubeParameterInverse
open OriginalPairStripGeometry OriginalUnitLineParameters OriginalClippedUnitTube

private theorem same_chart_det_controls_normal
    (a b c d w : ℝ) (hab : a^2+b^2=1) (hcd : c^2+d^2=1)
    (hchart : 1≤(a+c)^2+(b+d)^2) (hdet : |a*d-b*c|≤w) :
    |a-c|≤4*w ∧ |b-d|≤4*w := by
  have ha : |a|≤1 := abs_le.mpr ⟨by nlinarith [sq_nonneg b],by nlinarith [sq_nonneg b]⟩
  have hb : |b|≤1 := abs_le.mpr ⟨by nlinarith [sq_nonneg a],by nlinarith [sq_nonneg a]⟩
  have hc : |c|≤1 := abs_le.mpr ⟨by nlinarith [sq_nonneg d],by nlinarith [sq_nonneg d]⟩
  have hd : |d|≤1 := abs_le.mpr ⟨by nlinarith [sq_nonneg c],by nlinarith [sq_nonneg c]⟩
  have he : 1/2≤1+a*c+b*d := by nlinarith only [hab,hcd,hchart]
  have hep : 0<1+a*c+b*d := by linarith only [he]
  have hw : 0≤w := (abs_nonneg _).trans hdet
  have hid1 : (a-c)*(1+a*c+b*d)=(a*d-b*c)*(b+d) := by
    linear_combination c*hab-a*hcd
  have hid2 : (b-d)*(1+a*c+b*d)= -(a*d-b*c)*(a+c) := by
    linear_combination d*hab-b*hcd
  have hn1 : |b+d|≤2 := (abs_add_le b d).trans (by linarith only [hb,hd])
  have hn2 : |a+c|≤2 := (abs_add_le a c).trans (by linarith only [ha,hc])
  have h1 : |a-c| * (1+a*c+b*d)≤2*w := by
    calc
      _ = |(a*d-b*c)*(b+d)| := by rw [← hid1,abs_mul,abs_of_pos hep]
      _ = |a*d-b*c| * |b+d| := abs_mul _ _
      _ ≤ w*2 := mul_le_mul hdet hn1 (abs_nonneg _) hw
      _ = _ := by ring
  have h2 : |b-d| * (1+a*c+b*d)≤2*w := by
    calc
      _ = |-(a*d-b*c)*(a+c)| := by rw [← hid2,abs_mul,abs_of_pos hep]
      _ = |a*d-b*c| * |a+c| := by rw [abs_mul,abs_neg]
      _ ≤ w*2 := mul_le_mul hdet hn2 (abs_nonneg _) hw
      _ = _ := by ring
  exact ⟨by nlinarith [abs_nonneg (a-c)],by nlinarith [abs_nonneg (b-d)]⟩

/-- Actual same-chart unit normals are controlled by their determinant. -/
theorem original_same_chart_determinant_normal_close
    (z u : Pair) (v : ℝ) (hz : z.1≠z.2) (hu : u.1≠u.2)
    (hchart : normalChart z=normalChart u)
    (hdet : |unitX z*unitY u-unitY z*unitX u|≤v) :
    |unitX z-unitX u|≤4*v ∧ |unitY z-unitY u|≤4*v :=
  same_chart_det_controls_normal _ _ _ _ _ (original_unit_normal_square z hz)
    (original_unit_normal_square u hu) (original_same_chart_sum_square z u hz hu hchart) hdet

theorem original_bounded_unit_offset (z : Pair) (hz : z.1≠z.2)
    (hroot : |z.1.1|≤1 ∧ |z.1.2|≤1) : |unitOffset z|≤2 := by
  obtain ⟨hx,hy⟩ := original_unit_coordinate_bounds z hz
  have h1 := mul_le_mul hx hroot.1 (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h2 := mul_le_mul hy hroot.2 (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have hh := abs_add_le (unitX z*z.1.1) (unitY z*z.1.2)
  simp only [abs_mul] at hh
  change |unitX z*z.1.1+unitY z*z.1.2|≤2
  linarith only [h1,h2,hh]

/-- Containment of the actual clipped unit rectangle in a doubled-width
strip controls its genuine line parameters. The proof tests the full
centerline endpoints; no finite source-support containment is used. -/
theorem original_clipped_containment_parameter_close
    (z u : Pair) (w : ℝ) (hw : 0≤w)
    (hz : z.1≠z.2) (hu : u.1≠u.2)
    (hroot : |z.1.1|≤1 ∧ |z.1.2|≤1)
    (hchart : normalChart z=normalChart u)
    (hcontain : ∀ p∈clippedTube z w, |scaledResidual u p|≤2*w) :
    |unitX z-unitX u|≤8*w ∧ |unitY z-unitY u|≤8*w ∧
    |unitOffset z-unitOffset u|≤36*w := by
  let D := unitX z*unitY u-unitY z*unitX u
  let B := unitOffset z/2*(unitX z*unitX u+unitY z*unitY u)-unitOffset u/2
  have hp := hcontain (corePoint z 1) (original_core_point_mem z hz w 1 hw (by norm_num))
  have hm := hcontain (corePoint z (-1)) (original_core_point_mem z hz w (-1) hw (by norm_num))
  have h0 := hcontain (corePoint z 0) (original_core_point_mem z hz w 0 hw (by norm_num))
  have hep : scaledResidual u (corePoint z 1)=B+D := by dsimp [scaledResidual,corePoint,B,D]; ring
  have hem : scaledResidual u (corePoint z (-1))=B-D := by dsimp [scaledResidual,corePoint,B,D]; ring
  have he0 : scaledResidual u (corePoint z 0)=B := by dsimp [scaledResidual,corePoint,B]; ring
  rw [hep] at hp
  rw [hem] at hm
  rw [he0] at h0
  have hdet : |D|≤2*w := by
    obtain ⟨hp1,hp2⟩ := abs_le.mp hp
    obtain ⟨hm1,hm2⟩ := abs_le.mp hm
    exact abs_le.mpr ⟨by linarith only [hp1,hm2],by linarith only [hp2,hm1]⟩
  obtain ⟨hx,hy⟩ := same_chart_det_controls_normal (unitX z) (unitY z)
    (unitX u) (unitY u) (2*w) (original_unit_normal_square z hz)
    (original_unit_normal_square u hu) (original_same_chart_sum_square z u hz hu hchart) hdet
  have hx' : |unitX z-unitX u|≤8*w := by linarith only [hx]
  have hy' : |unitY z-unitY u|≤8*w := by linarith only [hy]
  refine ⟨hx',hy',?_⟩
  obtain ⟨hnx,hny⟩ := original_unit_coordinate_bounds z hz
  have hb := original_bounded_unit_offset z hz hroot
  let I := unitX z*(unitX z-unitX u)+unitY z*(unitY z-unitY u)
  have hi : |I|≤16*w := by
    have hh := abs_add_le (unitX z*(unitX z-unitX u)) (unitY z*(unitY z-unitY u))
    simp only [abs_mul] at hh
    have h1 := mul_le_mul_of_nonneg_right hnx (abs_nonneg (unitX z-unitX u))
    have h2 := mul_le_mul_of_nonneg_right hny (abs_nonneg (unitY z-unitY u))
    change |I|≤_ at hh
    nlinarith only [hh,h1,h2,hx',hy']
  have he : unitOffset z-unitOffset u=2*B+unitOffset z*I := by
    have hs := original_unit_normal_square z hz
    dsimp [B,I]
    linear_combination -(unitOffset z)*hs
  rw [he]
  have hh := abs_add_le (2*B) (unitOffset z*I)
  simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  have hprod := mul_le_mul hb hi (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  linarith only [hh,hprod,h0]

end OriginalClippedTubeParameterInverse
