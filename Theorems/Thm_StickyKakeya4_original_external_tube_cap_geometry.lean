import Theorems.Thm_StickyKakeya4_original_clipped_tube_parameter_inverse
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3400000

noncomputable section
namespace OriginalExternalTubeCapGeometry
open OriginalPairStripGeometry OriginalUnitLineParameters OriginalClippedUnitTube
open OriginalClippedTubeParameterInverse OriginalLocalizedLineCellCharge

def normalDot (z u : Pair) : ℝ := unitX z*unitX u+unitY z*unitY u
def normalDet (z u : Pair) : ℝ := unitX z*unitY u-unitY z*unitX u

theorem original_unit_dot_det_square (z u : Pair) (hz : z.1≠z.2) (hu : u.1≠u.2) :
    normalDot z u^2+normalDet z u^2=1 := by
  calc
    _ = (unitX z^2+unitY z^2)*(unitX u^2+unitY u^2) := by dsimp [normalDot,normalDet]; ring
    _ = 1 := by rw [original_unit_normal_square z hz,original_unit_normal_square u hu]; norm_num

/-- Full clipped-segment containment tests yield the actual determinant
and offset moment against any external line, with no source-point proxy. -/
theorem original_clipped_strip_moments (z u : Pair) (w W : ℝ)
    (hw : 0≤w) (hz : z.1≠z.2)
    (hcontain : ∀ p∈clippedTube z w, |scaledResidual u p|≤W) :
    |normalDet z u|≤W ∧ |unitOffset z/2*normalDot z u-unitOffset u/2|≤W := by
  let B := unitOffset z/2*normalDot z u-unitOffset u/2
  have hp := hcontain (corePoint z 1) (original_core_point_mem z hz w 1 hw (by norm_num))
  have hm := hcontain (corePoint z (-1)) (original_core_point_mem z hz w (-1) hw (by norm_num))
  have h0 := hcontain (corePoint z 0) (original_core_point_mem z hz w 0 hw (by norm_num))
  have hep : scaledResidual u (corePoint z 1)=B+normalDet z u := by
    dsimp [scaledResidual,corePoint,B,normalDet,normalDot]; ring
  have hem : scaledResidual u (corePoint z (-1))=B-normalDet z u := by
    dsimp [scaledResidual,corePoint,B,normalDet,normalDot]; ring
  have he0 : scaledResidual u (corePoint z 0)=B := by dsimp [scaledResidual,corePoint,B,normalDot]; ring
  rw [hep] at hp
  rw [hem] at hm
  rw [he0] at h0
  refine ⟨?_,h0⟩
  obtain ⟨hp1,hp2⟩ := abs_le.mp hp
  obtain ⟨hm1,hm2⟩ := abs_le.mp hm
  exact abs_le.mpr ⟨by linarith only [hp1,hm2],by linarith only [hp2,hm1]⟩

/-- Two actual clipped tubes in one external narrow strip have close
original line parameters. The common signed chart resolves antipodal
orientation, while the external line need not come from the source. -/
theorem original_common_external_strip_parameter_close
    (z a u : Pair) (w W : ℝ) (hw : 0≤w) (hW : W≤1/4)
    (hz : z.1≠z.2) (ha : a.1≠a.2) (hu : u.1≠u.2)
    (hroot : |z.1.1|≤1 ∧ |z.1.2|≤1)
    (hchart : normalChart z=normalChart a)
    (hzcontain : ∀ p∈clippedTube z w, |scaledResidual u p|≤W)
    (hacontain : ∀ p∈clippedTube a w, |scaledResidual u p|≤W) :
    parameterNear (72*W) a z := by
  obtain ⟨hDz,hBz⟩ := original_clipped_strip_moments z u w W hw hz hzcontain
  obtain ⟨hDa,hBa⟩ := original_clipped_strip_moments a u w W hw ha hacontain
  have hW0 : 0≤W := (abs_nonneg _).trans hDz
  have hzu := original_unit_dot_det_square z u hz hu
  have hau := original_unit_dot_det_square a u ha hu
  have hdotz : |normalDot z u|≤1 := abs_le.mpr
    ⟨by nlinarith [sq_nonneg (normalDet z u)],by nlinarith [sq_nonneg (normalDet z u)]⟩
  have hdota : |normalDot a u|≤1 := abs_le.mpr
    ⟨by nlinarith [sq_nonneg (normalDet a u)],by nlinarith [sq_nonneg (normalDet a u)]⟩
  have hid : normalDet z a=normalDet z u*normalDot a u-normalDet a u*normalDot z u := by
    have hs := original_unit_normal_square u hu
    dsimp [normalDet,normalDot]
    linear_combination -(unitX z*unitY a-unitY z*unitX a)*hs
  have hza : |normalDet z a|≤2*W := by
    rw [hid]
    have hh := abs_sub (normalDet z u*normalDot a u) (normalDet a u*normalDot z u)
    simp only [abs_mul] at hh
    have h1 := mul_le_mul hDz hdota (abs_nonneg _) hW0
    have h2 := mul_le_mul hDa hdotz (abs_nonneg _) hW0
    linarith only [hh,h1,h2]
  obtain ⟨hx,hy⟩ := original_same_chart_determinant_normal_close z a (2*W) hz ha hchart hza
  have hdiff : |normalDot a u-normalDot z u|≤16*W := by
    have he : normalDot a u-normalDot z u=
        (unitX a-unitX z)*unitX u+(unitY a-unitY z)*unitY u := by dsimp [normalDot]; ring
    rw [he]
    have hh := abs_add_le ((unitX a-unitX z)*unitX u) ((unitY a-unitY z)*unitY u)
    simp only [abs_mul,abs_sub_comm (unitX a),abs_sub_comm (unitY a)] at hh
    obtain ⟨hux,huy⟩ := original_unit_coordinate_bounds u hu
    have h1 := mul_le_mul_of_nonneg_left hux (abs_nonneg (unitX z-unitX a))
    have h2 := mul_le_mul_of_nonneg_left huy (abs_nonneg (unitY z-unitY a))
    nlinarith only [hh,h1,h2,hx,hy]
  have hdotlower : 1/2≤|normalDot a u| := by
    obtain ⟨hlo,hhi⟩ := abs_le.mp (hDa.trans hW)
    have hprod : 0≤(1/4-normalDet a u)*(1/4+normalDet a u) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_abs (normalDot a u),abs_nonneg (normalDot a u)]
  let Bz := unitOffset z/2*normalDot z u-unitOffset u/2
  let Ba := unitOffset a/2*normalDot a u-unitOffset u/2
  have he : normalDot a u*(unitOffset z-unitOffset a)=
      2*(Bz-Ba)+unitOffset z*(normalDot a u-normalDot z u) := by dsimp [Bz,Ba]; ring
  have hb := original_bounded_unit_offset z hz hroot
  have hbdiff : |Bz-Ba|≤2*W := (abs_sub _ _).trans (by linarith only [hBz,hBa])
  have hproduct : |normalDot a u| * |unitOffset z-unitOffset a|≤36*W := by
    rw [← abs_mul,he]
    have hh := abs_add_le (2*(Bz-Ba)) (unitOffset z*(normalDot a u-normalDot z u))
    simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
    have hp := mul_le_mul hb hdiff (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
    linarith only [hh,hp,hbdiff]
  refine ⟨by linarith only [hx,hW0],by linarith only [hy,hW0],?_⟩
  nlinarith only [hproduct,hdotlower,abs_nonneg (unitOffset z-unitOffset a)]

end OriginalExternalTubeCapGeometry
