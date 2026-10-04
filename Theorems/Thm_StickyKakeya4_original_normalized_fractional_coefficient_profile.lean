import Theorems.Thm_StickyKakeya4_original_fractional_linear_coefficient_profile
import Theorems.Thm_StickyKakeya4_original_coefficient_profile_mesh_transfer
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
noncomputable section
namespace OriginalNormalizedFractionalCoefficientProfile
open Classical GKZOriginalGapEnergy OriginalFractionalLinearCoefficientProfile
open OriginalCoefficientProfileMeshTransfer

def normalizedCoefficient (a b c0 c : ℝ) : ℝ := coefficient a b c/coefficient a b c0

lemma original_reference_coefficient_lower (a b c0 h : ℝ) (hh : 0 < h)
    (hb : |b| ≤ 1) (hc0 : |c0| ≤ 1)
    (h0a : h ≤ |c0-a|) (h0b : h ≤ |b-c0|) :
    h/2 ≤ |coefficient a b c0| := by
  have hden : 0 < |b-c0| := hh.trans_le h0b
  rw [coefficient,abs_div]
  apply (le_div_iff₀ hden).mpr
  have hbc : |b-c0| ≤ 2 := (abs_sub b c0).trans (by linarith only [hb,hc0])
  have hm := mul_le_mul_of_nonneg_left hbc (show 0 ≤ h/2 by positivity)
  nlinarith only [hm,h0a]

lemma original_normalized_coefficient_inverse (a b c0 c d h : ℝ) (hh : 0 < h)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc0 : |c0| ≤ 1)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) (hab : h ≤ |a-b|)
    (h0a : h ≤ |c0-a|) (h0b : h ≤ |b-c0|)
    (hbc : h ≤ |b-c|) (hbd : h ≤ |b-d|) :
    |c-d| ≤ (8/h^2)*|normalizedCoefficient a b c0 c-normalizedCoefficient a b c0 d| := by
  have hlo := original_reference_coefficient_lower a b c0 h hh hb hc0 h0a h0b
  have hne : coefficient a b c0≠0 := abs_pos.mp ((by positivity : 0<h/2).trans_le hlo)
  have hup := original_coefficient_bound a b c0 h hh ha hc0 h0b
  have hi := original_coefficient_inverse_bound a b c d h hh hb hc hd hab
    (abs_pos.mp (hh.trans_le hbc)) (abs_pos.mp (hh.trans_le hbd))
  have he : coefficient a b c-coefficient a b d=coefficient a b c0*
      (normalizedCoefficient a b c0 c-normalizedCoefficient a b c0 d) := by
    unfold normalizedCoefficient
    field_simp
  rw [he,abs_mul] at hi
  calc
    |c-d| ≤ (4/h)*(|coefficient a b c0| * |normalizedCoefficient a b c0 c-normalizedCoefficient a b c0 d|) := hi
    _ ≤ (4/h)*((2/h)*|normalizedCoefficient a b c0 c-normalizedCoefficient a b c0 d|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hup (abs_nonneg _)) (by positivity)
    _ = (8/h^2)*|normalizedCoefficient a b c0 c-normalizedCoefficient a b c0 d| := by ring

/-- A reference third slope normalizes the coefficient alphabet without
losing original labels. Its full weak profile is valid at the ACTUAL
re-rounding mesh h*delta/64, not merely at the larger old mesh. -/
theorem original_normalized_coefficient_image_profile (C : Finset ℝ)
    (a b c0 h delta K u : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hd : 0 < delta) (hK : 1 ≤ K) (hu : 0 ≤ u)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc0 : |c0| ≤ 1)
    (hab : h ≤ |a-b|) (h0a : h ≤ |c0-a|) (h0b : h ≤ |b-c0|)
    (hC : ∀ c∈C,|c| ≤ 1) (hgap : ∀ c∈C,h ≤ |b-c|)
    (hprofile : ScalarFrostman C delta K u) :
    (C.image (normalizedCoefficient a b c0)).card=C.card ∧
    (∀ x∈C.image (normalizedCoefficient a b c0),|x| ≤ 4/h^2) ∧
    ScalarFrostman (C.image (normalizedCoefficient a b c0)) (h*delta/64)
      (K*(64/h^2)^u) u := by
  have hlo := original_reference_coefficient_lower a b c0 h hh hb hc0 h0a h0b
  have hp : 0 < |coefficient a b c0| := (by positivity : 0<h/2).trans_le hlo
  have hne := abs_pos.mp hp
  have hinj0 := original_coefficient_injective C a b h hh hb hab hC hgap
  have hinj : Set.InjOn (normalizedCoefficient a b c0) C := by
    intro c hc d hd he
    exact hinj0 hc hd ((div_left_inj' hne).mp he)
  refine ⟨Finset.card_image_of_injOn hinj,?_,?_⟩
  · intro x hx
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hx
    rw [normalizedCoefficient,abs_div]
    have hu0 := original_coefficient_bound a b c h hh ha (hC c hc) (hgap c hc)
    apply (div_le_iff₀ hp).mpr
    have hm := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 4/h^2 by positivity)
    have he : (4/h^2)*(h/2)=2/h := by field_simp; norm_num
    rw [he] at hm
    exact hu0.trans hm
  apply original_inverse_profile_at_finer_mesh C (normalizedCoefficient a b c0)
    delta (h*delta/64) K u (8/h^2) (64/h^2) hd (by positivity) hK hu
    (by positivity) (by positivity) ?_ ?_ hinj ?_ hprofile
  · have he : 2*(8/h^2)=16/h^2 := by ring
    rw [he]
    exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg h)
  · have he : (64/h^2)*(h*delta/64)=delta/h := by field_simp
    rw [he]
    apply (le_div_iff₀ hh).mpr
    have hm := mul_le_mul_of_nonneg_left hh1 hd.le
    simpa only [mul_one] using hm
  · intro c hc d hdC
    exact original_normalized_coefficient_inverse a b c0 c d h hh ha hb hc0
      (hC c hc) (hC d hdC) hab h0a h0b (hgap c hc) (hgap d hdC)

end OriginalNormalizedFractionalCoefficientProfile
