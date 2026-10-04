import Theorems.Thm_StickyKakeya4_original_separated_packing
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
open Classical
namespace OriginalScalarAffinePacking
open OriginalSeparatedPacking

/-- Count actual separated scalar preimages of a short affine interval.
The lower slope bound comes from the actual original B secant. -/
theorem scalar_affine_card (C : Finset ℝ) {delta eta d u z : ℝ}
    (hdelta : 0 < delta) (heta : 0 ≤ eta) (hd : 0 < d) (hu : d ≤ |u|)
    (hsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → delta ≤ |c-c'|) :
    ((C.filter (fun c => |u*c-z| ≤ eta)).card : ℝ) ≤ 2*((eta/d)/delta)+2 := by
  have hu0 : u ≠ 0 := abs_pos.mp (hd.trans_le hu)
  have hsub : C.filter (fun c => |u*c-z| ≤ eta) ⊆
      C.filter (fun c => |c-z/u| ≤ eta/d) := by
    intro c hc
    obtain ⟨hcC,hc⟩ := Finset.mem_filter.mp hc
    have hid : u*(c-z/u)=u*c-z := by field_simp
    have he : |u| *|c-z/u| ≤ eta := by simpa only [← hid,abs_mul] using hc
    have hm := mul_le_mul_of_nonneg_right hu (abs_nonneg (c-z/u))
    refine Finset.mem_filter.mpr ⟨hcC,?_⟩
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hm,he]
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (scalar_ball_card C hdelta (show 0 ≤ eta/d by positivity) hsep (z/u))

/-- Original scalar separation controls every fiber of a planar affine
line map; the bound is independent of the original population of C. -/
theorem planar_affine_card (C : Finset ℝ) (v z : ℝ × ℝ) {delta eta d : ℝ}
    (hdelta : 0 < delta) (heta : 0 ≤ eta) (hd : 0 < d) (hv : d ≤ ‖v‖)
    (hsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → delta ≤ |c-c'|) :
    ((C.filter (fun c => ‖c • v-z‖ ≤ eta)).card : ℝ) ≤ 2*((eta/d)/delta)+2 := by
  have hv' : d ≤ max |v.1| |v.2| := by simpa only [Prod.norm_def,Real.norm_eq_abs] using hv
  rcases le_max_iff.mp hv' with hv1|hv2
  · have hsub : C.filter (fun c => ‖c • v-z‖ ≤ eta) ⊆
        C.filter (fun c => |v.1*c-z.1| ≤ eta) := by
      intro c hc
      obtain ⟨hcC,hc⟩ := Finset.mem_filter.mp hc
      have hh : |c*v.1-z.1| ≤ eta ∧ |c*v.2-z.2| ≤ eta := by
        simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
          smul_eq_mul,Real.norm_eq_abs,max_le_iff] using hc
      exact Finset.mem_filter.mpr ⟨hcC,by simpa only [mul_comm] using hh.1⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (scalar_affine_card C hdelta heta hd hv1 hsep)
  · have hsub : C.filter (fun c => ‖c • v-z‖ ≤ eta) ⊆
        C.filter (fun c => |v.2*c-z.2| ≤ eta) := by
      intro c hc
      obtain ⟨hcC,hc⟩ := Finset.mem_filter.mp hc
      have hh : |c*v.1-z.1| ≤ eta ∧ |c*v.2-z.2| ≤ eta := by
        simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,
          smul_eq_mul,Real.norm_eq_abs,max_le_iff] using hc
      exact Finset.mem_filter.mpr ⟨hcC,by simpa only [mul_comm] using hh.2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (scalar_affine_card C hdelta heta hd hv2 hsep)
end OriginalScalarAffinePacking
