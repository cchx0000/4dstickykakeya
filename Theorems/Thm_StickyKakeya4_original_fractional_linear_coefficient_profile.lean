import Theorems.Thm_StickyKakeya4_gkz_original_gap_energy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
namespace OriginalFractionalLinearCoefficientProfile
open Classical GKZOriginalGapEnergy

def coefficient (a b c : ℝ) : ℝ := (c-a)/(b-c)

lemma original_coefficient_difference_identity (a b c d : ℝ)
    (hc : b-c≠0) (hd : b-d≠0) :
    (b-c)*(b-d)*(coefficient a b c-coefficient a b d)=(b-a)*(c-d) := by
  unfold coefficient
  field_simp
  ring

lemma original_coefficient_bound (a b c h : ℝ) (hh : 0 < h)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hgap : h ≤ |b-c|) :
    |coefficient a b c| ≤ 2/h := by
  have hb : 0 < |b-c| := hh.trans_le hgap
  rw [coefficient,abs_div]
  apply (div_le_div_iff₀ hb hh).mpr
  have hn := abs_sub c a
  have hm := mul_le_mul_of_nonneg_right (show |c-a| ≤ 2 by linarith only [hn,ha,hc]) hh.le
  nlinarith only [hm,hgap]

/-- The inverse bound concerns actual original slope labels, so no
coefficient separation or replacement measure is needed. -/
theorem original_coefficient_inverse_bound (a b c d h : ℝ) (hh : 0 < h)
    (hb : |b| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ 1)
    (hab : h ≤ |a-b|) (hbc : b-c≠0) (hbd : b-d≠0) :
    |c-d| ≤ (4/h)*|coefficient a b c-coefficient a b d| := by
  have hid := congrArg abs (original_coefficient_difference_identity a b c d hbc hbd)
  simp only [abs_mul,abs_sub_comm b a] at hid
  have hbc2 : |b-c| ≤ 2 := (abs_sub b c).trans (by linarith only [hb,hc])
  have hbd2 : |b-d| ≤ 2 := (abs_sub b d).trans (by linarith only [hb,hd])
  have hprod := mul_le_mul hbc2 hbd2 (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  have hup := mul_le_mul_of_nonneg_right hprod (abs_nonneg (coefficient a b c-coefficient a b d))
  have hlo := mul_le_mul_of_nonneg_right hab (abs_nonneg (c-d))
  have hhbound : h*|c-d| ≤ 4*|coefficient a b c-coefficient a b d| := by
    nlinarith only [hid,hup,hlo]
  calc
    |c-d| ≤ (4*|coefficient a b c-coefficient a b d|)/h := by
      apply (le_div_iff₀ hh).mpr
      nlinarith only [hhbound]
    _ = (4/h)*|coefficient a b c-coefficient a b d| := by ring

theorem original_coefficient_injective (C : Finset ℝ) (a b h : ℝ) (hh : 0 < h)
    (hb : |b| ≤ 1) (hab : h ≤ |a-b|)
    (hC : ∀ c∈C,|c| ≤ 1) (hgap : ∀ c∈C,h ≤ |b-c|) :
    Set.InjOn (coefficient a b) C := by
  intro c hc d hd he
  have hbc : b-c≠0 := abs_pos.mp (hh.trans_le (hgap c hc))
  have hbd : b-d≠0 := abs_pos.mp (hh.trans_le (hgap d hd))
  have hz := original_coefficient_inverse_bound a b c d h hh hb (hC c hc) (hC d hd) hab hbc hbd
  rw [he,sub_self,abs_zero,mul_zero] at hz
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

/-- The literal image of the retained original slope source has a full
weak profile at delta/4. Arbitrary coefficient intervals are charged in an
original interval with radius8R/h, including radii larger than one. -/
theorem original_coefficient_image_profile (C : Finset ℝ) (a b h delta K u : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hd : 0 < delta) (hK : 1 ≤ K) (hu : 0 ≤ u)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : h ≤ |a-b|)
    (hC : ∀ c∈C,|c| ≤ 1) (hgap : ∀ c∈C,h ≤ |b-c|)
    (hprofile : ScalarFrostman C delta K u) :
    (C.image (coefficient a b)).card=C.card ∧
    (∀ x∈C.image (coefficient a b),|x| ≤ 2/h) ∧
    ScalarFrostman (C.image (coefficient a b)) (delta/4) (K*(8/h)^u) u := by
  have hinj := original_coefficient_injective C a b h hh hb hab hC hgap
  have hcard := Finset.card_image_of_injOn hinj
  refine ⟨hcard,?_,?_⟩
  · intro x hx
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hx
    exact original_coefficient_bound a b c h hh ha (hC c hc) (hgap c hc)
  intro z r hr _hr1
  let E := C.filter (fun c => |coefficient a b c-z| ≤ r)
  have heq : (C.image (coefficient a b)).filter (fun x => |x-z| ≤ r)=E.image (coefficient a b) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxC,hxr⟩ := Finset.mem_filter.mp hx
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hxC
      exact Finset.mem_image.mpr ⟨c,Finset.mem_filter.mpr ⟨hc,hxr⟩,rfl⟩
    · intro hx
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩
  rw [heq,Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)),hcard]
  have hr0 : 0 ≤ r := by linarith only [hr,hd]
  let T := 8*r/h
  have hT : delta ≤ T := by
    apply (le_div_iff₀ hh).mpr
    have hm := mul_le_mul_of_nonneg_left hh1 hd.le
    nlinarith only [hm,hr,hd]
  have hpow : T^u=(8/h)^u*r^u := by
    rw [show T=(8/h)*r by dsimp [T]; ring]
    exact Real.mul_rpow (by positivity) hr0
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  change (E.card : ℝ) ≤ K*(8/h)^u*r^u*C.card
  by_cases hE : E.Nonempty
  · obtain ⟨c0,hc0⟩ := hE
    have hc0C := (Finset.mem_filter.mp hc0).1
    have hc0z := (Finset.mem_filter.mp hc0).2
    have hsub : E⊆C.filter (fun c => |c-c0| ≤ T) := by
      intro c hc
      obtain ⟨hcC,hcz⟩ := Finset.mem_filter.mp hc
      refine Finset.mem_filter.mpr ⟨hcC,?_⟩
      have hbc : b-c≠0 := abs_pos.mp (hh.trans_le (hgap c hcC))
      have hb0 : b-c0≠0 := abs_pos.mp (hh.trans_le (hgap c0 hc0C))
      have hdiff : |coefficient a b c-coefficient a b c0| ≤ 2*r := by
        have hx := abs_sub (coefficient a b c-z) (coefficient a b c0-z)
        rw [show (coefficient a b c-z)-(coefficient a b c0-z)=coefficient a b c-coefficient a b c0 by ring] at hx
        linarith only [hx,hcz,hc0z]
      have hi := original_coefficient_inverse_bound a b c c0 h hh hb (hC c hcC) (hC c0 hc0C) hab hbc hb0
      exact hi.trans ((mul_le_mul_of_nonneg_left hdiff (by positivity)).trans_eq (by dsimp [T]; ring))
    by_cases hT1 : T ≤ 1
    · have hn := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hprofile c0 T hT hT1)
      rw [hpow] at hn
      simpa only [mul_assoc] using hn
    · have hpow1 : 1 ≤ T^u := Real.one_le_rpow (le_of_not_ge hT1) hu
      have hcoef : 1 ≤ K*T^u := by nlinarith only [hK,hpow1]
      have hcount : (E.card : ℝ) ≤ C.card :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      have hm := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg C.card)
      rw [one_mul,hpow] at hm
      exact hcount.trans (by simpa only [mul_assoc] using hm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hE,Finset.card_empty,Nat.cast_zero]
    positivity

end OriginalFractionalLinearCoefficientProfile
