import Theorems.Thm_StickyKakeya4_gkz_original_anchor_cover
import Theorems.Thm_StickyKakeya4_gkz_original_gap_energy
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZOriginalAnchorProfile
open ActualRoundedAdditiveEnergy GKZOriginalGapEnergy GKZOriginalAnchorCover

lemma original_profile_constant_ge_one (A : Finset ℝ) {delta K sigma : ℝ}
    (hA : A.Nonempty) (hd : delta ≤ 1) (hbox : ∀ a∈A, 1 ≤ a ∧ a ≤ 2)
    (hprofile : ScalarFrostman A delta K sigma) : 1 ≤ K := by
  have heq : A.filter (fun a => |a-1| ≤ 1)=A := by
    apply Finset.filter_eq_self.mpr
    intro a ha
    obtain ⟨hlo,hhi⟩ := hbox a ha
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hp := hprofile 1 1 hd le_rfl
  rw [heq, Real.one_rpow, mul_one] at hp
  have hN : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  nlinarith

/-- Extend the original profile beyond unit radius using only its total
original mass, sigma ≥ 0, and the derived normalization K ≥ 1. -/
lemma original_profile_extended (A : Finset ℝ) {delta K sigma : ℝ}
    (hK : 1 ≤ K) (hsigma : 0 ≤ sigma)
    (hprofile : ScalarFrostman A delta K sigma) (z r : ℝ) (hr : delta ≤ r) :
    ((A.filter (fun a => |a-z| ≤ r)).card : ℝ) ≤ K*r^sigma*A.card := by
  by_cases hr1 : r ≤ 1
  · exact hprofile z r hr hr1
  have hrlo : 1 ≤ r := (lt_of_not_ge hr1).le
  have hp : 1 ≤ r^sigma := Real.one_le_rpow hrlo hsigma
  have hfactor : 1 ≤ K*r^sigma := by
    simpa only [one_mul] using mul_le_mul hK hp
      (show (0:ℝ) ≤ 1 by norm_num) (le_trans (by norm_num) hK)
  have hc : ((A.filter (fun a => |a-z| ≤ r)).card : ℝ) ≤ A.card :=
    Nat.cast_le.mpr (Finset.card_filter_le _ _)
  exact hc.trans (by nlinarith [mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg A.card)])

/-- Recover the denominator-scale factor from every original anchor point,
with its original Frostman law and complete mesh error. -/
theorem original_denominator_cover_recovery (A S : Finset ℝ)
    {delta b c e2 K sigma : ℝ}
    (hA : A.Nonempty) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hb : 1 ≤ b) (hsigma : 0 ≤ sigma) (he2 : 2*delta ≤ |e2|)
    (hbox : ∀ a∈A, 1 ≤ a ∧ a ≤ 2)
    (hS : ∀ x∈S, |x-c| ≤ 2*|e2|)
    (hprofile : ScalarFrostman A delta K sigma) :
    ((S.image (rounded delta)).card : ℝ) ≤
      4*(3:ℝ)^sigma*K*|e2|^sigma*
        ((A.product S).image (fun p => rounded delta (b*p.1+p.2))).card := by
  have hK := original_profile_constant_ge_one A hA hd1 hbox hprofile
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hepos : 0 < |e2| := (by positivity : 0 < 2*delta).trans_le he2
  have hball : ∀ z : ℝ, ((A.filter (fun a => |a-z| ≤ 2*|e2|+delta)).card : ℝ) ≤
      K*(3*|e2|)^sigma*A.card := by
    intro z
    have hsub : A.filter (fun a => |a-z| ≤ 2*|e2|+delta) ⊆
        A.filter (fun a => |a-z| ≤ 3*|e2|) := by
      intro a ha
      obtain ⟨ha, hnear⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨ha, by linarith⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (original_profile_extended A hK hsigma hprofile z (3*|e2|) (by linarith))
  have hc := original_anchor_cover_recovery A S hd hb
    (show 0 ≤ K*(3*|e2|)^sigma*(A.card : ℝ) by positivity) hS hball
  have hpow : (3*|e2|)^sigma=(3:ℝ)^sigma*|e2|^sigma :=
    Real.mul_rpow (by norm_num) (abs_nonneg e2)
  rw [hpow] at hc
  have hN : 0 < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  apply (mul_le_mul_iff_left₀ hN).mp
  nlinarith only [hc]

/-- Unit-interval ratio information gives the required short target interval
for the actual original linear sum, including both coefficient signs. -/
theorem original_linear_sum_radius (A1 : Finset ℝ) {e1 e2 : ℝ}
    (hA1 : A1.Nonempty) (hbox : ∀ a∈A1, 1 ≤ a ∧ a ≤ 2)
    (hcoeff : |e1| ≤ |e2|) :
    ∃ c : ℝ, ∀ x∈(A1.product A1).image (fun p => e2*p.1+e1*p.2),
      |x-c| ≤ 2*|e2| := by
  obtain ⟨a0, ha0⟩ := hA1
  refine ⟨e2*a0+e1*a0, ?_⟩
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
  have hb0 := hbox a0 ha0
  have hb1 := hbox p.1 hp1
  have hb2 := hbox p.2 hp2
  have hd1 : |p.1-a0| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hd2 : |p.2-a0| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hid : e2*p.1+e1*p.2-(e2*a0+e1*a0)=e2*(p.1-a0)+e1*(p.2-a0) := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul]
  have hm1 := mul_le_mul_of_nonneg_left hd1 (abs_nonneg e2)
  have hm2 := mul_le_mul_of_nonneg_left hd2 (abs_nonneg e1)
  nlinarith

end GKZOriginalAnchorProfile
