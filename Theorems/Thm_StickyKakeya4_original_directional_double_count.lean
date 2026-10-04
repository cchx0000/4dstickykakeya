import Theorems.Thm_StickyKakeya4_original_direction_pair_count
import Theorems.Thm_StickyKakeya4_original_common_fiber_projection
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Finset
open scoped BigOperators
noncomputable section
open Classical
namespace OriginalDirectionalDoubleCount
open OriginalCommonFiberProjection OriginalDirectionPairCount OriginalPhysicalPairTube
abbrev Point := ℝ × ℝ

def separatedAPairs (A : Finset Point) (s : ℝ) :=
  (A ×ˢ A).filter (fun aa => s ≤ ‖aa.1-aa.2‖)

/-- Reverse the count of the SAME original ordered A/B pair incidences. -/
lemma sum_projectedPairs_eq (A : Finset Point) (H : Finset (Point × Point)) (eta s : ℝ) :
    (∑ bb ∈ H, (projectedPairs A (bb.1-bb.2) eta s).card) =
      ∑ aa ∈ separatedAPairs A s, (directionPairs H (aa.1-aa.2) eta).card := by
  simp only [projectedPairs,directionPairs,separatedAPairs,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro aa _
  by_cases hsep : s ≤ ‖aa.1-aa.2‖ <;> simp [hsep]

/-- Actual pair tubes supply the upper incidence count. No direction set or
its Frostman property is assumed or selected independently of original B. -/
theorem projectedPairs_sum_upper (A B : Finset Point) (H : Finset (Point × Point))
    {eta s cap : ℝ} (heta : 0 < eta) (hs : 0 < s) (hcap0 : 0 ≤ cap)
    (hH : H ⊆ B ×ˢ B) (hdistinct : ∀ bb ∈ H, bb.1 ≠ bb.2)
    (hbox : ∀ b ∈ B, ‖b‖ ≤ 1)
    (hcap : ∀ bb ∈ H, ((physicalPairTube B (8*eta/s) bb).card : ℝ) ≤ cap*B.card) :
    (∑ bb ∈ H, ((projectedPairs A (bb.1-bb.2) eta s).card : ℝ)) ≤
      cap*(B.card : ℝ)^2*(A.card : ℝ)^2 := by
  have heq := congrArg (fun n : ℕ => (n : ℝ)) (sum_projectedPairs_eq A H eta s)
  simp only [Nat.cast_sum] at heq
  rw [heq]
  have hAcard : ((separatedAPairs A s).card : ℝ) ≤ (A.card : ℝ)^2 := by
    have hh := Finset.card_le_card (show separatedAPairs A s ⊆ A ×ˢ A from Finset.filter_subset _ _)
    simpa only [Finset.card_product,Nat.cast_mul,pow_two] using (Nat.cast_le.mpr hh :
      ((separatedAPairs A s).card : ℝ) ≤ ((A ×ˢ A).card : ℝ))
  calc
    _ ≤ ∑ _aa ∈ separatedAPairs A s, cap*(B.card : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro aa haa
      exact directionPairs_card B H (aa.1-aa.2) heta hs hcap0 (Finset.mem_filter.mp haa).2
        hH hdistinct hbox hcap
    _ = cap*(B.card : ℝ)^2*(separatedAPairs A s).card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hAcard (by positivity)

/-- The finite final comparison: dense original radial/common-C pairs and
their proved A-pair lower counts force population growth. The directional
upper estimate is derived from literal original-pair physical tube counts. -/
theorem original_pair_double_count_growth (A B : Finset Point) (C : Finset ℝ)
    (H : Finset (Point × Point)) {eta s cap q lam : ℝ}
    (heta : 0 < eta) (hs : 0 < s) (hcap0 : 0 ≤ cap) (hlam : 0 ≤ lam)
    (hA : A.Nonempty) (hB : B.Nonempty) (hH : H ⊆ B ×ˢ B)
    (hmass : q*(B.card : ℝ)^2 ≤ H.card)
    (hdistinct : ∀ bb ∈ H, bb.1 ≠ bb.2) (hbox : ∀ b ∈ B, ‖b‖ ≤ 1)
    (hcap : ∀ bb ∈ H, ((physicalPairTube B (8*eta/s) bb).card : ℝ) ≤ cap*B.card)
    (hcounts : ∀ bb ∈ H, lam*A.card*C.card ≤ (projectedPairs A (bb.1-bb.2) eta s).card) :
    q*lam*C.card ≤ cap*A.card := by
  have hAc : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hBc : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
  have hup := projectedPairs_sum_upper A B H heta hs hcap0 hH hdistinct hbox hcap
  have hlo : lam*A.card*C.card*H.card ≤
      ∑ bb ∈ H, ((projectedPairs A (bb.1-bb.2) eta s).card : ℝ) := by
    have hh := Finset.sum_le_sum hcounts
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh
  have hmass' := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ lam*(A.card : ℝ)*(C.card : ℝ) by positivity)
  have hcomp := hmass'.trans (hlo.trans hup)
  apply (mul_le_mul_iff_left₀ (show 0 < (B.card : ℝ)^2*A.card by positivity)).mp
  nlinarith only [hcomp]
end OriginalDirectionalDoubleCount
