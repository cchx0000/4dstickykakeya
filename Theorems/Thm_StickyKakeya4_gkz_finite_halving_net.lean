import Theorems.Thm_StickyKakeya4_original_separated_packing

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
open Classical

namespace GKZFiniteHalvingNet

/-- Clipping to the original endpoints keeps the approximating point in the
original finite carrier and cannot increase distance from the unit interval. -/
lemma original_unit_interval_approximation (B : Finset ℝ)
    (hzero : 0 ∈ B) (hone : 1 ∈ B) {x b : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (hb : b ∈ B) :
    ∃ b' ∈ B, 0 ≤ b' ∧ b' ≤ 1 ∧ |x-b'| ≤ |x-b| := by
  by_cases hb0 : b < 0
  · refine ⟨0, hzero, le_rfl, by norm_num, ?_⟩
    rw [sub_zero, abs_of_nonneg hx.1, abs_of_nonneg (by linarith : 0 ≤ x-b)]
    linarith
  by_cases hb1 : 1 < b
  · refine ⟨1, hone, by norm_num, le_rfl, ?_⟩
    rw [abs_of_nonpos (by linarith : x-1 ≤ 0),
      abs_of_nonpos (by linarith : x-b ≤ 0)]
    linarith
  exact ⟨b, hb, le_of_not_gt hb0, le_of_not_gt hb1, le_rfl⟩

def gridPoint (n k : ℕ) : ℝ := (k : ℝ)/(2:ℝ)^n

lemma gridPoint_left (n k : ℕ) : gridPoint (n+1) k = gridPoint n k / 2 := by
  unfold gridPoint
  rw [pow_succ, div_mul_eq_div_div]

lemma gridPoint_right (n k : ℕ) :
    gridPoint (n+1) (k+2^n) = (gridPoint n k+1)/2 := by
  unfold gridPoint
  push_cast
  rw [pow_succ]
  field_simp

/-- Approximate closure under the two binary contractions supplies witnesses
for every dyadic grid point in the original carrier. -/
theorem original_dyadic_net (S : Finset ℝ) {s : ℝ} (hs : 0 ≤ s)
    (hzero : 0 ∈ S)
    (hleft : ∀ b ∈ S, ∃ b' ∈ S, |b/2-b'| ≤ s)
    (hright : ∀ b ∈ S, ∃ b' ∈ S, |(b+1)/2-b'| ≤ s) :
    ∀ n k : ℕ, k < 2^n → ∃ b ∈ S, |gridPoint n k-b| ≤ 2*s := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst k
      exact ⟨0, hzero, by simpa [gridPoint] using (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hs)⟩
  | succ n ih =>
      intro k hk
      by_cases hlow : k < 2^n
      · obtain ⟨b, hb, hclose⟩ := ih k hlow
        obtain ⟨b', hb', hchild⟩ := hleft b hb
        refine ⟨b', hb', ?_⟩
        rw [gridPoint_left]
        have hhalf : |gridPoint n k / 2-b/2| ≤ s := by
          rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          linarith
        exact (abs_sub_le (gridPoint n k / 2) (b/2) b').trans (by linarith)
      · have hpow : 2^(n+1) = 2^n+2^n := by omega
        have hk' : k-2^n < 2^n := by omega
        obtain ⟨b, hb, hclose⟩ := ih (k-2^n) hk'
        obtain ⟨b', hb', hchild⟩ := hright b hb
        refine ⟨b', hb', ?_⟩
        have heq : k = (k-2^n)+2^n := by omega
        rw [heq, gridPoint_right]
        have hhalf : |(gridPoint n (k-2^n)+1)/2-(b+1)/2| ≤ s := by
          have hid : (gridPoint n (k-2^n)+1)/2-(b+1)/2 =
              (gridPoint n (k-2^n)-b)/2 := by ring
          rw [hid, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          linarith
        exact (abs_sub_le ((gridPoint n (k-2^n)+1)/2) ((b+1)/2) b').trans
          (by linarith)

end GKZFiniteHalvingNet
