import Theorems.Thm_StickyKakeya4_native_middle_window_balance
import Theorems.Thm_StickyKakeya4_wz_carrier_pruning
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000
noncomputable section

namespace NativeRankOneSourceCutoff
open StickyKakeya4 NativeMiddleWindowBalance

/-- Choose the cutoff before the source and all returned retention and radix
parameters. The actual local transfer cost supplies the entire Q-squared
bound. In rank-one exclusion, use `s = a*kappa/2 - theta - nu` and choose
the fixed G from the finite menu before constructing the source. -/
theorem exists_source_cutoff {G s b : ℝ} (hG : 0 < G) (hgap : b < s) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        ∀ F Q : ℕ, 0 < F → ∀ eta : ℝ, 0 ≤ eta →
          (125 * 175616 * 16384 : ℝ) * (F : ℝ) * (Q : ℝ) ^ (2 : ℕ) *
            delta ^ (-eta) ≤ delta ^ (-b) →
          (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G * (Q : ℝ) ^ (2 : ℕ) *
            delta ^ s < 1 := by
  obtain ⟨delta0, hd0, hd01, hcut⟩ := exists_positive_rpow_absorption_threshold
    (show 0 < s - b by linarith)
    (show 0 ≤ (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G by positivity)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨delta0, hd0, hd01, ?_⟩
  intro delta hd hsmall F Q hF eta heta hcost
  have hradix : (Q : ℝ) ^ (2 : ℕ) ≤ delta ^ (-b) :=
    radix_sq_le_of_transfer_cost hd (hsmall.trans hd01) heta F Q hF hcost
  calc
    (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G * (Q : ℝ) ^ (2 : ℕ) * delta ^ s ≤
        (9261 * (6144 : ℝ) ^ (3 : ℕ)) * G * delta ^ (-b) * delta ^ s :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hradix (by positivity)) (Real.rpow_nonneg hd.le _)
    _ = ((9261 * (6144 : ℝ) ^ (3 : ℕ)) * G) *
        (delta ^ (-b) * delta ^ s) := by ring
    _ = ((9261 * (6144 : ℝ) ^ (3 : ℕ)) * G) * delta ^ (s - b) := by
      rw [← Real.rpow_add hd]
      congr 2
      ring
    _ ≤ 1 / 2 := hcut delta hd hsmall
    _ < 1 := by norm_num

end NativeRankOneSourceCutoff
