import Theorems.Thm_StickyKakeya4_native_compact_ancestor_regularity

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace NativeConfiguredDyadicMatching

/-- A configured dyadic mesh above the actual first-parent rho gives the
correct six-level comparison, with every normalization constant retained. -/
lemma configured_depth_le (m u : ℕ)
    (hcfg : 64 / ((2 ^ m : ℕ) : ℝ) ≤ (2 : ℝ)⁻¹ ^ u) : u + 6 ≤ m := by
  have hm : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hu : (0 : ℝ) < (2 : ℝ) ^ u := by positivity
  have hh : (64 : ℝ) / (2 : ℝ) ^ m ≤ 1 / (2 : ℝ) ^ u := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, inv_pow, one_div] using hcfg
  have hp : (2 : ℝ) ^ (u + 6) ≤ (2 : ℝ) ^ m := by
    have hc := (div_le_div_iff₀ hm hu).mp hh
    rw [pow_add]
    norm_num only [show (2 : ℝ) ^ 6 = 64 by norm_num] at ⊢
    nlinarith only [hc]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp (by exact_mod_cast hp)

lemma configured_scale_product (u : ℕ) :
    ((2 ^ (u + 12) : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ u = 4096 := by
  push_cast
  rw [pow_add, inv_pow, show (2 : ℝ) ^ 12 = 4096 by norm_num]
  calc
    ((2 : ℝ) ^ u * 4096) * ((2 : ℝ) ^ u)⁻¹ =
        4096 * ((2 : ℝ) ^ u * ((2 : ℝ) ^ u)⁻¹) := by ring
    _ = 4096 := by rw [mul_inv_cancel₀ (by positivity), mul_one]

/-- Base grid, output tube radius, and the representative error all use
the same dyadic M, with the second 512 contraction explicit. -/
lemma configured_scale_identities (u : ℕ) :
    (2 : ℝ)⁻¹ ^ u / 512 = 8 / ((2 ^ (u + 12) : ℕ) : ℝ) ∧
    64 / ((2 ^ (u + 12) : ℕ) : ℝ) = (2 : ℝ)⁻¹ ^ u / 64 ∧
    1 / (32 * ((2 ^ (u + 12) : ℕ) : ℝ)) = (2 : ℝ)⁻¹ ^ u / 131072 := by
  have hM : (0 : ℝ) < ((2 ^ (u + 12) : ℕ) : ℝ) := by positivity
  have hp := configured_scale_product u
  refine ⟨?_, ?_, ?_⟩
  · apply (eq_div_iff hM.ne').mpr
    nlinarith only [hp]
  · apply (div_eq_iff hM.ne').mpr
    nlinarith only [hp]
  · apply (div_eq_iff (mul_ne_zero (by norm_num) hM.ne')).mpr
    nlinarith only [hp]

/-- The actual quarter-depth cap implies the relative-source scale guard.
The weaker phaseDepth bound is not used in its place. The last conclusion
matches the genuine rawPoint radius 3*rho to the fat-tube containment lemma. -/
theorem match_actual_scales {delta : ℝ} (level m u : ℕ)
    (hdy : delta = (2 : ℝ)⁻¹ ^ level) (hquarter : m ≤ level / 4)
    (hcfg : 64 / ((2 ^ m : ℕ) : ℝ) ≤ (2 : ℝ)⁻¹ ^ u) :
    u + 12 ≤ m + 6 ∧ u + 12 ≤ level - m + 6 ∧
    ((2 ^ (u + 12) : ℕ) : ℝ) * (((2 ^ m : ℕ) : ℝ) * delta / 64) ≤ 1 ∧
    (2 : ℝ)⁻¹ ^ u / 512 = 8 / ((2 ^ (u + 12) : ℕ) : ℝ) ∧
    64 / ((2 ^ (u + 12) : ℕ) : ℝ) = (2 : ℝ)⁻¹ ^ u / 64 ∧
    3 * (64 / ((2 ^ m : ℕ) : ℝ)) ≤ 12288 / ((2 ^ (u + 12) : ℕ) : ℝ) := by
  have hdepth := configured_depth_le m u hcfg
  have hb : u + 12 ≤ m + 6 := by omega
  have hlocal : u + 12 ≤ level - m + 6 := by omega
  have hd : 0 < delta := by rw [hdy]; positivity
  have hguard : ((2 ^ (u + 12) : ℕ) : ℝ) * (((2 ^ m : ℕ) : ℝ) * delta / 64) ≤ 1 := by
    have hp : ((2 ^ (u + 12) : ℕ) : ℝ) ≤ ((2 ^ (m + 6) : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hb
    have hfine := NativeCompactAncestorRegularity.dyadic_parent_scale hdy ⟨2 * m, by omega⟩
    calc
      _ ≤ ((2 ^ (m + 6) : ℕ) : ℝ) * (((2 ^ m : ℕ) : ℝ) * delta / 64) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = ((2 ^ (2 * m) : ℕ) : ℝ) * delta := by
        push_cast
        rw [show 2 * m = m + m by omega]
        rw [pow_add, pow_add, show (2 : ℝ) ^ 6 = 64 by norm_num]
        ring
      _ ≤ 1 := hfine
  have hM : (0 : ℝ) < ((2 ^ (u + 12) : ℕ) : ℝ) := by positivity
  have hprod := configured_scale_product u
  have ht : 3 * (64 / ((2 ^ m : ℕ) : ℝ)) ≤ 12288 / ((2 ^ (u + 12) : ℕ) : ℝ) := by
    calc
      _ ≤ 3 * (2 : ℝ)⁻¹ ^ u := mul_le_mul_of_nonneg_left hcfg (by norm_num)
      _ = _ := by
        apply (eq_div_iff hM.ne').mpr
        nlinarith only [hprod]
  exact ⟨hb, hlocal, hguard, (configured_scale_identities u).1,
    (configured_scale_identities u).2.1, ht⟩

end NativeConfiguredDyadicMatching
